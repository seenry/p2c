#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "frontends/common/constantFolding.h"
#include "frontends/common/options.h"
#include "frontends/common/parseInput.h"
#include "frontends/common/parser_options.h"
#include "frontends/common/resolveReferences/referenceMap.h"
#include "frontends/p4/frontend.h"
#include "frontends/p4/toP4/toP4.h"
#include "frontends/p4/typeChecking/typeChecker.h"
#include "frontends/p4/typeMap.h"
#include "ir/ir.h"
#include "ir/pass_manager.h"
#include "ir/visitor.h"
#include "lib/compile_context.h"
#include "lib/cstring.h"
#include "lib/error.h"
#include "options.h"
#include "rocq_helpers.h"
#include "test/gtest/helpers.h"

namespace P4::Rocq {

// The reference and type maps are owned by [main] and shared with the visitor:
// resolving a field's width needs the same [TypeMap] the type checker filled
// in.  A P4 header field is declared with a named type as often as not
// (`typedef bit<48> macAddr_t; ... macAddr_t dstAddr;`), and the frontend
// records the resolution in the map rather than rewriting the AST, so a
// backend that reads `field->type` directly sees a [Type_Name] and no width.
class MidEnd : public PassManager {
 public:
    MidEnd(P4::ReferenceMap *refMap, P4::TypeMap *typeMap) {
        addPasses({
            new P4::TypeChecking(refMap, typeMap, true),
            new P4::ConstantFolding(typeMap),
        });
    }
};

// One IR [Header] per P4 header-INSTANCE field, and per metadata field.
struct FieldInfo {
    std::string qualified;  // "ipv4.protocol" -- the instance, not the type
    int uid = 0;            // HeaderCtr id, 1-based
    int width = 0;          // bits on the wire
    bool onWire = true;     // false for metadata: never extracted or emitted,
                            // and so not part of the input packet's length
};

// =====================================================================
// Predication.
//
// A P4 control is structured and acyclic: no gotos, no loops.  So the
// condition under which any statement runs is a static predicate over header
// fields at that point, and a statement can be lowered by REPLICATING that
// predicate into the rule that carries it -- there is no need for a program
// counter, and no join points to name.
//
// A [Guard] is a conjunction of clauses that must hold ([pos], flattened into
// one clause since a conjunction of conjunctions is a conjunction) and clauses
// that must NOT hold ([neg], each from an else-branch or a `!`).  It cannot be
// collapsed to a single clause because a [MatchPattern] has no negation: it is
// a conjunction of (header, op, value) triples and nothing else.
//
// What supplies the negation is RULE ORDER.  Only the first matching rule of a
// transformer fires, so a guard `P and not N1 and not N2` becomes
//
//     [ (N1, nop); (N2, nop); (P, ops); (true, nop) ]
//
// -- if any Ni holds the run stops at a no-op, and otherwise P decides.  The
// trailing empty rule is what "the guard did not hold" looks like.
struct Guard {
    std::vector<std::string> pos;               // atoms, all of which must hold
    std::vector<std::vector<std::string>> neg;  // clauses, none of which may
};

// A run of statements sharing one guard, and the ops that compute whatever
// temporaries the guard itself reads.  [setup] is UNGUARDED and has to run
// before the guard is evaluated, so it becomes a module of its own in front.
// One arm of a match-action unit: extra atoms beyond the enclosing guard, and
// what to do when they hold.  A plain statement has a single arm with no extra
// atoms; a TABLE has one per entry, tried in the order they appear, which is
// exactly what a first-match rule list gives.
struct Alt {
    std::vector<std::string> atoms;
    std::vector<std::string> ops;
    int priority = 0;  // more specific first; see [prefixBitsOf]
};

struct Group {
    Guard guard;
    std::vector<std::string> setup;
    std::vector<Alt> alts;
};

// Two guards are the same guard if they read the same, which is a string
// comparison because every atom is already rendered.  Used to merge adjacent
// statements into one module rather than one module each.
static bool sameGuard(const Guard &a, const Guard &b) {
    return a.pos == b.pos && a.neg == b.neg;
}

static bool guardIsTrue(const Guard &g) { return g.pos.empty() && g.neg.empty(); }

static void mergeGuard(Guard &into, const Guard &g) {
    into.pos.insert(into.pos.end(), g.pos.begin(), g.pos.end());
    into.neg.insert(into.neg.end(), g.neg.begin(), g.neg.end());
}

// The negation of a guard, when it has one in this form.  A guard is
// `P and not N1 and not N2 ...`; negating it gives `not P or N1 or N2`, a
// DISJUNCTION, which is a conjunction again only in the two cases below.
// Anything else would need the group duplicated once per disjunct, which is
// not worth doing until a target needs it.
static bool negateGuard(const Guard &in, Guard &out) {
    if (in.neg.empty() && !in.pos.empty()) {  // not (a and b)  ->  one neg clause
        out.neg.push_back(in.pos);
        return true;
    }
    if (in.pos.empty() && in.neg.size() == 1) {  // not (not C)  ->  C
        out.pos = in.neg[0];
        return true;
    }
    return false;
}

// v1model drops a packet by setting the egress port to a reserved value
// rather than by any distinguished action, and so does this backend.
static const unsigned long long V1MODEL_DROP_PORT = 511;

class CoqVisitor : public Inspector {
    P4::TypeMap *typeMap;  // shared with the MidEnd; see the comment there
    std::ostringstream coqOutput;
    std::vector<std::string> actions;
    std::vector<std::string> tables;
    int header_uid = 1;  // For generating unique HeaderCtr IDs

    // One entry per P4 action: the HdrOp sexps its body lowered to, in order.
    // Held rather than streamed, because a transformer module is assembled in
    // [finalize] and an action's ops are its raw material.
    std::map<std::string, std::vector<std::string>> actionOps;

    // Intermediates.  See [newTemp]: an expression tree flattens into HdrOps
    // over Headers, so every subexpression that is not already a variable or a
    // literal needs one to land in.
    int nextTemp = 0;

    // An action's parameters and locals, by source name, valid only while that
    // action is being lowered.  They are Headers like everything else -- the
    // IR has no other place to put a value.
    std::map<std::string, FieldInfo> localHeaders;

    // The pipeline controls, in declaration order, and the ops they assemble
    // to.  Collected during traversal and lowered in [finalize], because a
    // control's actions are its children and are not lowered until after it.
    std::vector<const IR::P4Control *> pipelineControls;

    // Header validity, derived from the parser.
    //
    // The IR has no validity bit, so `isValid()` cannot be read off the state.
    // It does not need to be: a header is valid exactly when the parser
    // reached the state that extracts it, and when the parser is a TREE that
    // is the conjunction of the select tests along the one path to that state
    // -- every one of them over a field parsed earlier, so every one of them
    // expressible as a MatchPattern atom.
    //
    // When the parser is NOT a tree -- a state reachable two ways, a loop, a
    // select this backend cannot read -- a header is valid for more than one
    // reason, which is a disjunction, and no guard here can say it.  Validity
    // is then refused rather than guessed.
    std::map<std::string, Guard> validityOf;
    bool parserIsTree = true;

    // An entry, in the one form both sources reduce to.  `const entries` in
    // the P4 source and a line of --table-entries say the same thing, so they
    // are read into this and lowered once.
    struct RawKey {
        bool wildcard = false;
        bool masked = false;
        unsigned long long value = 0;
        unsigned long long mask = 0;
        // An lpm prefix written `v/n`.  The mask it denotes depends on the
        // key's WIDTH, which a --table-entries file does not know, so it is
        // resolved against the table when the entry is lowered.
        int prefixLen = -1;
    };
    struct RawEntry {
        std::vector<RawKey> keys;
        std::string action;
        std::vector<unsigned long long> args;
    };

    // Tables by name, and the parameter Headers of each action, both needed
    // where a table is APPLIED rather than where it is declared.
    std::map<std::string, const IR::P4Table *> tablesByName;
    std::map<std::string, std::vector<FieldInfo>> actionParams;

    // Entries read from --table-entries, by table name.  Same representation
    // `const entries` reduces to, so both lower through one path.
    std::map<std::string, std::vector<RawEntry>> suppliedEntries;

    // Header TYPE declarations, by name, collected before the struct that
    // instantiates them (p4c visits declarations in program order).
    std::map<cstring, const IR::Type_Header *> headerDecls;

    // The allocated fields, and a lookup keyed on the QUALIFIED name.  These
    // are PACKET fields only: one per header-instance field, and nothing else.
    // [inputLenBits] and [fieldsOfInstance] both walk this list, so a Header
    // that is not part of a header instance must not be in it.
    std::vector<FieldInfo> fields;
    std::map<std::string, FieldInfo> fieldByQualified;

    // Headers that hold intermediates, action parameters and locals.  They
    // share the Header namespace with [fields] -- an Operand can name nothing
    // else -- but they are never extracted or emitted, so they are kept apart.
    std::vector<FieldInfo> temps;

    // Ingress parser and deparser, populated by their preorder visitors.
    int nextParserLabel = 1;
    std::map<std::string, int> stateLabel;      // P4 state name -> entry label
    std::vector<std::string> parserStates;      // emitted ParserStateDef sexps
    std::vector<std::string> deparserEmits;     // emitted EmitOpConstructor sexps

 public:
    explicit CoqVisitor(P4::TypeMap *typeMap) : typeMap(typeMap) {}
    ~CoqVisitor() {}

    // Resolve a struct field's type to the header type it names, whether it is
    // still a Type_Name or has already been resolved.
    cstring headerTypeNameOf(const IR::Type *type) {
        if (auto tn = type->to<IR::Type_Name>()) return tn->path->name;
        if (auto th = type->to<IR::Type_Header>()) return th->name;
        return cstring::empty;
    }

    // The canonical form of a type node: what it denotes once named types are
    // resolved.  [TypeMap::getTypeType] is the frontend's own answer to this
    // question and is what keeps [Type_Typedef] and [Type_Newtype] from having
    // to be unwrapped by hand here.  Returns [type] unchanged when the map has
    // no entry, which is the right fallback -- a type already in canonical
    // form is its own canonical form.
    const IR::Type *canonicalTypeOf(const IR::Type *type) {
        if (type == nullptr) return nullptr;
        if (type->is<IR::Type_Bits>()) return type;
        if (typeMap != nullptr) {
            if (auto canon = typeMap->getTypeType(type, false)) return canon;
        }
        return type;
    }

    // Bit width of a field's type, through any named type it was declared
    // with.  Zero means "no width", which every caller treats as an error.
    int widthOf(const IR::Type *type) {
        auto canon = canonicalTypeOf(type);
        if (canon == nullptr) return 0;
        if (auto bits = canon->to<IR::Type_Bits>()) return bits->size;
        return 0;
    }

    // The header type a struct field instantiates, in canonical form -- so its
    // own fields carry resolved widths.  Falls back to the declaration
    // collected during traversal when the type map cannot answer.
    const IR::Type_Header *headerTypeOf(const IR::Type *instType) {
        if (auto th = canonicalTypeOf(instType)->to<IR::Type_Header>()) return th;
        cstring name = headerTypeNameOf(instType);
        if (name.isNullOrEmpty()) return nullptr;
        auto decl = headerDecls.find(name);
        return decl == headerDecls.end() ? nullptr : decl->second;
    }

    // The narrowest CrIntType that holds [width] bits.  Extraction widths are
    // arbitrary nats -- only the CONTAINER has to be one of W8/W16/W32/W64 --
    // so a bit<13> field is width 13 stored as W16.
    std::string containerFor(int width) {
        if (width <= 8) return "W8";
        if (width <= 16) return "W16";
        if (width <= 32) return "W32";
        if (width <= 64) return "W64";
        error("field of %1% bits does not fit any CrIntType", width);
        return "W64";
    }

    const FieldInfo *lookupField(const std::string &qualified) const {
        auto it = fieldByQualified.find(qualified);
        return it == fieldByQualified.end() ? nullptr : &it->second;
    }

void generateCoqListSexp(const std::vector<std::string> &elements) {
    // Edge case: If the list is empty, just output Coq_nil.
    if (elements.empty()) {
        coqOutput << "Coq_nil";
        return;
    }

    // (Coq_cons E1 (Coq_cons E2 ... (Coq_cons EN Coq_nil)...))

    // The logic:
    // 1. Print N times: (Coq_cons <Element>
    // 2. Print: Coq_nil
    // 3. Print N times: )

    for (const std::string &element : elements) {
        coqOutput << "(Coq_cons " << element << " ";
    }

    coqOutput << "Coq_nil";

    for (size_t i = 0; i < elements.size(); ++i) {
        coqOutput << ")";
    }
}

// Header TYPE declarations are only recorded here.  UIDs are allocated per
// INSTANCE below: a type may be instantiated more than once (sai.p4 declares
// both `ipv4_t ipv4` and `ipv4_t inner_ipv4`), and keying on the field name
// alone would give hdr.ipv4.protocol and hdr.inner_ipv4.protocol the same
// Header -- silently merging two distinct headers.
bool preorder(const IR::Type_Header *header) override {
    headerDecls[header->name] = header;
    return true;
}

// The struct that instantiates the header types -- `struct headers` in sai.p4.
// One IR Header per instance field, keyed on "<instance>.<field>".  A struct
// with no header-typed fields (`struct metadata`) contributes nothing.
bool preorder(const IR::Type_Struct *st) override {
    // A struct of plain bit<N> fields is metadata -- `struct metadata`, or
    // v1model's `standard_metadata_t`.  Those are variables like any other and
    // need Headers, but they are NOT on the wire: nothing extracts or emits
    // them, and counting them in the packet length would be wrong.  Fields
    // with no bit width (an `error`, an enum) are skipped rather than
    // reported: v1model's intrinsic metadata has several, and none of them is
    // something this backend can represent or a program is likely to want.
    bool anyHeaderFields = false;
    for (auto inst : st->fields) {
        if (headerTypeOf(inst->type) != nullptr) anyHeaderFields = true;
    }
    if (!anyHeaderFields) {
        for (auto f : st->fields) {
            int width = widthOf(f->type);
            if (width <= 0 || width > 64) continue;
            std::string qualified =
                std::string(st->name.name.c_str()) + "." + std::string(f->name.name.c_str());
            if (fieldByQualified.count(qualified)) continue;
            FieldInfo fi{qualified, header_uid++, width, false};
            fields.push_back(fi);
            fieldByQualified[fi.qualified] = fi;
        }
        return true;
    }

    for (auto inst : st->fields) {
        const IR::Type_Header *hdrType = headerTypeOf(inst->type);
        if (hdrType == nullptr) continue;

        for (auto field : hdrType->fields) {
            std::string qualified = std::string(inst->name.name.c_str()) + "." +
                                    std::string(field->name.name.c_str());
            int width = widthOf(field->type);
            if (width == 0) {
                error("field %1% has no bit width; only bit<N> is supported",
                      qualified.c_str());
                continue;
            }

            // A CrVal tops out at W64, but P4 headers are wider: sai.p4's IPv6
            // addresses are bit<128>.  Split such a field into 64-bit chunks,
            // MSB first, each its own IR Header.  Extraction and emission then
            // cover it in wire order, so the packet still round-trips; what is
            // lost is the ability to SELECT on it, since one SelectCase reads
            // one Header -- and [lookupField] deliberately has no entry under
            // the unsuffixed name, so attempting to select on one is an error
            // rather than a silent truncation.
            if (width <= 64) {
                FieldInfo fi{qualified, header_uid++, width};
                fields.push_back(fi);
                fieldByQualified[fi.qualified] = fi;
                continue;
            }
            int remaining = width;
            int chunk = 0;
            while (remaining > 0) {
                int w = remaining > 64 ? 64 : remaining;
                FieldInfo fi{qualified + "#" + std::to_string(chunk), header_uid++, w};
                fields.push_back(fi);
                fieldByQualified[fi.qualified] = fi;
                remaining -= w;
                chunk++;
            }
        }
    }
    return true;
}

    // "hdr.ipv4.protocol" -> "ipv4.protocol".  The leading path expression is
    // the parameter name (hdr), which is not part of the identity of the field:
    // what distinguishes two headers is the INSTANCE, not the parameter it
    // arrived through.
    std::string qualifiedNameOf(const IR::Expression *expr) {
        auto member = expr->to<IR::Member>();
        if (member == nullptr) return "";
        std::string field = member->member.name.c_str();
        if (auto outer = member->expr->to<IR::Member>()) {
            return std::string(outer->member.name.c_str()) + "." + field;
        }
        // A parameter of struct type, reached in one step:
        // `standard_metadata.egress_spec`, or a field of `struct metadata`.
        // Keyed on the struct TYPE rather than the parameter, because the
        // parameter name is the program's choice -- v1model's own examples
        // spell the same struct `standard_metadata`, `smeta` and `sm` -- while
        // the type is what makes two references the same variable.
        if (member->expr->is<IR::PathExpression>() && typeMap != nullptr) {
            auto t = canonicalTypeOf(typeMap->getType(member->expr, false));
            if (t != nullptr) {
                if (auto ts = t->to<IR::Type_StructLike>()) {
                    return std::string(ts->name.name.c_str()) + "." + field;
                }
            }
        }
        return "";
    }

    // Resolve a header-field expression to its IR Header id.
    std::string resolveHeaderField(const IR::Expression *expr) {
        std::string qualified = qualifiedNameOf(expr);
        if (qualified.empty()) {
            error("resolveHeaderField: not a header field access: %1%", expr);
            return "1";
        }
        if (auto fi = lookupField(qualified)) return pos_to_str(fi->uid);
        error("resolveHeaderField: no Header allocated for %1%", qualified.c_str());
        return "1";
    }

    // Converts P4 operation types to a string representing the COQ operation type
    std::string p4OpToCoqOp(const IR::Operation_Binary *binOp) {
        if (binOp->is<IR::Add>()) return "AddOp";
        if (binOp->is<IR::Sub>()) return "SubOp";
        if (binOp->is<IR::BAnd>()) return "AndOp";
        if (binOp->is<IR::BOr>()) return "OrOp";
        if (binOp->is<IR::BXor>()) return "XorOp";
        if (binOp->is<IR::Mul>()) return "MulOp";
        if (binOp->is<IR::Div>()) return "DivOp";
        if (binOp->is<IR::Mod>()) return "ModOp";

        error("Unsupported binary operation: %1%", binOp);
        return "";
    }

    // =================================================================
    // Expression lowering.
    //
    // A P4 expression is a tree; an IR action is a FLAT list of HdrOps over
    // named Headers.  So lowering an expression means returning an [Operand]
    // and appending, to [ops], whatever computes it into a temporary.
    //
    // The invariant that makes this work is about TYPES, not just widths.  A
    // [CrVal] carries its [CrIntType], every arithmetic HdrOp reads BOTH
    // operands at the single [ty] it carries, and an operand whose value is
    // tagged anything else yields [ErrorVal] -- silently, and then
    // [CrVal.ltb] is false on it in both directions, so a mistyped
    // intermediate does not produce a wrong number, it produces a value every
    // later comparison fails against.  Hence: every function below states the
    // [CrIntType] its result is tagged with, and crossing between two of them
    // is an explicit [CastHeaderOp], never an implicit reinterpretation.
    // =================================================================

    // Bits in a container.  The inverse of [containerFor].
    int containerBits(const std::string &ty) const {
        if (ty == "W8") return 8;
        if (ty == "W16") return 16;
        if (ty == "W32") return 32;
        return 64;
    }

    // Low [w] bits set.  [w] of 64 or more is all ones; shifting by 64 would
    // be undefined behaviour, which is why this is not written inline.
    unsigned long long maskOf(int w) const {
        if (w <= 0) return 0ULL;
        if (w >= 64) return ~0ULL;
        return (1ULL << w) - 1ULL;
    }

    std::string constOperand(unsigned long long v) const {
        return "(OpConst " + std::to_string(v) + ")";
    }

    // A fresh Header to hold an intermediate.  Temporaries share the Header
    // namespace with real fields because that is the only namespace an
    // [Operand] can name -- there is no notion of a register or a stack slot
    // -- but they go in [temps], NOT in [fields]: they are not on the wire,
    // and [inputLenBits] would count them as packet bits.
    int newTemp(int width) {
        FieldInfo fi{"$t" + std::to_string(nextTemp++), header_uid++, width};
        temps.push_back(fi);
        return fi.uid;
    }

    // The P4 bit width an expression denotes, from the type map.  Zero when
    // the map has no entry, which every caller reports.
    int p4WidthOf(const IR::Expression *e) {
        if (typeMap == nullptr) return 0;
        return widthOf(typeMap->getType(e, false));
    }

    // The variable a Member or PathExpression names: a header field, or an
    // action parameter / local, which get Headers of their own.
    const FieldInfo *lookupVar(const IR::Expression *e) {
        if (e->is<IR::Member>()) return lookupField(qualifiedNameOf(e));
        if (auto p = e->to<IR::PathExpression>()) {
            auto it = localHeaders.find(std::string(p->path->name.name.c_str()));
            return it == localHeaders.end() ? nullptr : &it->second;
        }
        return nullptr;
    }

    // Is this operand a literal?  A literal adopts the consuming operation's
    // type ([OpConst] is width-free), so it never needs coercing -- which is
    // worth checking, because coercing one would cost a temporary and a cast
    // for nothing.
    static bool isConstOperand(const std::string &operand) {
        return operand.compare(0, 9, "(OpConst ") == 0;
    }

    // Re-tag [operand] from [from] to [to].  [CrVal.cast] masks to the TARGET
    // container, so widening zero-extends and narrowing truncates.
    std::string coerce(const std::string &operand, const std::string &from,
                       const std::string &to, std::vector<std::string> &ops) {
        if (from == to || isConstOperand(operand)) return operand;
        int t = newTemp(containerBits(to));
        ops.push_back("(CastHeaderOp " + from + " " + to + " " + operand + " " +
                      pos_to_str(t) + ")");
        return "(OpHeader " + pos_to_str(t) + ")";
    }

    // Mask [operand] (tagged [ty]) down to [w] bits.  This is what keeps a
    // field narrower than its container honest: P4 arithmetic on bit<9> is mod
    // 2^9, while [mask_width] masks to the W16 container it lives in, so
    // without this an overflow that P4 discards survives.  A no-op when the
    // field fills its container, which is the common case.
    std::string narrowTo(const std::string &operand, int w, const std::string &ty,
                         std::vector<std::string> &ops) {
        if (w <= 0 || w >= containerBits(ty)) return operand;
        int t = newTemp(containerBits(ty));
        ops.push_back("(StatelessOp AndOp " + ty + " " + operand + " " +
                      constOperand(maskOf(w)) + " " + pos_to_str(t) + ")");
        return "(OpHeader " + pos_to_str(t) + ")";
    }

    // Lower [e] at its own natural container, which is reported in [natTy].
    // Lowering at the natural container rather than at whatever the consumer
    // wants is what keeps a slice honest: evaluating `v[63:32]` at W32 would
    // truncate v to its low half BEFORE the shift, and the result would be
    // zero rather than v's top half.
    std::string lowerNat(const IR::Expression *e, std::string &natTy,
                         std::vector<std::string> &ops) {
        int w = p4WidthOf(e);
        natTy = containerFor(w > 0 ? w : 64);

        if (auto c = e->to<IR::Constant>()) {
            return constOperand(c->value.convert_to<unsigned long long>());
        }

        // A slice is a shift and a mask.  Both amounts are static: the
        // frontend has already constant-folded the bounds.
        if (auto sl = e->to<IR::Slice>()) {
            int lo = static_cast<int>(sl->getL());
            int hi = static_cast<int>(sl->getH());
            std::string srcTy;
            std::string v = lowerNat(sl->e0, srcTy, ops);
            if (lo > 0) {
                int t = newTemp(containerBits(srcTy));
                ops.push_back("(StatelessOp DivOp " + srcTy + " " + v + " " +
                              constOperand(1ULL << lo) + " " + pos_to_str(t) + ")");
                v = "(OpHeader " + pos_to_str(t) + ")";
            }
            v = narrowTo(v, hi - lo + 1, srcTy, ops);
            return coerce(v, srcTy, natTy, ops);
        }

        // `a ++ b` is `(a << width(b)) | b`, evaluated at the container of the
        // RESULT so the shift has room.  [b] is masked first: nothing
        // guarantees its container holds no bits above its declared width, and
        // one that did would corrupt [a]'s half of the answer.
        if (auto cc = e->to<IR::Concat>()) {
            int wr = p4WidthOf(cc->right);
            std::string a = lowerExpr(cc->left, natTy, ops);
            std::string b = narrowTo(lowerExpr(cc->right, natTy, ops), wr, natTy, ops);
            int t1 = newTemp(containerBits(natTy));
            ops.push_back("(StatelessOp MulOp " + natTy + " " + a + " " +
                          constOperand(1ULL << wr) + " " + pos_to_str(t1) + ")");
            int t2 = newTemp(containerBits(natTy));
            ops.push_back("(StatelessOp OrOp " + natTy + " (OpHeader " + pos_to_str(t1) +
                          ") " + b + " " + pos_to_str(t2) + ")");
            return "(OpHeader " + pos_to_str(t2) + ")";
        }

        // `~x` is xor with the ones of x's DECLARED width, not its container's.
        if (auto cm = e->to<IR::Cmpl>()) {
            std::string x = lowerExpr(cm->expr, natTy, ops);
            int t = newTemp(containerBits(natTy));
            ops.push_back("(StatelessOp XorOp " + natTy + " " + x + " " +
                          constOperand(maskOf(w)) + " " + pos_to_str(t) + ")");
            return "(OpHeader " + pos_to_str(t) + ")";
        }

        // An explicit cast.  [coerce] re-tags to the target container and
        // [narrowTo] then applies the truncation P4 means when the target is
        // narrower than that container.
        if (auto ca = e->to<IR::Cast>()) {
            std::string srcTy;
            std::string v = lowerNat(ca->expr, srcTy, ops);
            v = coerce(v, srcTy, natTy, ops);
            return narrowTo(v, w, natTy, ops);
        }

        // A shift by a constant is a multiply or a divide by a power of two.
        // The IR has no shift op, and does not need one: [MulOp] at [natTy]
        // already discards what shifts off the top, because [mask_width] masks
        // the result to the container.  A variable shift amount has no such
        // lowering and is refused.
        if (e->is<IR::Shl>() || e->is<IR::Shr>()) {
            auto bin = e->to<IR::Operation_Binary>();
            auto amt = bin->right->to<IR::Constant>();
            if (amt == nullptr) {
                error("a shift by a non-constant amount is not supported: %1%", e);
                return constOperand(0);
            }
            int k = static_cast<int>(amt->value.convert_to<unsigned long long>());
            std::string v = lowerExpr(bin->left, natTy, ops);
            if (k >= containerBits(natTy)) return constOperand(0);
            if (k > 0) {
                int t = newTemp(containerBits(natTy));
                ops.push_back("(StatelessOp " + std::string(e->is<IR::Shl>() ? "MulOp" : "DivOp") +
                              " " + natTy + " " + v + " " + constOperand(1ULL << k) + " " +
                              pos_to_str(t) + ")");
                v = "(OpHeader " + pos_to_str(t) + ")";
            }
            return narrowTo(v, w, natTy, ops);
        }

        // Ordinary arithmetic.  P4 says bit<w> arithmetic is mod 2^w, so the
        // result is narrowed to w even though the container may be wider.
        if (auto bin = e->to<IR::Operation_Binary>()) {
            std::string op = p4OpToCoqOp(bin);
            if (op.empty()) return constOperand(0);
            std::string l = lowerExpr(bin->left, natTy, ops);
            std::string r = lowerExpr(bin->right, natTy, ops);
            int t = newTemp(containerBits(natTy));
            ops.push_back("(StatelessOp " + op + " " + natTy + " " + l + " " + r + " " +
                          pos_to_str(t) + ")");
            return narrowTo("(OpHeader " + pos_to_str(t) + ")", w, natTy, ops);
        }

        // A variable: a header field, an action parameter, or a local.  Its
        // stored value is tagged with ITS container, which is what [natTy] has
        // to report -- the caller coerces.
        if (e->is<IR::Member>() || e->is<IR::PathExpression>()) {
            const FieldInfo *fi = lookupVar(e);
            if (fi == nullptr) {
                error("no Header allocated for %1%", e);
                return constOperand(0);
            }
            natTy = containerFor(fi->width);
            return "(OpHeader " + pos_to_str(fi->uid) + ")";
        }

        error("Unsupported expression: %1%", e);
        return constOperand(0);
    }

    // Lower [e] to an Operand whose value is tagged [ty].
    std::string lowerExpr(const IR::Expression *e, const std::string &ty,
                          std::vector<std::string> &ops) {
        std::string natTy;
        std::string v = lowerNat(e, natTy, ops);
        return coerce(v, natTy, ty, ops);
    }

// One assignment statement, appended to [ops] as however many HdrOps it takes.
// The target's container fixes the type the whole statement is evaluated at,
// and its declared width fixes the mask applied before the store.
void lowerAssignment(const IR::AssignmentStatement *assign, std::vector<std::string> &ops) {
    const FieldInfo *tgt = lookupVar(assign->left);
    if (tgt == nullptr) {
        error("assignment to something that is not a header field, parameter or "
              "local: %1%",
              assign->left);
        return;
    }
    std::string ty = containerFor(tgt->width);

    std::string v = lowerExpr(assign->right, ty, ops);
    v = narrowTo(v, tgt->width, ty, ops);

    // The IR has no move op, so adding zero at the target's width is one.
    // Every lowering above ends in a temporary, so this last step is what
    // names the destination.
    ops.push_back("(StatelessOp AddOp " + ty + " " + v + " (OpConst 0) " +
                  pos_to_str(tgt->uid) + ")");
}

    // Compute [e] into a fresh temporary tagged [ty] and return the Header's uid.
    int tempAt(const IR::Expression *e, const std::string &ty, std::vector<std::string> &ops) {
        std::string v = lowerExpr(e, ty, ops);
        int t = newTemp(containerBits(ty));
        ops.push_back("(StatelessOp AddOp " + ty + " " + v + " (OpConst 0) " + pos_to_str(t) + ")");
        return t;
    }

    // The Header a MatchPattern entry names on its LEFT.  A MatchPattern is a list
    // of (Header, CmpOp, MatchValue) and its left-hand side is a Header and
    // nothing else, so anything more complicated is computed into a temporary
    // first -- in [setup], which runs in a module of its own ahead of the guarded
    // one, because a match is evaluated before the rule's action.
    int matchHeaderOf(const IR::Expression *e, std::string &ty, std::vector<std::string> &setup) {
        if (const FieldInfo *fi = lookupVar(e)) {
            ty = containerFor(fi->width);
            return fi->uid;
        }
        int w = p4WidthOf(e);
        ty = containerFor(w > 0 ? w : 64);
        return tempAt(e, ty, setup);
    }

    // The MatchValue on the right.  Both sides have to carry the SAME
    // [CrIntType]: [CrVal.eqb] and [ltb] compare the type before the value and are
    // false when they differ -- in both directions -- so a mismatch does not read
    // as "not equal", it reads as "neither less nor greater nor equal".
    std::string matchValueOf(const IR::Expression *e, const std::string &ty,
                             std::vector<std::string> &setup) {
        if (auto c = e->to<IR::Constant>()) {
            return "(MatchConst " + std::to_string(c->value.convert_to<unsigned long long>()) +
                   " " + ty + ")";
        }
        if (const FieldInfo *fi = lookupVar(e)) {
            if (containerFor(fi->width) == ty) return "(MatchHeader " + pos_to_str(fi->uid) + ")";
        }
        return "(MatchHeader " + pos_to_str(tempAt(e, ty, setup)) + ")";
    }

    std::string atomSexp(int header, const std::string &cmp, const std::string &value) {
        return "(Coq_pair (Coq_pair " + pos_to_str(header) + " " + cmp + ") " + value + ")";
    }

    // One comparison.  [<=] and [>=] have no CmpOp of their own and are lowered as
    // the negations of [>] and [<].  That is exact for the values a comparison can
    // actually see here -- a parsed field or a computed integer -- and differs
    // from P4 only on [ErrorVal], where BOTH `x < k` and `x > k` are false and so
    // `not (x < k)` is not `x >= k`.  Header seeding rules that out for a parsed
    // field; see SOUNDNESS.md on why an unconstrained input must not be able to
    // become ErrorVal.
    bool lowerRelation(const IR::Operation_Binary *rel, Guard &g,
                       std::vector<std::string> &setup) {
        std::string ty;
        int h = matchHeaderOf(rel->left, ty, setup);
        std::string v = matchValueOf(rel->right, ty, setup);

        if (rel->is<IR::Equ>()) { g.pos.push_back(atomSexp(h, "CmpEq", v)); return true; }
        if (rel->is<IR::Lss>()) { g.pos.push_back(atomSexp(h, "CmpLt", v)); return true; }
        if (rel->is<IR::Grt>()) { g.pos.push_back(atomSexp(h, "CmpGt", v)); return true; }
        if (rel->is<IR::Neq>()) { g.neg.push_back({atomSexp(h, "CmpEq", v)}); return true; }
        if (rel->is<IR::Geq>()) { g.neg.push_back({atomSexp(h, "CmpLt", v)}); return true; }
        if (rel->is<IR::Leq>()) { g.neg.push_back({atomSexp(h, "CmpGt", v)}); return true; }

        error("unsupported comparison: %1%", rel);
        return false;
    }

    // A condition, as a guard.  Conjunctions merge; a negation flips; a comparison
    // is an atom; `isValid` is the parser's path condition (see [validityOf]).
    // Disjunction is refused rather than approximated.
    bool lowerCondition(const IR::Expression *cond, Guard &g, std::vector<std::string> &setup) {
        if (auto land = cond->to<IR::LAnd>()) {
            return lowerCondition(land->left, g, setup) && lowerCondition(land->right, g, setup);
        }
        if (auto lnot = cond->to<IR::LNot>()) {
            Guard inner;
            if (!lowerCondition(lnot->expr, inner, setup)) return false;
            Guard negated;
            if (!negateGuard(inner, negated)) {
                error("cannot express the negation of %1% as a match pattern; it is a "
                      "disjunction, and a MatchPattern is a conjunction",
                      lnot->expr);
                return false;
            }
            mergeGuard(g, negated);
            return true;
        }
        if (cond->is<IR::LOr>()) {
            error("a disjunction in a condition is not supported yet; it needs the "
                  "statement duplicated once per disjunct: %1%",
                  cond);
            return false;
        }
        if (auto b = cond->to<IR::BoolLiteral>()) {
            if (b->value) return true;  // `true` adds nothing
            error("a condition that is constantly false is not supported: %1%", cond);
            return false;
        }
        if (auto call = cond->to<IR::MethodCallExpression>()) {
            auto m = call->method->to<IR::Member>();
            if (m != nullptr && m->member == "isValid") {
                return validityGuard(m->expr, g);
            }
            error("unsupported call in a condition: %1%", cond);
            return false;
        }
        if (auto rel = cond->to<IR::Operation_Relation>()) {
            return lowerRelation(rel, g, setup);
        }
        error("unsupported condition: %1%", cond);
        return false;
    }

// Actions.  The ops are RETAINED under the action's name rather than streamed
// onto the output: a transformer module is assembled in [finalize] out of the
// tables that invoke these actions, so an action's ops have to outlive its
// visit.  (They used to be written straight to [coqOutput], which [finalize]
// then cleared -- so every action lowered was thrown away.)
// Give [name] a Header of [width] bits, scoped to the action being lowered.
// Parameters and locals get fresh Headers per action rather than one per
// source name: two actions that both call a parameter `port` are two distinct
// variables, and sharing a Header would alias them.
void declareLocal(const std::string &name, int width, const IR::Node *at) {
    if (width <= 0) {
        error("%1% has no bit width; only bit<N> is supported", at);
        return;
    }
    FieldInfo fi{"$v" + std::to_string(nextTemp++) + "_" + name, header_uid++, width};
    temps.push_back(fi);
    localHeaders[name] = fi;
}

bool preorder(const IR::P4Action *action) override {
    std::string actionName = action->name.name.c_str();
    actions.push_back(actionName);

    // Parameters are the action's inputs.  Nothing BINDS them yet -- that is
    // what a table entry does -- so today they read as uninitialized; the
    // point of allocating them here is that the body can refer to them.
    localHeaders.clear();
    std::vector<FieldInfo> params;
    for (auto p : action->parameters->parameters) {
        std::string pname = std::string(p->name.name.c_str());
        declareLocal(pname, widthOf(p->type), p);
        auto it = localHeaders.find(pname);
        if (it != localHeaders.end()) params.push_back(it->second);
    }
    actionParams[actionName] = params;

    std::vector<std::string> ops;
    for (auto stmt : action->body->components) {
        if (auto decl = stmt->to<IR::Declaration_Variable>()) {
            declareLocal(std::string(decl->name.name.c_str()), widthOf(decl->type), decl);
            if (decl->initializer != nullptr) {
                error("a local with an initializer is not supported yet: %1%", decl);
            }
        } else if (auto assign = stmt->to<IR::AssignmentStatement>()) {
            lowerAssignment(assign, ops);
        } else if (auto mc = stmt->to<IR::MethodCallStatement>()) {
            auto path = mc->methodCall->method->to<IR::PathExpression>();
            if (path != nullptr && path->path->name == "mark_to_drop") {
                lowerDrop(mc, ops);
            } else {
                error("only mark_to_drop is supported as a call inside an action; "
                      "calling one action from another would need it inlined: %1%",
                      mc);
            }
        } else {
            error("Unsupported statement type in action %1%: %2%", actionName.c_str(), stmt);
        }
    }

    localHeaders.clear();
    actionOps[actionName] = ops;

    // Also register under the name the SOURCE used.  The frontend renames
    // declarations to keep them unique, so an action written `set` arrives as
    // `set_0`; a --table-entries file naming an action can only reasonably
    // spell what the source said.  An alias is only taken if it is free -- two
    // controls with a same-named action would otherwise silently share one.
    if (!action->name.originalName.isNullOrEmpty()) {
        std::string orig(action->name.originalName.c_str());
        if (orig != actionName && actionOps.count(orig) == 0) {
            actionOps[orig] = ops;
            actionParams[orig] = params;
        }
    }
    return true;
}

// The HdrOps an action lowered to, or nullptr if it was never visited.
const std::vector<std::string> *opsOfAction(const std::string &name) const {
    auto it = actionOps.find(name);
    return it == actionOps.end() ? nullptr : &it->second;
}

// The Headers holding an action's parameters, in declaration order.
const std::vector<FieldInfo> *paramsOfAction(const std::string &name) const {
    auto it = actionParams.find(name);
    return it == actionParams.end() ? nullptr : &it->second;
}

    // Tables are RECORDED, not lowered here: a table is lowered where it is
    // applied, because that is where its guard comes from, and by then its
    // actions have been visited.
    bool preorder(const IR::P4Table *table) override {
        std::string name = table->name.name.c_str();
        if (tablesByName.count(name) && tablesByName[name] != table) {
            warning(P4::ErrorType::WARN_DUPLICATE,
                    "two tables are named %1%; entries supplied by name cannot tell them "
                    "apart",
                    table->name);
        }
        tablesByName[name] = table;
        return true;
    }

    // ------------------------------------------------------------------
    // Tables.
    //
    // A table IS a match-action unit and so is a transformer module: rules in
    // priority order, of which exactly one fires.  The entries become the
    // rules, in order, with the enclosing guard conjoined onto each -- a table
    // applied under `if (hdr.ipv4.isValid())` has that test in every rule.
    //
    // The entries have to be STATIC.  A runtime-populated table could in
    // principle be modelled by lowering an action's parameters to OpCtrlPlane,
    // but a Ctrl variable is seeded per program (CrVarLike.v, `prefix ++
    // "ctrl_"`), so the two programs a comparison is about would get unrelated
    // configurations and the solver would satisfy "the outputs differ" by
    // handing them different tables.  See TODO.md 1.7.  Until that changes,
    // entries come from `const entries` or from --table-entries, and a table
    // with neither is an error rather than a guess.

    // How specific an entry is: exact keys count their full width, a mask
    // counts its set bits, a wildcard counts nothing.  P4 resolves an lpm table
    // by longest prefix, and a rule list resolves by order, so ordering the
    // entries by this is what makes the two agree.
    static int prefixBitsOf(unsigned long long mask, int width) {
        int n = 0;
        for (int i = 0; i < width; ++i) {
            if ((mask >> i) & 1ULL) ++n;
        }
        return n;
    }

    // One key element: the Header a rule matches on, plus its type.  A key that
    // is not already a variable is computed into a temporary in [setup].
    struct KeyInfo {
        int uid = 0;
        std::string ty;
        int width = 0;
    };

    // Bind an action's parameters to an entry's arguments, then run its body.
    // The parameters already have Headers of their own (see [declareLocal]), so
    // binding is a move into each -- and because exactly one rule of a
    // transformer fires, two entries calling the same action with different
    // arguments cannot interfere.
    bool lowerActionCall(const RawEntry &e, std::vector<std::string> &ops, const IR::Node *at) {
        if (e.action == "NoAction") return true;

        const std::vector<std::string> *aops = opsOfAction(e.action);
        const std::vector<FieldInfo> *params = paramsOfAction(e.action);
        if (aops == nullptr || params == nullptr) {
            error("%1%: %2% is not an action of this control", at, e.action.c_str());
            return false;
        }
        if (e.args.size() != params->size()) {
            error("%1%: %2% takes %3% arguments but the entry supplies %4%", at,
                  e.action.c_str(), (int)params->size(), (int)e.args.size());
            return false;
        }
        for (size_t i = 0; i < params->size(); ++i) {
            const FieldInfo &pf = params->at(i);
            std::string ty = containerFor(pf.width);
            ops.push_back("(StatelessOp AddOp " + ty + " " + constOperand(e.args[i]) +
                          " (OpConst 0) " + pos_to_str(pf.uid) + ")");
        }
        ops.insert(ops.end(), aops->begin(), aops->end());
        return true;
    }

    // One keyset element against one key: an atom, or nothing for a wildcard.
    // A masked match needs the masking done BEFORE the rule is tried -- a match
    // pattern compares a Header, it does not compute -- so it lands in [setup]
    // and the atom compares the temporary.
    void lowerKeySet(const RawKey &ks, const KeyInfo &key, std::vector<std::string> &atoms,
                     std::vector<std::string> &setup, int &bits) {
        if (ks.wildcard) return;  // no atom at all, which is what "don't care" is
        RawKey k = ks;
        if (k.prefixLen >= 0) {
            k.masked = true;
            k.mask = k.prefixLen >= key.width
                         ? maskOf(key.width)
                         : (maskOf(k.prefixLen) << (key.width - k.prefixLen));
        }
        const RawKey &ksr = k;
        if (!ksr.masked) {
            bits += key.width;
            atoms.push_back(atomSexp(
                key.uid, "CmpEq",
                "(MatchConst " + std::to_string(ksr.value) + " " + key.ty + ")"));
            return;
        }
        bits += prefixBitsOf(ksr.mask, key.width);
        int t = newTemp(containerBits(key.ty));
        setup.push_back("(StatelessOp AndOp " + key.ty + " (OpHeader " + pos_to_str(key.uid) +
                        ") " + constOperand(ksr.mask) + " " + pos_to_str(t) + ")");
        atoms.push_back(atomSexp(
            t, "CmpEq",
            "(MatchConst " + std::to_string(ksr.value & ksr.mask) + " " + key.ty + ")"));
    }

    // A keyset expression from `const entries`, as a RawKey.
    bool rawKeyOf(const IR::Expression *ks, RawKey &out) {
        if (ks->is<IR::DefaultExpression>()) {
            out.wildcard = true;
            return true;
        }
        if (auto m = ks->to<IR::Mask>()) {
            auto val = m->left->to<IR::Constant>();
            auto msk = m->right->to<IR::Constant>();
            if (val == nullptr || msk == nullptr) {
                error("a masked entry needs constant bounds: %1%", ks);
                return false;
            }
            out.masked = true;
            out.value = val->value.convert_to<unsigned long long>();
            out.mask = msk->value.convert_to<unsigned long long>();
            return true;
        }
        if (auto c = ks->to<IR::Constant>()) {
            out.value = c->value.convert_to<unsigned long long>();
            return true;
        }
        error("unsupported entry keyset %1%; a range has no match-pattern equivalent", ks);
        return false;
    }

    // The name a --table-entries file can reasonably use.  The frontend
    // renames declarations to keep them unique, so a table written `calc`
    // arrives here as `calc_0`; [IR::ID::originalName] is what the source
    // said.  The external name ("MyIngress.calc") is accepted too, so a
    // program with two same-named tables in different controls can still be
    // told apart.
    std::vector<std::string> entryNamesOf(const IR::P4Table *table) const {
        std::vector<std::string> names;
        if (!table->name.originalName.isNullOrEmpty()) {
            names.push_back(std::string(table->name.originalName.c_str()));
        }
        names.push_back(std::string(table->name.name.c_str()));
        cstring ext = table->externalName();
        if (!ext.isNullOrEmpty()) {
            std::string e(ext.c_str());
            names.push_back(e);
            auto dot = e.rfind('.');
            if (dot != std::string::npos) names.push_back(e.substr(dot + 1));
        }
        return names;
    }

    // The entries of a table: `const entries` if it has them, else whatever
    // --table-entries supplied for it.  A table with neither is an error --
    // guessing would mean inventing a forwarding table, and the verdict would
    // be about a program nobody wrote.
    bool entriesFor(const IR::P4Table *table, size_t nkeys, std::vector<RawEntry> &out) {
        std::vector<std::string> names = entryNamesOf(table);
        std::string tname = names.front();
        if (auto el = table->getEntries()) {
            for (auto e : el->entries) {
                RawEntry re;
                const IR::ListExpression *ks = e->keys;
                size_t n = ks == nullptr ? 0 : ks->components.size();
                if (n != nkeys) {
                    error("entry of %1% has %2% keys but the table has %3%", e, (int)n,
                          (int)nkeys);
                    return false;
                }
                for (size_t i = 0; i < n; ++i) {
                    RawKey rk;
                    if (!rawKeyOf(ks->components.at(i), rk)) return false;
                    re.keys.push_back(rk);
                }
                auto mce = e->action->to<IR::MethodCallExpression>();
                auto path = mce == nullptr ? nullptr : mce->method->to<IR::PathExpression>();
                if (path == nullptr) {
                    error("an entry's action must name an action: %1%", e->action);
                    return false;
                }
                re.action = path->path->name.name.c_str();
                for (auto a : *mce->arguments) {
                    auto c = a->expression->to<IR::Constant>();
                    if (c == nullptr) {
                        error("an entry's action arguments must be constants: %1%", a);
                        return false;
                    }
                    re.args.push_back(c->value.convert_to<unsigned long long>());
                }
                out.push_back(re);
            }
            return true;
        }

        auto it = suppliedEntries.end();
        for (const auto &n : names) {
            it = suppliedEntries.find(n);
            if (it != suppliedEntries.end()) break;
        }
        if (it == suppliedEntries.end()) {
            error("table %1% has no `const entries` and none were supplied for it; pass "
                  "--table-entries FILE. A runtime-populated table cannot be lowered: a "
                  "Ctrl variable is seeded per program, so the two programs compared would "
                  "get unrelated configurations",
                  tname.c_str());
            return false;
        }
        for (const auto &re : it->second) {
            if (re.keys.size() != nkeys) {
                error("supplied entry for %1% has %2% keys but the table has %3%",
                      tname.c_str(), (int)re.keys.size(), (int)nkeys);
                return false;
            }
            out.push_back(re);
        }
        return true;
    }

    // Read a --table-entries file.  One entry per line:
    //
    //     <table> <key> [<key> ...] -> <action> [<arg> ...]
    //
    // A key is a number (exact), `v/n` (an lpm prefix of n bits), `v&&&m`
    // (ternary), or `*` (don't care).  Numbers are decimal, or hex with 0x.
    // Blank lines and `#` comments are skipped.
    //
    // This exists because a table populated by the control plane has no
    // entries in its source, and the alternative -- lowering action parameters
    // to OpCtrlPlane -- does not work while a Ctrl variable is seeded per
    // program: the solver would satisfy "the outputs differ" by giving the two
    // programs different tables.  TODO.md 1.7.
    bool loadTableEntries(const std::string &path) {
        std::ifstream in(path);
        if (!in.is_open()) {
            error("cannot open table entries file %1%", path.c_str());
            return false;
        }
        std::string line;
        int lineNo = 0;
        while (std::getline(in, line)) {
            ++lineNo;
            auto hash = line.find('#');
            if (hash != std::string::npos) line = line.substr(0, hash);
            std::vector<std::string> tok;
            std::istringstream ls(line);
            std::string t;
            while (ls >> t) tok.push_back(t);
            if (tok.empty()) continue;

            size_t arrow = 0;
            while (arrow < tok.size() && tok[arrow] != "->") ++arrow;
            if (arrow == tok.size() || arrow < 2 || arrow + 1 >= tok.size()) {
                error("%1%:%2%: expected `<table> <key>... -> <action> [<arg>...]`",
                      path.c_str(), lineNo);
                return false;
            }

            RawEntry e;
            for (size_t i = 1; i < arrow; ++i) {
                RawKey k;
                const std::string &ks = tok[i];
                if (ks == "*" || ks == "_") {
                    k.wildcard = true;
                } else if (ks.find("&&&") != std::string::npos) {
                    size_t at = ks.find("&&&");
                    k.masked = true;
                    k.value = strtoull(ks.substr(0, at).c_str(), nullptr, 0);
                    k.mask = strtoull(ks.substr(at + 3).c_str(), nullptr, 0);
                } else if (ks.find('/') != std::string::npos) {
                    size_t at = ks.find('/');
                    k.value = strtoull(ks.substr(0, at).c_str(), nullptr, 0);
                    k.prefixLen = static_cast<int>(strtoul(ks.substr(at + 1).c_str(), nullptr, 0));
                } else {
                    k.value = strtoull(ks.c_str(), nullptr, 0);
                }
                e.keys.push_back(k);
            }
            e.action = tok[arrow + 1];
            for (size_t i = arrow + 2; i < tok.size(); ++i) {
                e.args.push_back(strtoull(tok[i].c_str(), nullptr, 0));
            }
            suppliedEntries[tok[0]].push_back(e);
        }
        return true;
    }

    void lowerTableApply(const IR::P4Table *table, const Guard &g, std::vector<Group> &out) {
        std::vector<std::string> setup;

        std::vector<KeyInfo> keys;
        if (auto k = table->getKey()) {
            for (auto ke : k->keyElements) {
                std::string mk = ke->matchType->path->name.name.c_str();
                if (mk != "exact" && mk != "lpm" && mk != "ternary") {
                    error("match kind %1% is not supported; only exact, lpm and ternary "
                          "have match-pattern equivalents",
                          mk.c_str());
                    return;
                }
                KeyInfo ki;
                ki.width = p4WidthOf(ke->expression);
                ki.uid = matchHeaderOf(ke->expression, ki.ty, setup);
                keys.push_back(ki);
            }
        }

        std::vector<RawEntry> entries;
        if (!entriesFor(table, keys.size(), entries)) return;

        std::vector<Alt> alts;
        for (const auto &e : entries) {
            Alt alt;
            for (size_t i = 0; i < keys.size(); ++i) {
                lowerKeySet(e.keys[i], keys[i], alt.atoms, setup, alt.priority);
            }
            if (!lowerActionCall(e, alt.ops, table)) return;
            alts.push_back(alt);
        }

        // Longest prefix first.  P4 resolves an lpm table by longest prefix and
        // a rule list resolves by order, so sorting on specificity is what
        // makes the two agree.  A stable sort leaves equally specific entries
        // -- every entry of an exact table -- in the order they were given.
        std::stable_sort(alts.begin(), alts.end(),
                         [](const Alt &a, const Alt &b) { return a.priority > b.priority; });

        // The default action matches whatever the entries did not, which is
        // what an arm with no atoms of its own means once the arms above it
        // have been tried.  NoAction contributes no arm at all.
        if (auto da = table->getDefaultAction()) {
            RawEntry de;
            auto mce = da->to<IR::MethodCallExpression>();
            auto path = mce == nullptr ? nullptr : mce->method->to<IR::PathExpression>();
            if (path == nullptr) {
                error("a default action must name an action: %1%", da);
                return;
            }
            de.action = path->path->name.name.c_str();
            for (auto a : *mce->arguments) {
                auto c = a->expression->to<IR::Constant>();
                if (c == nullptr) {
                    error("a default action's arguments must be constants: %1%", a);
                    return;
                }
                de.args.push_back(c->value.convert_to<unsigned long long>());
            }
            Alt alt;
            if (!lowerActionCall(de, alt.ops, table)) return;
            if (!alt.ops.empty()) alts.push_back(alt);
        }

        if (!setup.empty()) out.push_back(Group{g, {}, {Alt{{}, setup, 0}}});
        if (!alts.empty()) out.push_back(Group{g, {}, alts});
    }

    // ------------------------------------------------------------------
    // Parser.
    //
    // INGRESS ONLY.  A P4 pipeline is ingress and egress, each with its own
    // parser and deparser, and the egress parser re-parses what the ingress
    // deparser emitted.  The IR cannot express that handoff: a deparser
    // APPENDS to sh_write_tape and a parser reads sh_read_tape, and nothing
    // feeds one into the other, so chaining both pipelines would have the
    // egress parser reading the leftover of the original input.  The first
    // parser and the first packet_out control are taken; later ones warn.

    std::vector<std::string> fieldsOfInstance(const std::string &inst) {
        std::vector<std::string> out;
        const std::string prefix = inst + ".";
        for (const auto &f : fields) {
            if (!f.onWire) continue;
            if (f.qualified.compare(0, prefix.size(), prefix) == 0) out.push_back(f.qualified);
        }
        return out;
    }

    // "hdr.ipv4" -> "ipv4"
    std::string instanceNameOf(const IR::Expression *e) {
        if (auto m = e->to<IR::Member>()) return m->member.name.c_str();
        return "";
    }

    // A [ParserTarget]: accept/reject are pseudo-states, anything else is a
    // label that must already have an entry in stateLabel.
    std::string targetOf(const IR::Expression *e) {
        auto path = e->to<IR::PathExpression>();
        if (path == nullptr) {
            error("unsupported transition target %1%", e);
            return "Reject";
        }
        std::string name = path->path->name.name.c_str();
        if (name == "accept") return "Accept";
        if (name == "reject") return "Reject";
        auto it = stateLabel.find(name);
        if (it == stateLabel.end()) {
            error("transition to unknown parser state %1%", name.c_str());
            return "Reject";
        }
        return "(TargetState " + pos_to_str(it->second) + ")";
    }

    // A [Transition].  Only single-key selects are handled: an n-tuple select
    // decomposes into a chain of single-key states, which is a frontend
    // transformation and not needed for the programs targeted so far.
    std::string transitionOf(const IR::Expression *sel) {
        if (sel == nullptr) return "(Unconditional Reject)";
        if (sel->is<IR::PathExpression>()) {
            return "(Unconditional " + targetOf(sel) + ")";
        }
        auto select = sel->to<IR::SelectExpression>();
        if (select == nullptr) {
            error("unsupported transition %1%", sel);
            return "(Unconditional Reject)";
        }
        if (select->select->components.size() != 1) {
            error("tuple select (%1% keys) is not supported; split it into a "
                  "chain of single-key states",
                  (int)select->select->components.size());
            return "(Unconditional Reject)";
        }
        const IR::Expression *key = select->select->components.at(0);
        std::string qualified = qualifiedNameOf(key);
        const FieldInfo *fi = lookupField(qualified);
        if (fi == nullptr) {
            error("select key %1% is not a header field", key);
            return "(Unconditional Reject)";
        }

        std::vector<std::string> cases;
        std::string dflt = "Reject";
        for (auto c : select->selectCases) {
            if (c->keyset->is<IR::DefaultExpression>()) {
                dflt = targetOf(c->state);
                continue;
            }
            auto k = c->keyset->to<IR::Constant>();
            if (k == nullptr) {
                error("unsupported select keyset %1%; masks and ranges are not "
                      "expressible as a SelectCase pattern",
                      c->keyset);
                continue;
            }
            // Where the case reads its bits is a [SelBits]: [SelHdr h s e] for
            // an already-parsed header field, [Peek off width] for a
            // lookahead.  A select on a header field is the former, over the
            // whole field -- slice_val is LSB-indexed, so that is [0, width).
            //
            // The pattern is compared by bits_to_Z, but its LENGTH is what the
            // slice is matched against, so it carries leading zeros out to the
            // field width.  It is MSB-first; [bits_to_str] emits the Coq_cons
            // chain CrTypeIF.ml's derived converters accept.  Shape reference:
            // ~/proj/ir/test/parse_reject_deparse.ir.
            std::ostringstream cs;
            cs << "((sc_origin (SelHdr " << pos_to_str(fi->uid) << " 0 " << fi->width
               << ")) (sc_pattern "
               << bits_to_str(k->value.convert_to<unsigned long long>(), fi->width)
               << ") (sc_target " << targetOf(c->state) << "))";
            cases.push_back(cs.str());
        }
        return "(Select " + listSexp(cases) + " " + dflt + ")";
    }

    bool preorder(const IR::P4Parser *parser) override {
        if (parserStates.empty()) computeValidity(parser);
        if (!parserStates.empty()) {
            warning(P4::ErrorType::WARN_IGNORE_PROPERTY,
                    "ignoring parser %1%: only the ingress parser is translated",
                    parser->name);
            return false;
        }

        // Pass 1: an entry label per P4 state, so a transition can name a
        // state defined later in the file.
        for (auto st : parser->states) {
            std::string n = st->name.name.c_str();
            if (n == "accept" || n == "reject") continue;
            stateLabel[n] = nextParserLabel++;
        }

        // Pass 2: emit.  psd_action holds ONE ParserOp, but b.extract(hdr.X)
        // fills every field of X, so a state with an n-field extract becomes a
        // chain of n IR states; the last one carries the transition.
        for (auto st : parser->states) {
            std::string n = st->name.name.c_str();
            if (n == "accept" || n == "reject") continue;

            std::vector<std::string> extracted;  // qualified field names, in order
            for (auto c : st->components) {
                auto mc = c->to<IR::MethodCallStatement>();
                if (mc == nullptr) {
                    error("unsupported statement in parser state %1%", n.c_str());
                    continue;
                }
                auto m = mc->methodCall->method->to<IR::Member>();
                if (m == nullptr || m->member != "extract") {
                    error("only b.extract is supported in a parser state (%1%)", n.c_str());
                    continue;
                }
                if (mc->methodCall->arguments->size() != 1) {
                    error("b.extract with %1% arguments is not supported",
                          (int)mc->methodCall->arguments->size());
                    continue;
                }
                std::string inst =
                    instanceNameOf(mc->methodCall->arguments->at(0)->expression);
                for (const auto &q : fieldsOfInstance(inst)) extracted.push_back(q);
                if (fieldsOfInstance(inst).empty()) {
                    error("b.extract(%1%) names no allocated header instance", inst.c_str());
                }
            }

            std::string trans = transitionOf(st->selectExpression);

            if (extracted.empty()) {
                emitParserState(stateLabel[n], "None", trans);
                continue;
            }
            for (size_t i = 0; i < extracted.size(); ++i) {
                const FieldInfo *fi = lookupField(extracted[i]);
                std::ostringstream act;
                act << "(Some (ExtractOpConstructor " << pos_to_str(fi->uid) << " "
                    << fi->width << " " << containerFor(fi->width) << "))";
                bool last = (i + 1 == extracted.size());
                int label = (i == 0) ? stateLabel[n] : nextParserLabel++;
                // A chained state's successor is allocated as we go, so the
                // label of state i+1 has to be known before state i is emitted.
                if (!last) {
                    int next = nextParserLabel;  // what the next iteration takes
                    emitParserState(label, act.str(),
                                    "(Unconditional (TargetState " + pos_to_str(next) + "))");
                } else {
                    emitParserState(label, act.str(), trans);
                }
            }
        }
        return false;
    }

    void emitParserState(int label, const std::string &action, const std::string &trans) {
        std::ostringstream ss;
        ss << "((psd_label " << pos_to_str(label) << ") (psd_action " << action
           << ") (psd_trans " << trans << "))";
        parserStates.push_back(ss.str());
    }

    // Validity, walked off the parser AST.  See [validityOf].
    void computeValidity(const IR::P4Parser *parser) {
        std::map<cstring, const IR::ParserState *> byName;
        for (auto st : parser->states) byName[st->name] = st;
        std::set<cstring> seen;
        walkParser(byName, cstring("start"), Guard{}, seen);
    }

    void walkParser(const std::map<cstring, const IR::ParserState *> &byName, cstring name,
                    const Guard &g, std::set<cstring> &seen) {
        if (name == "accept" || name == "reject") return;
        // Already reached by another path: this state's headers are valid for
        // two different reasons, and their disjunction is not a guard.
        if (!seen.insert(name).second) {
            parserIsTree = false;
            return;
        }
        auto it = byName.find(name);
        if (it == byName.end()) return;
        const IR::ParserState *st = it->second;

        for (auto c : st->components) {
            auto mc = c->to<IR::MethodCallStatement>();
            if (mc == nullptr) continue;
            auto m = mc->methodCall->method->to<IR::Member>();
            if (m == nullptr || m->member != "extract") continue;
            if (mc->methodCall->arguments->size() != 1) continue;
            std::string inst = instanceNameOf(mc->methodCall->arguments->at(0)->expression);
            if (!inst.empty() && validityOf.count(inst) == 0) validityOf[inst] = g;
        }

        const IR::Expression *sel = st->selectExpression;
        if (sel == nullptr) return;
        if (auto path = sel->to<IR::PathExpression>()) {
            walkParser(byName, path->path->name, g, seen);
            return;
        }
        auto select = sel->to<IR::SelectExpression>();
        if (select == nullptr || select->select->components.size() != 1) {
            parserIsTree = false;
            return;
        }
        const FieldInfo *kf = lookupVar(select->select->components.at(0));
        if (kf == nullptr) {
            parserIsTree = false;
            return;
        }
        std::string ty = containerFor(kf->width);

        // Cases are tried in order, so a later case also requires that every
        // earlier one missed -- and the default requires that all of them did.
        std::vector<std::string> taken;
        for (auto c : select->selectCases) {
            Guard cg = g;
            for (const auto &t : taken) cg.neg.push_back({t});
            if (!c->keyset->is<IR::DefaultExpression>()) {
                auto k = c->keyset->to<IR::Constant>();
                if (k == nullptr) {
                    parserIsTree = false;
                    return;
                }
                std::string atom = atomSexp(
                    kf->uid, "CmpEq",
                    "(MatchConst " + std::to_string(k->value.convert_to<unsigned long long>()) +
                        " " + ty + ")");
                cg.pos.push_back(atom);
                taken.push_back(atom);
            }
            auto tp = c->state->to<IR::PathExpression>();
            if (tp == nullptr) {
                parserIsTree = false;
                return;
            }
            walkParser(byName, tp->path->name, cg, seen);
        }
    }

    bool validityGuard(const IR::Expression *hdrRef, Guard &g) {
        std::string inst = instanceNameOf(hdrRef);
        auto it = validityOf.find(inst);
        if (it == validityOf.end()) {
            error("cannot tell whether %1% is valid: no parser state extracts it", hdrRef);
            return false;
        }
        if (!parserIsTree) {
            error("cannot tell whether %1% is valid: the parser is not a tree, so its "
                  "validity is a disjunction over paths and not a match pattern",
                  hdrRef);
            return false;
        }
        mergeGuard(g, it->second);
        return true;
    }

    // ------------------------------------------------------------------
    // Deparser: the first control taking a packet_out.  b.emit(hdr.X) becomes
    // one EmitOpConstructor per field of X, in declaration order.
    bool preorder(const IR::P4Control *control) override {
        bool isDeparser = false;
        for (auto p : control->type->applyParams->parameters) {
            if (auto tn = p->type->to<IR::Type_Name>()) {
                if (tn->path->name == "packet_out") isDeparser = true;
            }
        }
        if (!isDeparser) {
            // A checksum control takes (hdr, meta); a pipeline control also
            // takes the intrinsic metadata.  That is what tells them apart
            // without reading the package instantiation, which is where the
            // roles are really written down.
            if (control->type->applyParams->parameters.size() >= 3) {
                pipelineControls.push_back(control);
            }
            return true;  // descend, so its actions and tables get visited
        }
        if (!deparserEmits.empty()) {
            warning(P4::ErrorType::WARN_IGNORE_PROPERTY,
                    "ignoring deparser %1%: only the ingress deparser is translated",
                    control->name);
            return false;
        }
        for (auto c : control->body->components) {
            auto mc = c->to<IR::MethodCallStatement>();
            if (mc == nullptr) continue;
            auto m = mc->methodCall->method->to<IR::Member>();
            if (m == nullptr || m->member != "emit") continue;
            if (mc->methodCall->arguments->size() != 1) continue;
            std::string inst = instanceNameOf(mc->methodCall->arguments->at(0)->expression);
            for (const auto &q : fieldsOfInstance(inst)) {
                const FieldInfo *fi = lookupField(q);
                deparserEmits.push_back("(EmitOpConstructor " + pos_to_str(fi->uid) + " " +
                                        std::to_string(fi->width) + ")");
            }
        }
        return false;
    }

    // ------------------------------------------------------------------
    // Statements.

    // Dropping needs no new IR concept: bmv2 drops by setting the egress port
    // to a reserved value, and so does this.  The port is emitted by the
    // deparser like any other metadata output, which is what makes a dropped
    // packet distinguishable from a forwarded one in the compared output.
    bool lowerDrop(const IR::Node *at, std::vector<std::string> &ops) {
        const FieldInfo *fi = lookupField("standard_metadata_t.egress_spec");
        if (fi == nullptr) {
            error("mark_to_drop with no standard_metadata_t.egress_spec in scope: %1%", at);
            return false;
        }
        std::string ty = containerFor(fi->width);
        ops.push_back("(StatelessOp AddOp " + ty + " " + constOperand(V1MODEL_DROP_PORT) +
                      " (OpConst 0) " + pos_to_str(fi->uid) + ")");
        return true;
    }

    // A call in an apply block: an action of this control, or [mark_to_drop].
    // Returns true when it filled [ops] with something the caller should wrap
    // in a group.  A TABLE apply returns false having already pushed its own
    // groups onto [out] -- a table is many rules, not one op list.
    bool lowerCall(const IR::MethodCallStatement *mc, std::vector<std::string> &ops,
                   const Guard &g, std::vector<Group> &out) {
        auto method = mc->methodCall->method;
        if (auto m = method->to<IR::Member>()) {
            if (m->member != "apply") {
                error("unsupported method call in an apply block: %1%", mc);
                return false;
            }
            auto tpath = m->expr->to<IR::PathExpression>();
            auto tit = tpath == nullptr
                           ? tablesByName.end()
                           : tablesByName.find(std::string(tpath->path->name.name.c_str()));
            if (tit == tablesByName.end()) {
                error("apply on something that is not a table of this control: %1%", mc);
                return false;
            }
            lowerTableApply(tit->second, g, out);
            return false;
        }
        auto path = method->to<IR::PathExpression>();
        if (path == nullptr) {
            error("unsupported call in an apply block: %1%", mc);
            return false;
        }
        std::string callee = path->path->name.name.c_str();

        if (callee == "mark_to_drop") return lowerDrop(mc, ops);

        const std::vector<std::string> *aops = opsOfAction(callee);
        if (aops == nullptr) {
            error("%1% is not an action of this control; externs are not supported yet",
                  callee.c_str());
            return false;
        }
        if (!mc->methodCall->arguments->empty()) {
            error("an action called with arguments is not supported yet: %1%", mc);
            return false;
        }
        ops.insert(ops.end(), aops->begin(), aops->end());
        return true;
    }

    // Flatten a statement into guarded groups.  The guard accumulated on the
    // way down is the statement's path condition; see the comment on [Guard].
    void flattenStatement(const IR::StatOrDecl *s, const Guard &g, std::vector<Group> &out) {
        if (auto blk = s->to<IR::BlockStatement>()) {
            for (auto c : blk->components) flattenStatement(c, g, out);
            return;
        }
        if (auto ifs = s->to<IR::IfStatement>()) {
            Guard cond;
            std::vector<std::string> setup;
            if (!lowerCondition(ifs->condition, cond, setup)) return;
            // Whatever the condition had to compute runs UNGUARDED by the
            // condition itself -- it is what the condition reads -- so it is a
            // group of its own, ahead of both branches.
            if (!setup.empty()) out.push_back(Group{g, {}, {Alt{{}, setup, 0}}});

            Guard thenG = g;
            mergeGuard(thenG, cond);
            flattenStatement(ifs->ifTrue, thenG, out);

            if (ifs->ifFalse != nullptr) {
                Guard notCond;
                if (!negateGuard(cond, notCond)) {
                    error("cannot express the else branch of %1%: the negation of its "
                          "condition is a disjunction",
                          ifs->condition);
                    return;
                }
                Guard elseG = g;
                mergeGuard(elseG, notCond);
                flattenStatement(ifs->ifFalse, elseG, out);
            }
            return;
        }
        if (auto assign = s->to<IR::AssignmentStatement>()) {
            std::vector<std::string> ops;
            lowerAssignment(assign, ops);
            if (!ops.empty()) out.push_back(Group{g, {}, {Alt{{}, ops, 0}}});
            return;
        }
        if (auto mc = s->to<IR::MethodCallStatement>()) {
            std::vector<std::string> ops;
            if (lowerCall(mc, ops, g, out) && !ops.empty())
                out.push_back(Group{g, {}, {Alt{{}, ops, 0}}});
            return;
        }
        if (s->is<IR::EmptyStatement>()) return;
        error("unsupported statement in an apply block: %1%", s);
    }

    // ------------------------------------------------------------------
    // The pipeline controls, as a chain of transformer modules.
    //
    // Run from [finalize], not from a visitor, for two reasons: a control's
    // actions are its children and are not lowered until after its preorder,
    // and the package instantiation that says which control plays which role
    // is declared LAST, after every control it names.  Until that
    // instantiation is read -- which is what tells ingress from egress -- the
    // order here is declaration order.
    std::vector<Group> lowerPipelineControls() {
        std::vector<Group> groups;

        // bmv2 hands a control a zeroed `struct metadata`; the IR hands it
        // UninitVal, which is not zero and not even comparable -- CrVal.eqb
        // and ltb are false against it in both directions, so a
        // read-before-write does not read as 0, it reads as a value every
        // later test fails against.  One unguarded group closes the gap.
        //
        // standard_metadata_t is deliberately NOT zeroed: its input fields
        // (ingress_port, packet_length, the timestamps) are environment
        // inputs, and pinning them to zero would be a different and wronger
        // lie than leaving them uninitialized.  Giving them free values means
        // extracting them from a metadata prefix ahead of the packet, which is
        // not done yet.
        std::vector<std::string> zeroing;
        for (const auto &f : fields) {
            if (f.onWire) continue;
            if (f.qualified.rfind("standard_metadata_t.", 0) == 0) continue;
            std::string ty = containerFor(f.width);
            zeroing.push_back("(StatelessOp AddOp " + ty + " (OpConst 0) (OpConst 0) " +
                              pos_to_str(f.uid) + ")");
        }
        if (!zeroing.empty()) groups.push_back(Group{Guard{}, {}, {Alt{{}, zeroing, 0}}});

        for (auto control : pipelineControls) {
            flattenStatement(control->body, Guard{}, groups);
        }

        // Adjacent statements under the same guard share a module: only one
        // rule of a transformer fires, so they could not share a RULE without
        // this, and a module apiece would make the chain as long as the
        // program.
        std::vector<Group> merged;
        for (auto &g : groups) {
            bool plain = g.alts.size() == 1 && g.alts[0].atoms.empty();
            bool prevPlain = !merged.empty() && merged.back().alts.size() == 1 &&
                             merged.back().alts[0].atoms.empty();
            if (plain && prevPlain && sameGuard(merged.back().guard, g.guard)) {
                auto &into = merged.back().alts[0].ops;
                into.insert(into.end(), g.alts[0].ops.begin(), g.alts[0].ops.end());
            } else {
                merged.push_back(g);
            }
        }
        return merged;
    }

    // A group's rule list.  See the comment on [Guard]: the negative clauses
    // come first as no-ops, so that reaching the positive rule already means
    // none of them held, and the trailing empty rule is "the guard did not
    // hold" -- without it a transformer whose guard fails would fall through
    // to no rule at all, which is the same thing, but only by accident.
    std::string rulesOf(const Group &grp) {
        std::vector<std::string> rules;
        for (const auto &n : grp.guard.neg) {
            rules.push_back("(Seq (SeqCtr " + listSexp(n) + " Coq_nil))");
        }
        for (const auto &alt : grp.alts) {
            std::vector<std::string> pattern = grp.guard.pos;
            pattern.insert(pattern.end(), alt.atoms.begin(), alt.atoms.end());
            rules.push_back("(Seq (SeqCtr " + listSexp(pattern) + " " + listSexp(alt.ops) +
                            "))");
        }
        rules.push_back("(Seq (SeqCtr Coq_nil Coq_nil))");
        return listSexp(rules);
    }

    // Build a Coq list into a string rather than onto coqOutput.
    std::string listSexp(const std::vector<std::string> &elements) {
        if (elements.empty()) return "Coq_nil";
        std::string s;
        for (const auto &e : elements) s += "(Coq_cons " + e + " ";
        s += "Coq_nil";
        for (size_t i = 0; i < elements.size(); ++i) s += ")";
        return s;
    }

    // ------------------------------------------------------------------
    // Emit the program.  ONE GeneralCaracaraProgramDef, built here rather
    // than streamed during traversal -- the previous version opened the
    // constructor in its own ctor and printed a (headers, nil, nil) triple per
    // header TYPE, so an N-header program produced a constructor applied to 3N
    // arguments instead of 4.
    //
    //   (GeneralCaracaraProgramDef <inp_len> <regions> <network>)
    //
    // Reference for the shape: ~/proj/ir/test/parse_reject_deparse.ir, which
    // corresponds to mod_prog_parse_reject_deparse in TestModulePrograms.v.
    //
    // The parser and deparser are real; there is no transformer module yet, so
    // the network a program lowers to today is parser -> deparser and the
    // control blocks are dropped.  Nothing streams onto [coqOutput] during
    // traversal any more, so nothing here has to clear it.
    void finalize() {
        std::vector<Group> groups = lowerPipelineControls();

        const int parserId = 1;
        const int deparserId = 2;

        if (parserStates.empty()) {
            // No parser in the program: a single accepting state keeps the
            // network well formed.
            emitParserState(1, "None", "(Unconditional Accept)");
        }

        std::ostringstream parser;
        parser << "(ParserModule " << pos_to_str(parserId) << " ((parser_start "
               << pos_to_str(1) << ") (parser_states " << listSexp(parserStates) << ")))";

        std::ostringstream deparser;
        deparser << "(DeparserModule " << pos_to_str(deparserId) << " "
                 << listSexp(deparserEmits) << ")";

        // parser -> transformer* -> deparser, a linear chain: a DAG with a
        // single sink and no fan-out or fan-in, which is what the semantics
        // assumes (is_linear_chain).  One module per guarded group, in program
        // order, because exactly one rule of a transformer fires and two
        // statements under different guards cannot share one.
        std::vector<std::string> mods{parser.str()};
        std::vector<std::string> edgeList;
        int prev = parserId;
        int nextId = deparserId + 1;
        for (const auto &grp : groups) {
            int id = nextId++;
            mods.push_back("(TransformerModule " + pos_to_str(id) + " Coq_nil Coq_nil " +
                           rulesOf(grp) + ")");
            edgeList.push_back("(" + pos_to_str(prev) + " " + pos_to_str(id) + ")");
            prev = id;
        }
        edgeList.push_back("(" + pos_to_str(prev) + " " + pos_to_str(deparserId) + ")");
        mods.push_back(deparser.str());

        coqOutput << "(GeneralCaracaraProgramDef " << inputLenBits() << " Coq_nil\n"
                  << " ((net_modules ";
        generateCoqListSexp(mods);
        coqOutput << ")\n  (net_edges (";
        for (size_t i = 0; i < edgeList.size(); ++i) {
            coqOutput << (i ? " " : "") << edgeList[i];
        }
        coqOutput << "))\n"
                  << "  (start_module " << pos_to_str(parserId) << ")))\n";
    }

    // Bits the parser may consume.  Phase 5 replaces this with the longest
    // parse path; the sum of every declared field is a safe over-estimate.
    int inputLenBits() const {
        int total = 0;
        for (const auto &f : fields) {
            if (f.onWire) total += f.width;
        }
        return total;
    }

    // The Header allocation, for debugging.  It is internal state, not part of
    // the emitted program: GeneralCaracaraProgramDef carries no header list,
    // since CrVarLike.collect_write_headers derives it from the network.
    void dumpFieldTable(std::ostream &os) const {
        auto row = [&](const FieldInfo &f) {
            os << ";   " << f.uid << "\t" << f.qualified << "\tbit<" << f.width
               << ">\t" << const_cast<CoqVisitor *>(this)->containerFor(f.width) << "\n";
        };
        os << "; " << fields.size() << " header fields allocated\n";
        for (const auto &f : fields) row(f);
        if (!temps.empty()) {
            os << "; " << temps.size() << " temporaries (not on the wire)\n";
            for (const auto &f : temps) row(f);
        }
    }

    std::string getCoqCode() const { return coqOutput.str(); }
};

}  // namespace P4::Rocq

int main(int argc, char *const argv[]) {
    P4::AutoCompileContext autoRocqContext(new P4::Rocq::RocqContext);
    auto &options = P4::Rocq::RocqContext::get().options();

    if (options.process(argc, argv) == nullptr) return EXIT_FAILURE;
    if (P4::errorCount() > 0) return EXIT_FAILURE;

    options.setInputFile();
    const P4::IR::P4Program *program = P4::parseP4File(options);

    if (program == nullptr || P4::errorCount() > 0) return EXIT_FAILURE;

    P4::FrontEnd fe;
    program = fe.run(options, program);
    if (program == nullptr) return EXIT_FAILURE;

    P4::ReferenceMap refMap;
    P4::TypeMap typeMap;
    program = program->apply(P4::Rocq::MidEnd(&refMap, &typeMap));
    if (program == nullptr || P4::errorCount() > 0) return EXIT_FAILURE;

    P4::Rocq::CoqVisitor coqVisitor(&typeMap);
    if (!options.tableEntries.empty() && !coqVisitor.loadTableEntries(options.tableEntries)) {
        return EXIT_FAILURE;
    }
    program->apply(coqVisitor);
    coqVisitor.finalize();  // Call finalize to generate the transformer definition

    coqVisitor.dumpFieldTable(std::cerr);

    // The program goes to stdout and nowhere else.  It used to also be written
    // to ./output.sexp, which drops an untracked file into whatever directory
    // the tool was run from.
    std::cout << coqVisitor.getCoqCode() << std::endl;

    return P4::errorCount() > 0 ? EXIT_FAILURE : EXIT_SUCCESS;
}