#include <fstream>
#include <iostream>
#include <map>
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

class MidEnd : public PassManager {
    P4::ReferenceMap refMap;
    P4::TypeMap typeMap;

 public:
    MidEnd() {
        addPasses({
            new P4::TypeChecking(&refMap, &typeMap, true),
            new P4::ConstantFolding(&typeMap),
        });
    }
};

class CoqVisitor : public Inspector {
    std::ostringstream coqOutput;
    // Map P4 field names (e.g., "a") to Coq identifiers (e.g., "h_a")
    std::map<std::string, std::string> headerFieldToCoqIdent;
    std::vector<std::string> actions;
    std::vector<std::string> tables;
    int header_uid = 1;  // For generating unique HeaderCtr IDs
    std::map<cstring, int> fieldToUID;

 public:
    CoqVisitor() {
        coqOutput << "(CaracaraProgramDef ";
    }
    ~CoqVisitor() {}


    /*
    Responsible for the part immediately after (CaracaraProgramDef
    e.g.,
    (Coq_cons Coq_xH Coq_nil)
    Coq_nil
    Coq_nil

    We consider every header field a seperate header and only support one of them.
    */
    bool preorder(const IR::Type_Header *header) override {
        for (auto field : header->fields) {
            fieldToUID[field->name] = header_uid;
            coqOutput << "(Coq_cons " + pos_to_str(header_uid) + " Coq_nil)";
            header_uid++;
        }

        coqOutput << "\n Coq_nil \n Coq_nil\n";
        return true;
    }

    // We return Coq_xH since only one header is supported.
    std::string resolveHeaderField(const IR::Expression *expr) {
        return pos_to_str(header_uid - 1); 
    }

    // Helper method to process an expression and get its Rocq FunctionArgument representation.
    std::string processExpressionAsArg(const IR::Expression *expr) {
        if (expr->to<IR::Member>()) {
            // header field: hdr.h.a
            std::string coqIdent = resolveHeaderField(expr);
            return "(HeaderArg " + coqIdent + ")";
        } else if (auto constant = expr->to<IR::Constant>()) {
            // Constant value
            return "(ConstantArg " + int_to_str(constant->asInt()) + ")\n";
        }
        // Else fail
        error("Unsupported expression type for action argument: %s", expr->toString().c_str());
        return nullptr;  // Fallback
    }

    // Converts P4 operation types to a string representing the COQ operation type
    std::string p4OpToCoqOp(const IR::Operation_Binary *binOp) {
        if (binOp->is<IR::Add>()) return "AddOp";
        if (binOp->is<IR::Sub>()) return "SubOp";
        // if (binOp->is<IR::BAnd>()) return "AndOp";
        // if (binOp->is<IR::BOr>()) return "OrOp";
        // if (binOp->is<IR::BXor>()) return "XorOp";
        // if (binOp->is<IR::Mul>()) return "MulOp";
        // if (binOp->is<IR::Div>()) return "DivOp";
        // if (binOp->is<IR::Mod>()) return "ModOp";

        error("Unsupported binary operation: %s", binOp->toString());
        return "(* unsupported_op *)";
    }

    void processAssignment(const IR::AssignmentStatement *assign, const std::string &actionName) {
        // Resolve the left-hand side (the target of the assignment)
        std::string targetIdent = resolveHeaderField(assign->left);

        // Check if the right-hand side is a binary operation (e.g., a + b). -= is expanded prior to
        // this pass
        if (auto binOp = assign->right->to<IR::Operation_Binary>()) {
            std::string coqOp = p4OpToCoqOp(binOp);
            std::string leftArg = processExpressionAsArg(binOp->left);
            std::string rightArg = processExpressionAsArg(binOp->right);

            coqOutput << "  StatelessOp " << coqOp << " " << leftArg << " " << rightArg << " "
                      << targetIdent << ")\n\n";

        } else if (assign->right->is<IR::Member>() || assign->right->is<IR::Constant>()) {
            // Handle simple assignments (e.g., b = a; or b = 1;) by modeling them as `b = a + 0`
            std::string sourceArg = processExpressionAsArg(assign->right); // This is constantArg a which will be added to 0 below.
            coqOutput << "  StatelessOp AddOp " << sourceArg
                      << " (ConstantArg " + int_to_str(0) + ") \n" << targetIdent << ")\n\n";
        } else {
            error("Unsupported expression on right side of assignment: %s",
                assign->right->toString().c_str());
        }
    }

    bool preorder(const IR::P4Action *action) override {
        std::string actionName = action->name.name.c_str();
        actions.push_back(actionName);

        for (auto stmt : action->body->components) {
            // Start the Coq action definition
            coqOutput << "(Coq_cons (Seq ( SeqCtr Coq_nil (Coq_cons (";
            if (auto assign = stmt->to<IR::AssignmentStatement>()) {
                // Handle assignment statements
                processAssignment(assign, actionName);
                coqOutput << "Coq_nil))) \n";

            } else {  // Else in case we haven't implemented.
                error("Unsupported statement type in action %s: %s", actionName.c_str(),
                    stmt->toString().c_str());
            }
        }
        return true;
    }

    bool preorder(const IR::P4Table *table) override { return true; }

    void finalize() { coqOutput << "Coq_nil))"; }

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

    program = program->apply(P4::Rocq::MidEnd());

    P4::Rocq::CoqVisitor coqVisitor;
    program->apply(coqVisitor);
    coqVisitor.finalize();  // Call finalize to generate the transformer definition

    std::string generatedCode = coqVisitor.getCoqCode();
    std::cout << generatedCode << std::endl;

    std::ofstream coqFile("output.sexp");
    if (coqFile.is_open()) {
        coqFile << generatedCode;
        coqFile.close();
    }

    return P4::errorCount() > 0 ? EXIT_FAILURE : EXIT_SUCCESS;
}