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
    CoqVisitor() { coqOutput << "(CaracaraProgramDef "; }
    ~CoqVisitor() {}

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

bool preorder(const IR::Type_Header *header) override {
    // vector to print out list
    std::vector<std::string> list_elements;

    for (auto field : header->fields) {
        // Map the header to the current UID
        fieldToUID[field->name] = header_uid; 

        // Convert the UID to the Coq string format
        std::string element_str = pos_to_str(header_uid);

        list_elements.push_back(element_str);
        
        // Increment the UID for the next field
        header_uid++;
    }
    
    // print list of headers
    generateCoqListSexp(list_elements);
    coqOutput << "\n Coq_nil \n Coq_nil\n"; 
    
    return true;
}

    // We resolve the header field expression by looking up its name
    // in the map populated by the preorder visitor.
    std::string resolveHeaderField(const IR::Expression *expr) {
        cstring fieldName;

        // HAPPY CASE The expression is most likely a Member access (e.g., "hdr.my_field")
        if (auto member = expr->to<IR::Member>()) {
            fieldName = member->member;
            // error("1resolveHeaderField: Found Member expression with field name %1%", fieldName);
        }
        // LEFT FOR LATER It could also be a PathExpression (e.g., just "my_field")
        else if (auto path = expr->to<IR::PathExpression>()) {
            fieldName = path->path->name;
            error("2resolveHeaderField: Found PathExpression with field name %1%", fieldName);
        }
        // Handle other cases or throw an error
        else {
            error("resolveHeaderField: Unexpected expression type %1%", expr);
            // Return a default/error value
            return "Coq_nil";
        }

        // Look up the field name
        auto it = fieldToUID.find(fieldName);
        if (it != fieldToUID.end()) {
            // Get the UID.
            unsigned uid = it->second;
            // Convert the UID to the Coq string format
            return pos_to_str(uid);

        } else {
            // Field was not found in the map
            error("resolveHeaderField: Could not find UID for field %1%", fieldName);
            // Return a default/error value
            return "Coq_nil";
        }
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
        if (binOp->is<IR::BAnd>()) return "AndOp";
        if (binOp->is<IR::BOr>()) return "OrOp";
        if (binOp->is<IR::BXor>()) return "XorOp";
        if (binOp->is<IR::Mul>()) return "MulOp";
        if (binOp->is<IR::Div>()) return "DivOp";
        if (binOp->is<IR::Mod>()) return "ModOp";

        error("Unsupported binary operation: %s", binOp->toString());
        return "(* unsupported_op *)";
    }

// Takes an assignment statement and generates the corresponding Coq S-expression string.
std::string generateCoqAssignmentSexp(const IR::AssignmentStatement *assign, const std::string &actionName) {
    std::string targetIdent = resolveHeaderField(assign->left);
    std::stringstream ss; // Use a stringstream to build the output string

    // Check if the right-hand side is a binary operation (e.g., a + b).
    if (auto binOp = assign->right->to<IR::Operation_Binary>()) {
        std::string coqOp = p4OpToCoqOp(binOp);
        std::string leftArg = processExpressionAsArg(binOp->left);
        std::string rightArg = processExpressionAsArg(binOp->right);

        ss << "  (StatelessOp " << coqOp << " " << leftArg << " " << rightArg << " "
           << targetIdent << ")\n";

    } else if (assign->right->is<IR::Member>() || assign->right->is<IR::Constant>()) {
        // Handle simple assignments (e.g., b = a; or b = 1;)
        std::string sourceArg = processExpressionAsArg(assign->right);

        ss << "  (StatelessOp AddOp " << sourceArg
           << " (ConstantArg " + int_to_str(0) + ")) \n"
           << targetIdent;

    } else {
        error("Unsupported expression on right side of assignment: %s \t %s",
              assign->right->toString().c_str(), resolveHeaderField(assign->right).c_str());
    }
    
    return ss.str();
}

// Actions
bool preorder(const IR::P4Action *action) override {
    std::string actionName = action->name.name.c_str();
    actions.push_back(actionName);
    
    std::vector<std::string> operations_for_list; 
    coqOutput << "(Coq_cons (Seq ( SeqCtr Coq_nil ";
    // Iterate through statements to collect the Coq strings
    for (auto stmt : action->body->components) {
        if (auto assign = stmt->to<IR::AssignmentStatement>()) {

            std::string coq_assignment_string = generateCoqAssignmentSexp(assign, actionName);
            operations_for_list.push_back(coq_assignment_string);
            
        } else {
            error("Unsupported statement type in action %s: %s", actionName.c_str(),
                  stmt->toString().c_str());
        }
    }
    
    generateCoqListSexp(operations_for_list);
    coqOutput << "))Coq_nil) \n";
    return true;
}

    bool preorder(const IR::P4Table *table) override { error("Tables are not supported");return true; }

    void finalize() { coqOutput << ")"; }

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