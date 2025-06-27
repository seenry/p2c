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
#include "test/gtest/helpers.h"

namespace P4::P4Dummy {

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

// Coq code generator class
class CoqGenerator : public Inspector {
    std::ostringstream coqOutput;
    std::vector<std::string> headers;
    std::vector<std::string> parserStates;
    std::vector<std::string> actions;
    std::vector<std::string> tables;
    std::string currentParser;
    std::map<std::string, std::vector<std::string>> parserStateDefs;

 public:
    CoqGenerator() {
        // Add standard Coq imports
        coqOutput << "From MyProject Require Export CrIdentifiers.\n";
        coqOutput << "From MyProject Require Export CrTransformer.\n";
        coqOutput << "Require Import Strings.String.\n";
        coqOutput << "Open Scope string_scope.\n";
        coqOutput << "Require Import ZArith.\n";
        coqOutput << "Require Import List.\n";
        coqOutput << "Import ListNotations.\n\n";
    }

    bool preorder(const IR::Type_Header *header) override {
        std::string headerName = header->name.name.c_str();
        headers.push_back(headerName);

        coqOutput << "(* Header definition: " << headerName << " *)\n";
        coqOutput << "Definition header_" << headerName << " : Header := HeaderCtr 1%positive.\n\n";

        return true;
    }

    // bool preorder(const IR::P4Parser* parser) override {
    //     currentParser = parser->name.name.c_str();
    //     coqOutput << "(* Parser " << currentParser << " *)\n";
    //     return true;
    // }

    // bool preorder(const IR::ParserState* state) override {
    //     std::string stateName = state->name.name.c_str();
    //     parserStates.push_back(stateName);

    //     coqOutput << "(* Parser State: " << stateName << " *)\n";
    //     coqOutput << "Definition " << stateName << "_state : ParserState := \"" << stateName <<
    //     "\".\n";

    //     // Collect state definition components
    //     std::vector<std::string> stateComponents;

    //     // TODO: Not working. Process statements in the state
    //     for (auto stmt : state->components) {
    //         if (auto methodCall = stmt->to<IR::MethodCallStatement>()) {
    //             if (auto member = methodCall->methodCall->method->to<IR::Member>()) {
    //                 if (member->member.name == "extract") {
    //                     // Handle extract operation
    //                     if (auto args = methodCall->methodCall->arguments) {
    //                         if (args->size() > 0) {
    //                             auto arg = (*args)[0];
    //                             if (auto pathExpr = arg->expression->to<IR::PathExpression>()) {
    //                                 std::string headerRef = pathExpr->path->name.name.c_str();
    //                                 // Extract the header name from the path (e.g., "hdr.h" ->
    //                                 "h") size_t dotPos = headerRef.find('.'); if (dotPos !=
    //                                 std::string::npos) {
    //                                     headerRef = headerRef.substr(dotPos + 1);
    //                                 }

    //                                 coqOutput << "Definition extract_" << headerRef << " :
    //                                 ExtractOp := \n"; coqOutput << "  ExtractOpConstructor
    //                                 header_" << headerRef << " 0 15. (* extract bits for header
    //                                 *)\n\n";

    //                                 stateComponents.push_back("extract_" + headerRef);
    //                             }
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //     }

    //     // Handle transitions
    //     if (state->selectExpression) {
    //         if (auto pathExpr = state->selectExpression->to<IR::PathExpression>()) {
    //             std::string targetState = pathExpr->path->name.name.c_str();
    //             coqOutput << "Definition " << stateName << "_to_" << targetState << " :
    //             Transition := \n"; coqOutput << "  Unconditional " << targetState <<
    //             "_state.\n\n";

    //             // Create parser state definition
    //             coqOutput << "Definition " << stateName << "_state_def : ParserStateDef := \n";
    //             coqOutput << "  ParserStateDefConstructor " << stateName << "_state ";
    //             if (!stateComponents.empty()) {
    //                 coqOutput << stateComponents[0] << " ";
    //             } else {
    //                 coqOutput << "NoOp ";
    //             }
    //             coqOutput << stateName << "_to_" << targetState << ".\n\n";
    //         }
    //     }

    //     return true;
    // }
    // Helper function to extract header name from field path

    bool preorder(const IR::P4Action *action) override {
        std::string actionName = action->name.name.c_str();
        actions.push_back(actionName);

        coqOutput << "(* Action: " << actionName << " *)\n";

        // Process action body
        for (auto stmt : action->body->components) {
            if (auto assign = stmt->to<IR::AssignmentStatement>()) {
                if (auto constant = assign->right->to<IR::Constant>()) {
                    int value = constant->asInt();

                    // Generate Coq assignment operation
                    coqOutput << "Definition " << actionName << "_op : HdrOp := \n";
                    coqOutput << "  StatelessOp AddOp (ConstantArg (repr " << value
                              << "%Z))  (ConstantArg (repr 0%Z)) header_" << headers.front()
                              << ".\n\n";
                }  // else if (auto add = assign->right->to<IR::Add>()) {
                   //  coqOutput << "Definition " << actionName << "_op : HdrOp := \n";
                   //  coqOutput << "  StatelessOp AddOp (ConstantArg (repr " << add.left << "%Z))
                   //  (ConstantArg (repr " << add.right << "%Z)) header_" << headerName << "\n\n";
                // }
            }
        }

        return true;
    }

    bool preorder(const IR::P4Table *table) override {
        std::string tableName = table->name.name.c_str();
        tables.push_back(tableName);

        coqOutput << "(* Table: " << tableName << " *)\n";

        // Generate match-action rule
        coqOutput << "Definition " << tableName << "_rule : MatchActionRule := \n";
        coqOutput << "  Seq (SeqCtr [(header_" << headers.front() << ", repr 0%Z)] [";  // Assuming match on first 8 bits

        // Add actions
        bool first = true;
        for (const auto &action : actions) {
            if (!first) coqOutput << "; ";
            coqOutput << action << "_op";
            first = false;
        }
        coqOutput << "]). (* Match and execute actions *)\n\n";

        return true;
    }

    // bool preorder(const IR::P4Control* control) override {
    //     std::string controlName = control->name.name.c_str();

    //     if (controlName == "ingress") {
    //         coqOutput << "(* Ingress control transformer *)\n";
    //         // Will be completed after processing tables and actions
    //     }

    //     return true;
    // }

    void finalize() {
        // TODO: This is mostly hardcoded stuff that hasn't been added to compiler logic yet.

        // Generate parser definition
        // coqOutput << "(* Parser definition *)\n";
        // coqOutput << "Definition p4_parser : Parser := [";
        // bool first = true;
        // for (const auto& state : parserStates) {
        //     if (state != "accept" && state != "reject") {
        //         if (!first) coqOutput << "; ";
        //         coqOutput << state << "_state";
        //         first = false;
        //     }
        // }
        // coqOutput << "].\n\n";

        // // Generate transformer definition
        // if (!tables.empty()) {
        //     coqOutput << "(* Transformer definition for ingress control *)\n";
        //     coqOutput << "Definition ingress_transformer : Transformer := [";
        //     first = true;
        //     for (const auto& table : tables) {
        //         if (!first) coqOutput << "; ";
        //         coqOutput << table << "_rule";
        //         first = false;
        //     }
        //     coqOutput << "].\n\n";
        // }

        // // Generate modules
        // coqOutput << "(* Module definitions *)\n";
        // coqOutput << "Definition parser_module : Module := \n";
        // coqOutput << "  ParserModule \"p\" p4_parser.\n\n";

        // if (!tables.empty()) {
        //     coqOutput << "Definition ingress_module : Module := \n";
        //     coqOutput << "  TransformerModule \"ingress\" ingress_transformer.\n\n";
        // }

        // // Generate scheduler
        // coqOutput << "(* Scheduler definition *)\n";
        // coqOutput << "Definition simple_scheduler_node : PNode := \n";
        // coqOutput << "  (header_H, 0, 15, [], fun x y => x + y). (* Simple scheduling function
        // *)\n\n"; coqOutput << "Definition p4_scheduler : Scheduler := \n"; coqOutput << "
        // PNodeCtr simple_scheduler_node.\n\n"; coqOutput << "Definition scheduler_module : Module
        // := \n"; coqOutput << "  SchedulerModule \"main_scheduler\" p4_scheduler.\n\n";

        // // Generate connections
        // coqOutput << "(* Connection definitions *)\n";
        // coqOutput << "Definition parser_to_ingress : Connection := \n";
        // coqOutput << "  ConnectionDef \"p\" \"ingress\" \"p_to_ingress\".\n\n";
        // coqOutput << "Definition ingress_to_scheduler : Connection := \n";
        // coqOutput << "  ConnectionDef \"ingress\" \"main_scheduler\"
        // \"ingress_to_scheduler\".\n\n";

        // // Generate complete program
        // coqOutput << "(* Complete Caracara program *)\n";
        // coqOutput << "Definition p4_caracara_program : CaracaraProgram := \n";
        // coqOutput << "  ([parser_module";
        // if (!tables.empty()) {
        //     coqOutput << "; ingress_module";
        // }
        // coqOutput << "; scheduler_module], \n";
        // coqOutput << "   [parser_to_ingress";
        // if (!tables.empty()) {
        //     coqOutput << "; ingress_to_scheduler";
        // }
        // coqOutput << "]).\n";
    }

    std::string getCoqCode() const { return coqOutput.str(); }
};

// Custom visitor that generates Coq code and provides parser debugging
class CoqVisitor : public Inspector {
    CoqGenerator *generator;

 public:
    CoqVisitor() : generator(new CoqGenerator()) {}

    ~CoqVisitor() { delete generator; }

    // bool preorder(const IR::P4Parser* parser) override {
    //     std::cout << "I am visiting parser " << parser->name.name << std::endl;
    //     return true;
    // }

    // bool preorder(const IR::ParserState* state) override {
    //     std::cout << "I am visiting parser state " << state->name.name << ":" << std::endl;
    //     // Print simplified state info similar to original ParserVisitor
    //     std::cout << "state " << state->name.name << " {" << std::endl;
    //     for (auto stmt : state->components) {
    //         if (auto methodCall = stmt->to<IR::MethodCallStatement>()) {
    //             if (auto member = methodCall->methodCall->method->to<IR::Member>()) {
    //                 if (member->member.name == "extract") {
    //                     std::cout << "  extract operation;" << std::endl;
    //                 }
    //             }
    //         }
    //     }
    //     if (state->selectExpression) {
    //         if (auto pathExpr = state->selectExpression->to<IR::PathExpression>()) {
    //             std::cout << "  " << pathExpr->path->name.name << ";" << std::endl;
    //         }
    //     }
    //     std::cout << " }" << std::endl;
    //     return true;
    // }

    bool preorder(const IR::P4Program *program) override {
        // First, do the parser debugging output
        // std::cout << "\n############################## PARSER DEBUG INFO
        // ##############################\n";

        // Visit all declarations for debugging
        for (auto decl : program->objects) {
            if (auto parser = decl->to<IR::P4Parser>()) {
                parser->apply(*this);
            }
        }

        // Now visit all declarations for Coq code generation
        // std::cout << "\n############################## GENERATING COQ CODE
        // ##############################\n";
        for (auto decl : program->objects) {
            decl->apply(*generator);
        }

        // Finalize the Coq code generation
        generator->finalize();

        // Output the generated Coq code
        // std::cout << "\n############################## GENERATED COQ CODE
        // ##############################\n";
        std::cout << generator->getCoqCode() << std::endl;

        // Optionally write to file
        std::ofstream coqFile("output.v");
        if (coqFile.is_open()) {
            coqFile << generator->getCoqCode();
            coqFile.close();
            std::cout << "\nCoq code written to output.v\n";
        }

        return false;  // Don't continue visiting
    }
};

}  // namespace P4::P4Dummy

int main(int argc, char *const argv[]) {
    P4::AutoCompileContext autoP4DummyContext(new P4::P4Dummy::P4DummyContext);
    auto &options = P4::P4Dummy::P4DummyContext::get().options();

    if (options.process(argc, argv) == nullptr) {
        return EXIT_FAILURE;
    }

    if (P4::errorCount() > 0) {
        return EXIT_FAILURE;
    }

    const P4::IR::P4Program *program = nullptr;
    options.setInputFile();
    program = P4::parseP4File(options);

    if (program == nullptr && P4::errorCount() != 0) {
        return EXIT_FAILURE;
    }

    // This compiler pass can print IR nodes.
    // auto top4 = P4::ToP4(&std::cout, false);

    // std::cout << "\n############################## INITIAL ##############################\n";
    // // Print the program before running front end passes.
    // program->apply(top4);

    // std::cout
    //     << "\n############################## AFTER FRONT END ##############################\n";
    // Apply the front end passes. These are usually fixed.
    P4::FrontEnd fe;
    program = fe.run(options, program);

    // Print the program after running front end passes.
    // program->apply(top4);

    // std::cout << "\n############################## AFTER MID END
    // ##############################\n"; Apply the mid end passes.
    program = program->apply(P4::P4Dummy::MidEnd());

    // Print the program after running front end passes.
    // program->apply(top4);

    // std::cout << "\n############################## CUSTOM VISITOR
    // ##############################\n"; Note: ParserVisitor functionality is now integrated into
    // CoqVisitor

    // std::cout << "\n############################## COQ GENERATION
    // ##############################\n"; Apply the new Coq generator visitor that also provides
    // parser debugging
    program->apply(P4::P4Dummy::CoqVisitor());

    return P4::errorCount() > 0 ? EXIT_FAILURE : EXIT_SUCCESS;
}