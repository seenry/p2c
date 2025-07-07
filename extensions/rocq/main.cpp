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
        coqOutput << "From MyProject Require Import SmtExpr.\n";
        coqOutput << "From MyProject Require Import SmtQuery.\n";
        coqOutput << "From MyProject Require Import CrTransformer.\n";
        coqOutput << "From MyProject Require Import CrSymbolicSemantics.\n";
        coqOutput << "From MyProject Require Import CrConcreteSemantics.\n";
        coqOutput << "From MyProject Require Import ConcreteToSymbolicLemmas.\n";
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

        // Generate Seq Rule
        coqOutput << "Definition " << tableName << "_seq_rule : SeqRule := \n";
        coqOutput << "  SeqCtr [(header_" << headers.front() << ", repr 0%Z)] [";

        // Add actions
        bool first = true;
        for (const auto &action : actions) {
            if (!first) coqOutput << "; ";
            coqOutput << action << "_op";
            first = false;
        }
        coqOutput << "]. \n\n";

        // Generate match-action rule
        coqOutput << "Definition " << tableName << "_rule : MatchActionRule := \n";
        coqOutput << "  Seq " << tableName << "_seq_rule.\n\n";  // Assuming match on first 8 bits

        return true;
    }

    void finalize() {
        // TODO: This is mostly hardcoded stuff that hasn't been added to compiler logic yet.

        coqOutput << "(* THE SIMPLEST POSSIBLE ProgramState SmtArithExpr *)\n";
        coqOutput << "Definition simplest_state : ProgramState SmtArithExpr := {|\n";
        coqOutput << "ctrl_plane_map := fun _ => SmtConst (repr 0%Z);\n";
        coqOutput << "header_map := fun _ => SmtConst (repr 0%Z);\n";
        coqOutput << "state_var_map := fun _ => SmtConst (repr 0%Z)\n";
        coqOutput << "|}.\n\n";

        coqOutput << "Definition headers_to_check : list Header := [header_" << headers.front()
                  << "].\n";
        coqOutput << "Definition state_vars_to_check : list StateVar := [].\n";

        coqOutput << "(* Construct the equivalence checker instance *)\n";
        coqOutput << "Definition my_equivalence_check : option SmtValuation :=\n";
        coqOutput << "  equivalence_checker\n";
        coqOutput << "      simplest_state       (* Starting symbolic state *)\n";
        coqOutput << "      " <<tables.front() << "_seq_rule          (* First rule *)\n";
        coqOutput << "      " <<tables.front() << "_seq_rule          (* Second rule (same) *)\n";
        coqOutput << "      headers_to_check             \n";
        coqOutput << "      state_vars_to_check.         \n";

        coqOutput << "Eval compute in my_equivalence_check.\n";
    }

    std::string getCoqCode() const { return coqOutput.str(); }
};

// Custom visitor that generates Coq code and provides parser debugging
class CoqVisitor : public Inspector {
    CoqGenerator *generator;

 public:
    CoqVisitor() : generator(new CoqGenerator()) {}

    ~CoqVisitor() { delete generator; }


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