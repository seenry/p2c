#pragma once
#include "ir/ir.h"
#include "ir/visitor.h"

namespace P4 {

class IRPrinter : public Inspector {
public:
    explicit IRPrinter(const std::string& label) : label(label) {}
    
    bool preorder(const IR::Node* node) override {
        std::cout << "\n=== IR Dump: " << label << " ===\n";
        std::cout << node << std::endl;
        return false;
    }
    
private:
    std::string label;
};

}