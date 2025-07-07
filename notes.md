# IR Analysis

## Printer
```cpp
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
```
## Additional Modifications
* `frontends/CMakeLists.txt`: included `pr/IRPrinter.h` @ line 90
* `frontends/p4/frontend.cpp`: added `#include "IRPrinter.h"` @ line 28
*  `frontends/p4/frontend.cpp`: added `new IRPrinter("Before ConstantFolding"),` @ line 174, 176