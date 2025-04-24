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
## Getting started

### Installing P4C from source
1.  Clone the repository. It includes submodules, so be sure to use
    `--recursive` to pull them in:
    ```
    git clone --recursive https://github.com/p4lang/p4c.git
    ```
    If you forgot `--recursive`, you can update the submodules at any time using:
    ```
    git submodule update --init --recursive
    ```

2.  Most dependencies can be installed using `apt-get install`:
    ```bash
    sudo apt-get install cmake g++ git automake libtool libgc-dev bison flex \
    libfl-dev libboost-dev libboost-iostreams-dev \
    libboost-graph-dev llvm pkg-config python3 python3-pip \
    tcpdump

    pip3 install --user -r requirements.txt
    ```

3.  Build. Building should also take place in a subdirectory named `build`.
    ```
    mkdir build
    cd build
    cmake .. <optional arguments>
    make -j4
    make -j4 check
    ```

4.  Compile Program using:
    ```
    ./build/p4c --target bmv2 --arch v1model ~/rocq-notes/cir/coqsrc/simpl.p4 > ~/output
    ```