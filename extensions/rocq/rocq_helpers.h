#ifndef _ROCQ_HELPERS_H_
#define _ROCQ_HELPERS_H_

#include <string>

namespace P4::Rocq {
    std::string pos_to_str(int x_); // for integers of type %positive
    std::string int_to_str(int x_); // for integers of type %Z
}

#endif
