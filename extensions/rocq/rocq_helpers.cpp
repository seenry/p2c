#include "rocq_helpers.h"

namespace P4::Rocq {

std::string pos_to_str(int x_) {
    // positive should never be zero
    if (x_ == 0) { return "invalid"; }

    std::string rocq_str = "Coq_xH";
    if (x_ == 1) { return rocq_str; }

    // find leading bit
    int bit_idx = (sizeof(x_) * 8) - 1;
    while (((x_ >> bit_idx) & 0x1) == 0x0) { bit_idx--; }

    // fill in bit string
    bit_idx--; // safe because x_ > 1
    do {
        if (((x_ >> bit_idx) & 0x1) == 0x0) {
            rocq_str = "(Coq_xO " + rocq_str + ")";
        } else /* ... == 0x1 */ {
            rocq_str = "(Coq_xI " + rocq_str + ")";
        }
    } while (bit_idx-- != 0);

    return rocq_str;
}

std::string int_to_str(int x_) {
    if (x_ == 0) { return "Z0"; }

    if (x_ < 0) {
        // works even if x_ = min e.g. (-8=0b1000 -> Zneg 0b1000)
        return "(Zneg " + pos_to_str(-x_) + ")";
    } /* else if (x_ > 0) {*/
        return "(Zpos " + pos_to_str( x_) + ")";
    // }
}

}
