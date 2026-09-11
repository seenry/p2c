#include "rocq_helpers.h"

namespace P4::Rocq {

// CrTypeIF.ml's positive/nat/Z converters emit decimal and accept either
// decimal or Coq's own encoding, so there is no reason to build a tower of
// Coq_xO/Coq_xI here -- it only makes the output unreadable.  See the
// "A network program can be read from a sexp now" note in ~/proj/ir/CLAUDE.md.
std::string pos_to_str(int x_) {
    // positive should never be zero
    if (x_ <= 0) { return "invalid"; }
    return std::to_string(x_);
}

std::string int_to_str(int x_) { return std::to_string(x_); }

// A [list bool] as the Coq_cons chain the .ir format uses.  There is no 0b
// shorthand: CrTypeIF.ml derives [coq_SelectCase]'s converters, so a bool list
// goes through the generic [Datatypes.list_of_sexp] and an atom like
// "0b00000001" is rejected as an unexpected variant constructor.  (A 0b sugar
// existed and was deliberately removed in ~/proj/ir 1a04afc, "remove bool list
// syntactic sugar", which also rewrote the fixtures to this form.)
//
// MSB FIRST -- CrParser.bits_to_Z folds the head in as the high bit -- and
// exactly [width] elements, because the list's LENGTH is what a SelectCase
// slice is compared against, so leading zeros are significant.  Width 0 is the
// empty list.
std::string bits_to_str(unsigned long long value, int width) {
    std::string s = "Coq_nil";
    // Wrapping from the LSB outwards puts bit [width-1] at the head, which is
    // what MSB-first means: each iteration pushes a more significant bit in
    // front of everything already built.
    for (int i = 0; i < width; ++i) {
        s = "(Coq_cons " + std::string(((value >> i) & 1ULL) ? "Coq_true" : "Coq_false") +
            " " + s + ")";
    }
    return s;
}

}  // namespace P4::Rocq
