#ifndef _ROCQS_OPTIONS_H_
#define _ROCQS_OPTIONS_H_

#include "frontends/common/options.h"
#include <string>

#include "frontends/common/parser_options.h"

namespace P4::Rocq {

class RocqOptions : public P4::CompilerOptions {
 public:
    virtual ~RocqOptions() = default;

    RocqOptions();
    RocqOptions(const RocqOptions &) = default;
    RocqOptions(RocqOptions &&) = delete;
    RocqOptions &operator=(const RocqOptions &) = default;
    RocqOptions &operator=(RocqOptions &&) = delete;

    bool useFixed = false;

    // Entries for tables the P4 source does not populate itself.  See
    // CoqVisitor::loadTableEntries for the format and for why they cannot
    // simply be left to the control plane.
    std::string tableEntries;

    // Proceed past a checksum control instead of refusing.  See the comment
    // where it is checked: the emitted packet then carries a stale checksum,
    // which is only sound when both programs a comparison is about are stubbed
    // the same way.
    bool stubChecksum = false;
};

using RocqContext = P4::P4CContextWithOptions<RocqOptions>;

}  // namespace P4::Rocq

#endif /* _ROCQS_OPTIONS_H_ */