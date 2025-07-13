#ifndef _ROCQS_OPTIONS_H_
#define _ROCQS_OPTIONS_H_

#include "frontends/common/options.h"
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
};

using RocqContext = P4::P4CContextWithOptions<RocqOptions>;

}  // namespace P4::Rocq

#endif /* _ROCQS_OPTIONS_H_ */