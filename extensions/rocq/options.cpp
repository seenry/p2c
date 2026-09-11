#include "options.h"

namespace P4::Rocq {

RocqOptions::RocqOptions() : P4::CompilerOptions() {
    registerOption(
        "--use-fixed", nullptr,
        [this](const char *) {
            useFixed = true;
            return true;
        },
        "Instead of parsing a real P4 program manipulate and parse a dummy program.");
    registerOption(
        "--table-entries", "file",
        [this](const char *arg) {
            tableEntries = arg;
            return true;
        },
        "Entries for tables with no `const entries` of their own, one per line:\n"
        "  <table> <key>... -> <action> [<arg>...]\n"
        "A key is a number, v/n for an lpm prefix, v&&&m for ternary, or * for any.");
}
}