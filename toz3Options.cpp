#include "toz3Options.h"

namespace P4TOZ3 {


toz3Options::toz3Options() {
    registerOption("--output", "file",
                   [this](const char* arg) { o_file = arg; return true; },
                   "The translated Z3 file.");
    registerOption("--p4output", "p4file",
                   [this](const char* arg) { p4_o_file = arg; return true; },
                   "The p4 file after random remove.");
    registerOption("--flag_rd_remove", "flag",
                   [this](const char* arg) { flag_rd_remove = atoi(arg); return true; },
                   "The flag whether to use random remove.");
}

} // namespace
