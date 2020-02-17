#ifndef _TOZ3_OPTIONS_H_
#define _TOZ3_OPTIONS_H_

#include "ir/ir.h"

#include "frontends/common/options.h"
#include "lib/options.h"


namespace P4TOZ3 {

class toz3Options : public CompilerOptions {


public:
    toz3Options();
    // output file
    cstring o_file = nullptr;
    cstring p4_o_file = nullptr;
    // input file is in CompilerOptions file
    int flag_rd_remove = 0;
};

using P4toZ3Context = P4CContextWithOptions<toz3Options>;

} // namespace



#endif /* _TOZ3_OPTIONS_H_ */
