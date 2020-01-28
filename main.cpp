#include "frontends/common/applyOptionsPragmas.h"
#include "frontends/common/parseInput.h"
#include "frontends/common/resolveReferences/resolveReferences.h"
#include "frontends/p4/typeMap.h"
#include "frontends/p4/parseAnnotations.h"
#include "frontends/p4/validateParsedProgram.h"
#include "frontends/p4/createBuiltins.h"
#include "frontends/p4/directCalls.h"
#include "frontends/p4/frontend.h"
#include "frontends/p4/evaluator/evaluator.h"
#include "frontends/common/constantFolding.h"

#include "frontends/p4/fromv1.0/v1model.h"

#include "ir/ir.h"
#include "lib/error.h"
#include "lib/log.h"
#include "lib/gc.h"
#include "lib/nullstream.h"
#include "lib/exceptions.h"


#include "toz3Options.h"
#include "codegen.h"


#ifndef DEBUG
#define DEBUG 0
#endif


int main(int argc, char *const argv[]) {
    setup_gc_logging();

    AutoCompileContext autoP4toZ3Context(new P4TOZ3::P4toZ3Context);
    auto& options = P4TOZ3::P4toZ3Context::get().options();
    // we only handles P4_16 right now
    options.langVersion = CompilerOptions::FrontendVersion::P4_16;
    options.compilerVersion = "p4toz3 test";

    if (options.process(argc, argv) != nullptr) {
        options.setInputFile();
    }
    if (::errorCount() > 0)
        return 1;
    // check input and output file
    if (options.file==nullptr || options.o_file==nullptr) {
        options.usage();
        return 1;
    }
    auto ostream = openFile(options.o_file, false);
    if (ostream == nullptr) {
        ::error("must have --output [file]");
        return 1;
    }

    auto hook = options.getDebugHook();

    const IR::P4Program *program = nullptr;

    program = P4::parseP4File(options);

    // const IR::ToplevelBlock* toplevel = nullptr;
    // P4::ReferenceMap refMap;
    // P4::TypeMap typeMap;
    // P4::ParseAnnotations parseAnnotations;
    // P4V1::V1Model&      v1model = P4V1::V1Model::instance;

    // PassManager passes = {
    //     // Synthesize some built-in constructs
    //     new P4::CreateBuiltins(),
    //     new P4::ResolveReferences(&refMap, true),  // check shadowing
    //     // First pass of constant folding, before types are known --
    //     // may be needed to compute types.
    //     new P4::ConstantFolding(&refMap, nullptr),
    //     // Desugars direct parser and control applications
    //     // into instantiations followed by application
    //     new P4::InstantiateDirectCalls(&refMap),
    //     // Type checking and type inference.  Also inserts
    //     // explicit casts where implicit casts exist.
    //     new P4::ResolveReferences(&refMap),  // check shadowing
    //     new P4::TypeInference(&refMap, &typeMap, false),  // insert casts
    //     };

    // program = program->apply(passes);

    if (program != nullptr && ::errorCount() == 0) {
        try {
            P4::P4COptionPragmaParser optionsPragmaParser;
            program->apply(P4::ApplyOptionsPragmas(optionsPragmaParser));

            TOZ3::CodeGenToz3* cgt3 = new TOZ3::CodeGenToz3(1, ostream);
            program->apply(*cgt3);
        } catch (const Util::P4CExceptionBase &bug) {
            std::cerr << bug.what() << std::endl;
            return 1;
        }
    }

    return ::errorCount() > 0;
}