#ifndef RUSTBUGDETECTOR_PRINTLOCK_H
#define RUSTBUGDETECTOR_PRINTLOCK_H

#include "llvm/Pass.h"

namespace detector {

    struct PrintLock : llvm::ModulePass {

        static char ID;

        PrintLock();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}


#endif //RUSTBUGDETECTOR_PRINTLOCK_H
