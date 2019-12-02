#ifndef RUSTBUGDETECTOR_SAMELOCKINSAMEFUNC_H
#define RUSTBUGDETECTOR_SAMELOCKINSAMEFUNC_H

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"

namespace detector {
    struct SameLockInSameFuncDetector : public llvm::ModulePass {

        static char ID;

        SameLockInSameFuncDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
        const llvm::DataLayout *pDL;
    };
}


#endif //RUSTBUGDETECTOR_SAMELOCKINSAMEFUNC_H
