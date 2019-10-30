#ifndef RUSTBUGDETECTOR_INVALIDFREEDETECTOR_H
#define RUSTBUGDETECTOR_INVALIDFREEDETECTOR_H

#include "llvm/Pass.h"

namespace detector {
    struct InvalidFreeDetector : public llvm::ModulePass {

        static char ID;

        InvalidFreeDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //RUSTBUGDETECTOR_INVALIDFREEDETECTOR_H
