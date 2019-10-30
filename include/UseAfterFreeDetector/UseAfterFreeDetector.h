#ifndef RUSTBUGDETECTOR_USEAFTERFREEDETECTOR_H
#define RUSTBUGDETECTOR_USEAFTERFREEDETECTOR_H

#include "llvm/Pass.h"

namespace detector {
    struct UseAfterFreeDetector : public llvm::ModulePass {

        static char ID;

        UseAfterFreeDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //RUSTBUGDETECTOR_USEAFTERFREEDETECTOR_H
