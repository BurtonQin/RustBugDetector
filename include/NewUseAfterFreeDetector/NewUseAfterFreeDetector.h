#ifndef RUSTBUGDETECTOR_NEWUSEAFTERFREEDETECTOR_H
#define RUSTBUGDETECTOR_NEWUSEAFTERFREEDETECTOR_H

#include "llvm/Pass.h"

namespace detector {
    struct NewUseAfterFreeDetector : public llvm::ModulePass {

        static char ID;

        NewUseAfterFreeDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //RUSTBUGDETECTOR_NEWUSEAFTERFREEDETECTOR_H
