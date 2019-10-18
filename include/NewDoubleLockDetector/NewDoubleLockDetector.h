#ifndef RUSTBUGDETECTOR_NEWDOUBLELOCKDETECTOR_H
#define RUSTBUGDETECTOR_NEWDOUBLELOCKDETECTOR_H

#include "llvm/Pass.h"

namespace detector {
    struct NewDoubleLockDetector : public llvm::ModulePass {

        static char ID;

        NewDoubleLockDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //RUSTBUGDETECTOR_NEWDOUBLELOCKDETECTOR_H
