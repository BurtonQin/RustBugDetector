#ifndef RUSTBUGDETECTOR_DOUBLELOCKDETECTOR_H
#define RUSTBUGDETECTOR_DOUBLELOCKDETECTOR_H

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"

namespace detector {
    struct DoubleLockDetector : public llvm::ModulePass {

        static char ID;

        DoubleLockDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
        const llvm::DataLayout *pDL;
    };
}


#endif //RUSTBUGDETECTOR_DOUBLELOCKDETECTOR_H
