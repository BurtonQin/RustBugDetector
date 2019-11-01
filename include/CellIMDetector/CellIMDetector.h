#ifndef RUSTBUGDETECTOR_CELLIMDETECTOR_H
#define RUSTBUGDETECTOR_CELLIMDETECTOR_H

#include "llvm/Pass.h"

namespace detector {
    struct CellIMDetector : public llvm::ModulePass {

        static char ID;

        CellIMDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //RUSTBUGDETECTOR_CELLIMDETECTOR_H
