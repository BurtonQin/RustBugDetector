#ifndef RUSTBUGDETECTOR_NEWCELLIMDETECTOR_H
#define RUSTBUGDETECTOR_NEWCELLIMDETECTOR_H

#include "llvm/Pass.h"

namespace detector {
    struct NewCellIMDetector : public llvm::ModulePass {

        static char ID;

        NewCellIMDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //RUSTBUGDETECTOR_NEWCELLIMDETECTOR_H
