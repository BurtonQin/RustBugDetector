#ifndef PRINTPASS_DOUBLELOCKDETECTOR_H
#define PRINTPASS_DOUBLELOCKDETECTOR_H

#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"

#include <set>

namespace detector {
    struct DoubleLockDetector : public llvm::ModulePass {

        static char ID;

        DoubleLockDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //PRINTPASS_DOUBLELOCKDETECTOR_H
