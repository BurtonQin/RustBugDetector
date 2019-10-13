#ifndef PRINTPASS_INTERDOUBLELOCKDETECTOR_H
#define PRINTPASS_INTERDOUBLELOCKDETECTOR_H

#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"

#include <set>

namespace detector {
    struct InterDoubleLockDetector : public llvm::ModulePass {

        static char ID;

        InterDoubleLockDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}

#endif //PRINTPASS_INTERDOUBLELOCKDETECTOR_H
