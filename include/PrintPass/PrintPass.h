#ifndef PRINTPASS_PRINTPASS_H
#define PRINTPASS_PRINTPASS_H

#include "llvm/Pass.h"

namespace printpass {
    struct PrintPass : public llvm::ModulePass {

        static char ID;

        PrintPass();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

        void printCallChain();

    private:

        llvm::Module *pModule;
    };
}

#endif //PRINTPASS_PRINTPASS_H