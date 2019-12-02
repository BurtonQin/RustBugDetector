#ifndef RUSTBUGDETECTOR_ATOMICCONTROLDEPDETECTOR_H
#define RUSTBUGDETECTOR_ATOMICCONTROLDEPDETECTOR_H

#include "llvm/Pass.h"

namespace detector {
    struct AtomicControlDepDetector : public llvm::ModulePass {

        static char ID;

        AtomicControlDepDetector();

        void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

        bool runOnModule(llvm::Module &M) override;

    private:

        llvm::Module *pModule;
    };
}


#endif //RUSTBUGDETECTOR_ATOMICCONTROLDEPDETECTOR_H
