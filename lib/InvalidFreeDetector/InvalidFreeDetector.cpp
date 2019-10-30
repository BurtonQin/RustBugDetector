#include "InvalidFreeDetector/InvalidFreeDetector.h"

#include <set>
#include <stack>

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

#include "Common/CallerFunc.h"

using namespace llvm;

namespace detector {

    char InvalidFreeDetector::ID = 0;

    InvalidFreeDetector::InvalidFreeDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializeAAResultsWrapperPassPass(Registry);
    }

    void InvalidFreeDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<AAResultsWrapperPass>();
    }

    static bool printDebugInfo(Instruction *I) {
        const llvm::DebugLoc &lockInfo = I->getDebugLoc();
        auto di = lockInfo.get();
        if (di) {
            errs() << " " << lockInfo->getDirectory() << '/'
                   << lockInfo->getFilename() << ' '
                   << lockInfo.getLine() << "\n";
            return true;
        }
        return false;
    }

    static std::set<StringRef> setUninitFuncName = {
            "_ZN4core3mem6zeroed",
            "_ZN4core3mem13uninitialized",
            "_ZN4core3mem12maybe_uninit20MaybeUninit$LT$T$GT$6zeroed",
            "_ZN4core3mem12maybe_uninit20MaybeUninit$LT$T$GT$6uninit"
//            "platform5alloc",
//            "process5alloc"
    };

    bool InvalidFreeDetector::runOnModule(Module &M) {
        this->pModule = &M;
        for (Function &F: M) {
            if (F.begin() == F.end()) {
                continue;
            }
//            errs() << "Caller:" << F.getName() << "\n";
            for (BasicBlock &B : F) {
                for (Instruction &I : B) {
                    if (isa<CallInst>(&I) || isa<InvokeInst>(&I)) {
                        CallSite CS(&I);
                        if (Value *CV = CS.getCalledValue()) {
                            if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
                                if (Callee->begin() != Callee->end()) {
//                                    errs() << Callee->getName() << "\n";
                                    for (StringRef UninitFuncName : setUninitFuncName) {
                                        if (Callee->getName().contains(UninitFuncName)) {
                                            errs() << F.getName() << "\n";
                                            errs() << "contains " << Callee->getName();
                                            errs() << "\n";
                                            printDebugInfo(&I);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        
        return false;
    }
}  // namespace detector

static RegisterPass<detector::InvalidFreeDetector> X(
        "detect",
        "Detect Invalid Free",
        false,
        true);


