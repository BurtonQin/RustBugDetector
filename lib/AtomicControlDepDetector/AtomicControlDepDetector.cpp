#include "AtomicControlDepDetector/AtomicControlDepDetector.h"

#include <fstream>
#include <string>
#include <set>
#include <stack>
#include <CFG/CFG.h>

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/Analysis/PostDominators.h"

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "AtomicControlDepDetector"

using namespace llvm;

namespace detector {

    char AtomicControlDepDetector::ID = 0;

    AtomicControlDepDetector::AtomicControlDepDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializePostDominatorTreeWrapperPassPass(Registry);
        initializeDominatorTreeWrapperPassPass(Registry);
        initializeAAResultsWrapperPassPass(Registry);
    }

    void AtomicControlDepDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<PostDominatorTreeWrapperPass>();
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<AAResultsWrapperPass>();
    }

    static bool isSkipInst(Instruction *I) {
        if (!I) {
            return true;
        }
        if (isa<PHINode>(I)) {
            return true;
        }
        if (isa<DbgInfoIntrinsic>(I)) {
            return true;
        }
        return false;
    }


    static bool isAtomicAPI(Function *F) {
        return F->getName().startswith("_ZN4core4sync6atomic");
    }

    static bool isAtomicRead(Function *F) {
        return F->getName().contains("load17h");
    }

    static bool isAtomicWrite(Function *F) {
        return F->getName().contains("store17h");
    }

    static bool isAtomicReadWrite(Function *F) {
        return F->getName().contains("compare_and_swap17h") ||
                F->getName().contains("compare_exchange17h") ||
                F->getName().contains("compare_exchange_weak17h") ||
                F->getName().contains("fetch_add17h") ||
                F->getName().contains("fetch_and17h") ||
                F->getName().contains("fetch_max17h") ||
                F->getName().contains("fetch_min17h") ||
                F->getName().contains("fetch_nand17h") ||
                F->getName().contains("fetch_or17h") ||
                F->getName().contains("fetch_sub17h") ||
                F->getName().contains("fetch_update17h") ||
                F->getName().contains("fetch_xor17h");
    }

    static bool isPanic(Function *F) {
        return F->getName().startswith("_ZN3std9panicking15begin_panic");
    }

    static bool printDebugInfo(Instruction *I) {
        if (isSkipInst(I)) {
            return false;
        }
        const llvm::DebugLoc &lockInfo = I->getDebugLoc();
//        I->print(errs());
//        errs() << "\n";
        auto di = lockInfo.get();
        if (di) {
            errs() << " " << lockInfo->getDirectory() << '/'
                   << lockInfo->getFilename() << ' '
                   << lockInfo.getLine() << "\n";
            return true;
        } else {
            return false;
        }
    }

    static void printDebugInfo(Function *F) {
        if (!F || F->begin() == F->end()) {
            return;
        }
        Instruction *I = F->getEntryBlock().getFirstNonPHIOrDbgOrLifetime();
        while (I && !printDebugInfo(I)) {
            I = I->getNextNode();
        }
    }

    bool AtomicControlDepDetector::runOnModule(Module &M) {

        std::set<Function *> setAtomicReadFunc;
        std::set<Function *> setAtomicWriteFunc;
        std::set<Function *> setAtomicReadWriteFunc;
        std::set<Function *> setAtomicFunc;
        std::set<Function *> setPanicFunc;
        for (Function &F : M) {
            if (isAtomicAPI(&F)) {
                if (isAtomicRead(&F)) {
                    setAtomicReadFunc.insert(&F);
                    setAtomicFunc.insert(&F);
                } else if (isAtomicWrite(&F)) {
                    setAtomicWriteFunc.insert(&F);
                    setAtomicFunc.insert(&F);
                } else if (isAtomicReadWrite(&F)) {
                    setAtomicReadWriteFunc.insert(&F);
                    setAtomicFunc.insert(&F);
//                    setAtomicReadFunc.insert(&F);
//                    setAtomicWriteFunc.insert(&F);
                }
            } else if (isPanic(&F)) {
                setPanicFunc.insert(&F);
            }
        }

        std::map<Function *, std::set<Instruction *>> mapCalleeCallSites;
        for (Function &F : M) {
            if (F.begin() == F.end()) {
                continue;
            }
            for (BasicBlock &B : F) {
                for (Instruction &I : B) {
                    if (isSkipInst(&I)) {
                        continue;
                    }
                    if (!isCallOrInvokeInst(&I)) {
                        continue;
                    }
                    CallSite CS(&I);
                    Function *Callee = CS.getCalledFunction();
                    if (!Callee) {
                        continue;
                    }
                    mapCalleeCallSites[Callee].insert(&I);
                }
            }
        }

        std::set<Instruction *> setAtomicReadCallInst;
        std::set<Instruction *> setAtomicWriteCallInst;
        std::set<Instruction *> setAtomicReadWriteCallInst;
        std::set<Instruction *> setAtomicCallInst;
        std::set<Instruction *> setPanicInst;
        for (auto &kv : mapCalleeCallSites) {
            if (setAtomicFunc.find(kv.first) != setAtomicFunc.end()) {
                setAtomicCallInst.insert(kv.second.begin(), kv.second.end());
            }
            if (setAtomicReadFunc.find(kv.first) != setAtomicReadFunc.end()) {
                setAtomicReadCallInst.insert(kv.second.begin(), kv.second.end());
            } else if (setAtomicWriteFunc.find(kv.first) != setAtomicWriteFunc.end()) {
                setAtomicWriteCallInst.insert(kv.second.begin(), kv.second.end());
            } else if (setAtomicReadWriteFunc.find(kv.first) != setAtomicReadWriteFunc.end()) {
                setAtomicReadWriteCallInst.insert(kv.second.begin(), kv.second.end());
            } else if (setPanicFunc.find(kv.first) != setPanicFunc.end()) {
                setPanicInst.insert(kv.second.begin(), kv.second.end());
            }
        }

        std::map<Function *, std::set<Instruction *>> mapCallerAtomicRead;
        for (Instruction *AtomicReadCallInst : setAtomicReadCallInst) {
            mapCallerAtomicRead[AtomicReadCallInst->getFunction()].insert(AtomicReadCallInst);
        }

        std::map<Function *, std::set<Instruction *>> mapCallerAtomicWrite;
        for (Instruction *AtomicWriteCallInst : setAtomicWriteCallInst) {
            mapCallerAtomicWrite[AtomicWriteCallInst->getFunction()].insert(AtomicWriteCallInst);
        }

        std::map<Function *, std::set<Instruction *>> mapCallerAtomicReadWrite;
        for (Instruction *AtomicReadWriteCallInst : setAtomicReadWriteCallInst) {
            mapCallerAtomicReadWrite[AtomicReadWriteCallInst->getFunction()].insert(AtomicReadWriteCallInst);
        }

        std::map<Function *, std::set<Instruction *>> mapCallerPanic;
        for (Instruction *PanicInst : setPanicInst) {
            mapCallerPanic[PanicInst->getFunction()].insert(PanicInst);
        }

        std::map<Function *, std::set<Instruction *>> mapCallerAtomic;
        for (Instruction *AtomicCallInst : setAtomicCallInst) {
            mapCallerAtomic[AtomicCallInst->getFunction()].insert(AtomicCallInst);
        }

#define COUNT 1
#ifdef COUNT
        std::map<Function *, std::map<Instruction *, Function *>> mapCallerAtomicCallSites;
        for (auto &kv : mapCallerAtomic) {
            for (Instruction *AtomicCallInst : kv.second) {
                mapCallerAtomicCallSites[AtomicCallInst->getFunction()][AtomicCallInst] = kv.first;
            }
        }
//        errs() << "# of Func Containing Atomic\n";
//        for (auto &kv : mapCallerAtomicCallSites) {
//            if (!kv.second.empty()) {
//                printDebugInfo(kv.first);
//            }
//        }
        errs() << "# of Func Containing Two Atomic\n";
        for (auto &kv : mapCallerAtomicCallSites) {
            if (kv.second.size() >= 2) {
                printDebugInfo(kv.first);
            }
        }
#else
        for (auto &kv : mapCallerAtomicRead) {
            if (mapCallerAtomicWrite.find(kv.first) == mapCallerAtomicWrite.end()) {
                continue;
            }
            DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>(*kv.first).getDomTree();
            PostDominatorTree *PDT = &getAnalysis<PostDominatorTreeWrapperPass>(*kv.first).getPostDomTree();
            ControlDependenceGraphBase CDG;
            CDG.graphForFunction(*kv.first, *PDT);
            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(*kv.first).getAAResults();
            for (Instruction *AtomicReadInst : kv.second) {
                for (Instruction *AtomicWriteInst : mapCallerAtomicWrite[kv.first]) {
                    // if the first arg aliases and the read'users control write
                    if (AA.alias(AtomicReadInst->getOperand(0), AtomicWriteInst->getOperand(0)) != MustAlias) {
                        continue;
                    }
                    bool Influenced = false;
                    for (User *U : AtomicReadInst->users()) {
                        if (Instruction *UI = dyn_cast<Instruction>(U)) {
                            BasicBlock *AtomicReadUserBB = UI->getParent();
                            BasicBlock *AtomicWriteBB = AtomicWriteInst->getParent();
                            if (CDG.influences(AtomicReadUserBB, AtomicWriteBB)) {
                                bool IsPanic = false;
                                if (mapCallerPanic.find(kv.first) != mapCallerPanic.end()) {
                                    for (Instruction *PanicInst : mapCallerPanic[kv.first]) {
                                        if (CDG.influences(AtomicReadUserBB, PanicInst->getParent())) {
                                            IsPanic = true;
                                            break;
                                        }
                                    }
                                }
                                if (IsPanic) {
                                    continue;
                                }
                                if (mapCallerAtomicReadWrite.find(kv.first) == mapCallerAtomicReadWrite.end()) {
                                    Influenced = true;
                                    break;
                                } else {
                                    bool RWDom = false;
                                    for (Instruction *AtomicRWInst : mapCallerAtomicReadWrite[kv.first]) {
                                        if (DT->dominates(AtomicRWInst, AtomicWriteInst)) {
                                            RWDom = true;
                                            break;
                                        }
                                    }
                                    if (!RWDom) {
                                        Influenced = true;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    if (Influenced) {
                        errs() << "AtomicReadInst controls AtomicWriteInst" << "\n";
                        AtomicReadInst->print(errs());
                        errs() << "\n";
                        AtomicWriteInst->print(errs());
                        errs() << "\n";
                        printDebugInfo(AtomicReadInst);
                        printDebugInfo(AtomicWriteInst);
                    }
                }
            }

        }
#endif
        return false;
    }

}  // namespace detector


static RegisterPass<detector::AtomicControlDepDetector> X(
        "detect",
        "Detect Atomic Interior Mutability",
        false,
        true);
