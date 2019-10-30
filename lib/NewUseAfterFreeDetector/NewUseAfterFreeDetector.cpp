#include "NewUseAfterFreeDetector/NewUseAfterFreeDetector.h"

#include <set>
#include <stack>

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/TypeName.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Argument.h"

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "UseAfterFreeDetector"

using namespace llvm;

namespace detector {

    char NewUseAfterFreeDetector::ID = 0;

    NewUseAfterFreeDetector::NewUseAfterFreeDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializeDominatorTreeWrapperPassPass(Registry);
        initializePostDominatorTreeWrapperPassPass(Registry);
        initializeAAResultsWrapperPassPass(Registry);
        initializeLoopSimplifyPass(Registry);
        initializeLoopInfoWrapperPassPass(Registry);
    }

    void NewUseAfterFreeDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<PostDominatorTreeWrapperPass>();
        AU.addRequired<AAResultsWrapperPass>();
        AU.addRequired<LoopInfoWrapperPass>();
    }

    std::set<Loop *> LoopSet; /*Set storing loop and subloop */

    void getSubLoopSet(Loop *lp) {

        std::vector<Loop *> workList;
        if (lp != NULL) {
            workList.push_back(lp);
        }

        while (workList.size() != 0) {

            Loop *loop = workList.back();
            LoopSet.insert(loop);
            workList.pop_back();

            if (loop != nullptr && !loop->empty()) {

                std::vector<Loop *> &subloopVect = lp->getSubLoopsVector();
                if (subloopVect.size() != 0) {
                    for (std::vector<Loop *>::const_iterator SI = subloopVect.begin(); SI != subloopVect.end(); SI++) {
                        if (*SI != NULL) {
                            if (LoopSet.find(*SI) == LoopSet.end()) {
                                workList.push_back(*SI);
                            }
                        }
                    }

                }
            }
        }
    }

    void getLoopSet(Loop *lp) {
        if (lp != NULL && lp->getHeader() != NULL && !lp->empty()) {
            LoopSet.insert(lp);
            const std::vector<Loop *> &subloopVect = lp->getSubLoops();
            if (!subloopVect.empty()) {
                for (std::vector<Loop *>::const_iterator subli = subloopVect.begin(); subli != subloopVect.end(); subli++) {
                    Loop *subloop = *subli;
                    getLoopSet(subloop);
                }
            }
        }
    }

    static bool isStoreToGlobal(Instruction *UseInst) {
        if (StoreInst *SI = dyn_cast<StoreInst>(UseInst)) {
            if (GEPOperator *GEP = dyn_cast<GEPOperator>(SI->getPointerOperand())) {
                return isa<GlobalVariable>(GEP->getOperand(0)->stripPointerCasts());
            }
            return isa<GlobalVariable>(UseInst->getOperand(0)->stripPointerCasts());
        }
        return false;
    }

    static bool isOperandOfFunction(Instruction *UseInst) {
        return isa<CallInst>(UseInst) || isa<InvokeInst>(UseInst);
    }

    static bool isReachableInBB(Instruction *Src, Instruction *Dest) {
        if (Src && Dest && Src != Dest && Src->getParent() == Dest->getParent()) {
            Instruction *Curr = Src;
            while (Curr) {
                if (Curr == Dest) {
                    return true;
                }
                Curr = Curr->getNextNonDebugInstruction();
            }
            return false;
        }
        return false;
    }

    static bool isReachableAcrossBB(Instruction *Src, Instruction *Dest, std::set<BasicBlock *> &setBackEdge) {
        if (Src && Dest) {
            BasicBlock *SrcBB = Src->getParent();
            BasicBlock *DestBB = Dest->getParent();
            std::map<BasicBlock *, BasicBlock *> mapToParentBB;
            if (SrcBB != DestBB) {
                std::stack<BasicBlock *> WorkList;
                std::set<BasicBlock *> Visited;
                WorkList.push(SrcBB);
                Visited.insert(SrcBB);
                while (!WorkList.empty()) {
                    BasicBlock *Curr = WorkList.top();
                    WorkList.pop();
                    if (setBackEdge.find(Curr) != setBackEdge.end()) {
                        continue;
                    }
                    if (Curr == DestBB) {
                        BasicBlock *TrackCurr = Curr;
                        errs() << "\n\nFollowing Track:\n";
                        while (TrackCurr) {
                            errs() << TrackCurr->getName() << "->";
                            auto it = mapToParentBB.find(TrackCurr);
                            if (it != mapToParentBB.end()) {
                                TrackCurr = it->second;
                            } else {
                                TrackCurr = nullptr;
                            }
                        }
                        errs() << "\n";
                        return true;
                    }
                    Instruction *pTerm = Curr->getTerminator();
                    for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
                        BasicBlock *Succ = pTerm->getSuccessor(i);
                        if (Visited.find(Succ) == Visited.end()) {
                            WorkList.push(Succ);
                            Visited.insert(Succ);
                            mapToParentBB[Succ] = Curr;
                        }
                    }
                }
                return false;
            }
            return false;
        }
        return false;
    }

    static bool isReachableInst(Instruction *Src, Instruction *Dest, std::set<BasicBlock *> &setBackEdge) {
        return isReachableInBB(Src, Dest) || isReachableAcrossBB(Src, Dest, setBackEdge);
    }

    static bool isOverWritten(Use *U1, Use *U2) {
        // TODO
        return false;
    }

    static bool isEscapeInst(Instruction *UseInst, Instruction *DropInst, std::set<BasicBlock *> &setBackEdge) {
        if (isReachableInst(DropInst, UseInst, setBackEdge)) {
            return true;
        } else if (isStoreToGlobal(UseInst)) {
            return true;
        }
//        } else if (isOperandOfFunction(UseInst)) {
//            return true;
//        }
        return false;
    }

    static bool isDropInst(Instruction *I) {
        if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
            CallSite CS;
            if (Function *F = getCalledFunc(I, CS)) {
                if (F->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                    return true;
                } else if (F->getName().startswith("_ZN4core3mem4drop")) {
                    return true;
                }
                return false;
            }
            return false;
        }
        return false;
    }

    static bool collectDropInsts(Function *F, std::set<Instruction *> &setDropInst) {
        for (BasicBlock &B : *F) {
            for (Instruction &I : B) {
                if (isDropInst(&I)) {
//                    ++numDropInsts;
                    CallSite CS(&I);
                    if (Value *CV = CS.getCalledValue()) {
                        if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
//                            if (isDropContainsDealloc(Callee)) {
                                setDropInst.insert(&I);
//                                ++numDropContainsDealloc;
//                            }
                        }
                    }
                }
            }
        }
        return !setDropInst.empty();
    }

    static bool printDebugInfo(Instruction *I) {
        const llvm::DebugLoc &lockInfo = I->getDebugLoc();
        auto di = lockInfo.get();
        if (di) {
            errs() << " " << lockInfo->getDirectory() << '/'
                   << lockInfo->getFilename() << ' '
                   << lockInfo.getLine() << "\n\n";
            return true;
        }
        return false;
    }

    static bool printUseAfterFreeDebugInfo(Instruction *DropInst, Instruction *UseAfterDrop) {
        errs() << "\nUse After Free Happens!\n";
        BasicBlock *DropBB = DropInst->getParent();
        BasicBlock *UseBB = UseAfterDrop->getParent();
        Function *DropFunc = DropBB->getParent();
        errs() << "In Function: " << DropFunc->getName() << "\n";
        printDebugInfo(DropInst);
        errs() << "DropBB: " << DropBB->getName() << "\n";
        DropInst->print(errs());
        errs() << "\n";
        printDebugInfo(UseAfterDrop);
        errs() << "UseBB: " << UseBB->getName() << "\n";
        UseAfterDrop->print(errs());
        errs() << "\n";
        return true;
    }

    static bool getEffectiveUses(Instruction *DI, Value *DV, std::set<Use *> &Uses) {
        for (Use &US : DV->uses()) {
            Value *USV = US.get();
            User *U = US.getUser();
            if (Instruction *UI = dyn_cast<Instruction>(U)) {
                if (UI == DI) {
                    continue;
                }
                if (StoreInst *SI = dyn_cast<StoreInst>(UI)) {
                    if (SI->getOperand(1) == USV) {
                        Uses.insert(&US);
                        continue;
                    } else {
                        Uses.insert(&SI->getOperandUse(0));
                        continue;
                    }
                }
                Uses.insert(&US);
            } else {
                Uses.insert(&US);
            }
        }
        return !Uses.empty();
    }

    static bool trackDropDataDep(std::set<Instruction *> &setDropInst, std::set<BasicBlock *> &setBackEdge) {
        for (Instruction *DI : setDropInst) {
            Value *DV = DI->getOperand(0);

            std::set<Use *> setUses;
            if (!getEffectiveUses(DI, DV, setUses)) {
                continue;
            }

            std::list<Value *> WorkList;
            std::set<Value *> Visited;

            for (Use *U : setUses) {
                User *UV = U->getUser();
                WorkList.push_back(UV);
                Visited.insert(UV);
            }

            while (!WorkList.empty()) {
                Value *Curr = WorkList.front();
                WorkList.pop_front();

                if (Instruction *CI = dyn_cast<Instruction>(Curr)) {
                    if (isEscapeInst(CI, DI, setBackEdge)) {
                        printUseAfterFreeDebugInfo(DI, CI);
                        break;
                    }
                }

                setUses.clear();
                if (getEffectiveUses(DI, Curr, setUses)) {
                    for (Use *U : setUses) {
                        User *UV = U->getUser();
                        if (Visited.find(UV) != Visited.end()) {
                            WorkList.push_back(UV);
                            Visited.insert(UV);
                        }
                    }
                }
            }
        }
        return false;
    }

    // ReturnType FuncName(ArgType1, ArgType2, ...)
    // Input Types: All the ArgType, read from global variable
    // Output Types: ReturnType, non-readonly ArgType, write to global variable
    static bool isPtrInPtrOutFunc(Function *F) {

        for (unsigned i = 0; i < F->getNumOperands(); ++i) {
            for (Argument &AR : F->args()) {
                if (AR.getType()->isPointerTy()) {
                    if (AR.hasByValAttr()) {
                        // Input
                    }
                }
            }
            if (F->getOperand(i)->getType()->isPointerTy()) {

                return true;
            }
            if (F->getReturnType()->isPointerTy()) {
                return true;
            }
        }
        return false;
    }

    static bool printErrMsg(Instruction *I, StringRef Msg) {
        errs() << '\n' << Msg << '\n';
        BasicBlock *B = I->getParent();
        Function *F = B->getParent();
        errs() << "In Function: " << F->getName() << "\n";
        errs() << "In BB: " << B->getName() << "\n";
        I->print(errs());
        errs() << "\n";
        return printDebugInfo(I);
    }

    bool NewUseAfterFreeDetector::runOnModule(llvm::Module &M) {

        std::map<Function *, std::map<Instruction *, Function *>> mapCallerCallee;

        for (Function &F : M) {
            if (F.begin() == F.end()) {
                continue;
            }

            for (BasicBlock &B : F) {
                for (Instruction &I : B) {
                    if (isa<CallInst>(&I) || isa<InvokeInst>(&I)) {
                        CallSite CS(&I);
                        if (Value *CV = CS.getCalledValue()) {
                            if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
                                mapCallerCallee[&F][&I] = Callee;
                            } else {
                                printErrMsg(&I, "Callee Not Found:");
                            }
                        } else {
                            printErrMsg(&I, "Callee Not Found:");
                        }
                    }
                }
            }
        }

        for (auto &kv : mapCallerCallee) {
            bool ContainsNonEmptyFunc = false;
            for (auto &kv2 : kv.second) {
                if (kv2.second->begin() != kv2.second->end()) {
                    ContainsNonEmptyFunc = true;
                    break;
                }
            }
            if (!ContainsNonEmptyFunc) {
                if (isPtrInPtrOutFunc(kv.first)) {
                    kv.first->getType()->getContainedType(0)->print(errs());
                    errs() << "\n";
                }
            }
        }

        return false;
    }

//    bool NewUseAfterFreeDetector::runOnModule(llvm::Module &M) {
//        for (Function &F : M) {
//            if (F.begin() == F.end()) {
//                continue;
//            }
//
//            std::set<Instruction *> setDropInst;
//            collectDropInsts(&F, setDropInst);
////            errs() << F.getName() << "\n";
////            for (Instruction *I : setDropInst) {
////                I->print(errs());
////                errs() << "\n";
////            }
//            LoopSet.clear();
//            LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
//            if (!LI.empty()) {
//                for (Loop *L : LI) {
//                    getSubLoopSet(L);
//                }
//            }
//
//            std::set<BasicBlock *> setBackEdge;
//            for (Loop *L : LoopSet) {
//                BasicBlock *IncomingEdge = nullptr;
//                BasicBlock *BackEdge = nullptr;
//                L->getIncomingAndBackEdge(IncomingEdge, BackEdge);
//                if (BackEdge) {
//                    setBackEdge.insert(BackEdge);
//                }
//            }
//
////            if (!setBackEdge.empty()) {
////                errs() << "Function:\n";
////                errs() << (*setBackEdge.begin())->getParent()->getName() << "\n";
////                errs() << "BackEdge:\n";
////                for (BasicBlock *B : setBackEdge) {
////                    errs() << B->getName() << "\n";
////                }
////                errs() << "End of BackEdge:\n";
////            }
//
//            trackDropDataDep(setDropInst, setBackEdge);
//        }
//        return false;
//    }

}  // namespace detector

static RegisterPass<detector::NewUseAfterFreeDetector> X(
        "detect",
        "Detect Use After Free",
        false,
        true);