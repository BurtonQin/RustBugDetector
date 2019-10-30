/**
 * Escape Analysis
 *
 * 1. Given an AllocaInst in the function.
 * 2. Find the Pointer to the AllocaInst.
 * 3. Find the Drop of the AllocaInst.:
 * 4. Determine if Pointer is still alive after the Drop.
 */

#include "UseAfterFreeDetector/UseAfterFreeDetector.h"

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

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "UseAfterFreeDetector"

using namespace llvm;

namespace detector {

    char UseAfterFreeDetector::ID = 0;

    UseAfterFreeDetector::UseAfterFreeDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializeDominatorTreeWrapperPassPass(Registry);
        initializePostDominatorTreeWrapperPassPass(Registry);
        initializeAAResultsWrapperPassPass(Registry);
        initializeLoopInfoWrapperPassPass(Registry);
    }

    void UseAfterFreeDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<PostDominatorTreeWrapperPass>();
        AU.addRequired<AAResultsWrapperPass>();
        AU.addRequired<LoopInfoWrapperPass>();
    }

    static bool isDropInst(Instruction *I) {
        assert(I);
        if (isCallOrInvokeInst(I)) {
            CallSite CS;
            if (Function *F = getCalledFunc(I, CS)) {
                if (F->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                    return true;
                }
            }
        }
        return false;
    }


    // Assumption: Function(p1) -> (p2,...) then p2,... may depend on p1.
    // This may introduce FP.
    static bool isReturnPtr(Function *F) {
        Type *RT = F->getReturnType();
        if (RT->isPointerTy()) {
            return true;
        } else if (RT->isStructTy()) {
            StructType *ST = cast<StructType>(RT);
            if (ST) {
                for (auto it = ST->element_begin(); it != ST->element_end(); ++it) {
                    if ((*it)->isPointerTy()) {
                        return true;
                    }
                }
            }
        } else if (RT->isArrayTy()) {
           ArrayType *AT = cast<ArrayType>(RT);
           if (AT) {
               return AT->getArrayElementType()->isPointerTy();
           }
        }
        return false;
    }

    static void addUses(const Value *V, std::stack<const Use *> &WorkList, std::set<const Use *> &Visited) {
        errs() << "Start\n";
        for (const Use &U : V->uses()) {
            U.getUser()->print(errs());
            errs() << '\n';
            if (Visited.find(&U) == Visited.end()) {
                U.getUser()->print(errs());
                errs() << '\n';
                Visited.insert(&U);
                WorkList.push(&U);
            }
        }
        errs() << "End\n";
    }

    static void trackDependence(const Value *V, std::set<const Use *> &Visited, std::set<const Instruction *> &setDropInst) {
        // check if Value is of pointer type
        assert(V->getType()->isPointerTy() && "Capture is for pointers only!");

        std::stack<const Use *> WorkList;

        addUses(V, WorkList, Visited);

        while (!WorkList.empty()) {
            const Use *U = WorkList.top();
            WorkList.pop();
            Instruction *I = cast<Instruction>(U->getUser());
            V = U->get();

            I->print(errs());
            errs() << '\n';

            switch (I->getOpcode()) {
                case Instruction::Call:
                case Instruction::Invoke: {
                    CallSite CS;
                    Function *F = getCalledFunc(I, CS);
                    if (F->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                        // Record and stop propagation
                        setDropInst.insert(I);
                    } else if (isReturnPtr(F)) {
                        errs() << F->getName() << ": use ";
                        errs() << F->getNumUses() << '\n';
                        errs() << "\n";
                        addUses(V, WorkList, Visited);
                    }
                    break;
                }
                case Instruction::Load: {
                    if (I->getType()->isPointerTy()) {
                        addUses(V, WorkList, Visited);
                    }
                    break;
                }
                case Instruction::Store: {
                    addUses(I->getOperand(1), WorkList, Visited);
                    break;
                }
                case Instruction::ExtractValue:
                case Instruction::BitCast:
                case Instruction::GetElementPtr:
                case Instruction::PHI:
                case Instruction::Select:
                case Instruction::AddrSpaceCast: {
                    addUses(I, WorkList, Visited);
                    break;
                }
                default: {
                    break;
                }
            }
        }
    }


    static bool trackAllocaInst(Instruction *AI, PostDominatorTree &PDT) {
        assert(AI);
        // AllocaInst
        // Get Pointer from BitCast/GEP...
        // Drop
        // No more Use of Pointer
        // Rare(or (Pointer <- X, or Store &Pointer <- X): OK)
        // x <- Pointer: Escape
        // *Pointer <- x: Escape

        std::set<const Use *> Visisted;
        std::set<const Instruction *> setDropInst;
        trackDependence(AI, Visisted, setDropInst);

//        errs() << "setDropInst\n";
//        for (const Instruction *DI : setDropInst) {
//            DI->print(errs());
//            errs() << '\n';
//        }
//        errs() << "End of setDropInst\n";
        std::set<const Use *> NoDropVisited;
        errs() << "Visited\n";
        for (const Use *U : Visisted) {
            Instruction *UI = cast<Instruction>(U->getUser());
            if (setDropInst.find(UI) == setDropInst.end()) {
                NoDropVisited.insert(U);
                UI->print(errs());
                errs() << '\n';
            }
        }
//        errs() << "End of Visited\n";
//        return false;

        // Exists a Use, s.t. No DropInst can dominate it.
        for (const Use *U : NoDropVisited) {
//            // Debug
//            errs() << "Alloca Inst\n";
//            AI->print(errs());
//            errs() << '\n';
//            errs() << "Recursive User\n";
            Instruction *UI = cast<Instruction>(U);
            if (!UI) {
                continue;
            }
//            UI->print(errs());
//            errs() << '\n';
            bool canPostDominate = false;
            for (const Instruction *I : setDropInst) {
                if (PDT.dominates(UI->getParent(), I->getParent())) {
                    canPostDominate = true;
                    break;
                }
            }
            if (canPostDominate) {
                // Debug
                errs() << "DropInst can be post dominated by the Instruction:\n";
                if (Instruction *UI = cast<Instruction>(U->getUser())) {
                    UI->print(errs());
                    errs() << '\n';
                    errs() << "In Function, BB:\n";
                    errs() << UI->getParent()->getParent()->getName() << ", " << UI->getParent()->getName() << '\n';
                }
                errs() << '\n';
                break;
            }
        }

        return false;
    }

    static bool isDropContainsDealloc(Function *DropInPlace) {
        unsigned i = 0;
        for (BasicBlock &B : *DropInPlace) {
            ++i;
            if (i == 3) {
                continue;
            }
            for (Instruction &I : B) {
                if (isCallOrInvokeInst(&I)) {
                    CallSite CS;
                    if (Function *F = getCalledFunc(&I, CS)) {
                        if (F->getName().startswith("_ZN4core3ptr18real_drop_in_place")
                        || F->getName().contains("drop17h")
                        || F->getName().contains("dealloc")
                        || F->getName().contains("free")) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
//        StringRef TargetFuncNamePrefix = "_ZN5alloc5alloc7dealloc";
//
//        std::list<Function *> WorkList;
//        std::set<Function *> Visited;
//
//        WorkList.push_back(DropInPlace);
//        Visited.insert(DropInPlace);
//
//        while (!WorkList.empty()) {
//            Function *Curr = WorkList.front();
//            WorkList.pop_front();
//
//            for (BasicBlock &B : *Curr) {
//                for (Instruction &I : B) {
//                    if (isa<CallInst>(&I) || isa<InvokeInst>(&I)) {
//                        CallSite CS(&I);
//                        if (Value *CV = CS.getCalledValue()) {
//                            if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
//                                if (Callee->getName().startswith(TargetFuncNamePrefix)) {
//                                    return true;
//                                } else if (Visited.find(Callee) == Visited.end()) {
//                                    WorkList.push_back(Callee);
//                                    Visited.insert(Callee);
//                                }
//                            }
//                        }
//                    }
//                }
//            }
//        }

        return false;
    }

    static bool collectDropInsts(Function *F, std::set<Instruction *> &setDropInst, LoopInfo &LI) {
//        unsigned numDropInsts = 0;
//        unsigned numDropContainsDealloc = 0;
        std::set<BasicBlock *> setLoopBB;
        for (auto it = LI.begin(); it != LI.end(); ++it) {
            Loop *pLoop = *it;
            for (BasicBlock *BB : pLoop->blocks()) {
                setLoopBB.insert(BB);
            }
        }
        for (BasicBlock &B : *F) {
            if (setLoopBB.find(&B) != setLoopBB.end()) {
                continue;
            }
            for (Instruction &I : B) {
                if (isDropInst(&I)) {
//                    ++numDropInsts;
                    CallSite CS(&I);
                    if (Value *CV = CS.getCalledValue()) {
                        if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
                            if (isDropContainsDealloc(Callee)) {
                                setDropInst.insert(&I);
//                                ++numDropContainsDealloc;
                            }
                        }
                    }
                }
            }
        }
//        errs() << "numDropInsts:" << numDropInsts << "\n";
//        errs() << "numDropContainsDealloc:" << numDropContainsDealloc << "\n";
        return !setDropInst.empty();
    }

    static std::set<StringRef> AsSliceName { "as_slice", "as_mut_slice" };
    static std::set<StringRef> AsPtrName { "as_ptr", "as_mut_ptr" };

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

    static bool isReachableAcrossBB(Instruction *Src, Instruction *Dest) {
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
                    if (Curr == DestBB) {
                        BasicBlock *TrackCurr = Curr;
                        if (mapToParentBB[TrackCurr]->getName().contains("cleanup")) {
                            return false;
                        }
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

    static bool isReachableInst(Instruction *Src, Instruction *Dest) {
        return isReachableInBB(Src, Dest) || isReachableAcrossBB(Src, Dest);
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

    static bool isFunctionByName(Instruction *UI, const std::set<StringRef> &Names) {
        if (isa<CallInst>(UI) || isa<InvokeInst>(UI)) {
            CallSite CS(UI);
            if (Value *CV = CS.getCalledValue()) {
                if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
                    StringRef FuncName = Callee->getName();
                    for (StringRef Name : Names) {
                        if (FuncName.contains(Name)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    static bool isStoreToGlobal(Instruction *UseInst) {
        if (StoreInst *SI = dyn_cast<StoreInst>(UseInst)) {
            if (GEPOperator *GEP = dyn_cast<GEPOperator>(SI->getPointerOperand())) {
                return isa<GlobalVariable>(GEP->getOperand(0)->stripPointerCasts());
            }
            return false;
        }
        return false;
    }

    static bool isEscapeInst(Instruction *UseInst, Instruction *DropInst) {
        if (isReachableInst(DropInst, UseInst)) {
            errs() << "Drop Inst can reach UseInst\n";
            return true;
        }
        if (isStoreToGlobal(UseInst)) {
            errs() << "Pointer Store to Global Variable!\n";
            return true;
        }
        return false;
    }

    static Instruction *getReturnAlloca(Function *F) {
        return F->getEntryBlock().getFirstNonPHIOrDbgOrLifetime();
    }

    // AliasSet (MustAlias, MayAlias, PartialAlias)
    // If one dropping, coexists with global, return value, or output argument.
    // then report
    // Otherwise, compute the reachability from drop to use of aliased ptr.
    // If can reach, then report
    static bool collectAllocaInst(Function *F, std::set<Instruction *> &setAllocaInst) {
        if (!F) {
            return false;
        }
        if (F->begin() == F->end()) {
            return false;
        }
        for (Instruction &I : F->getEntryBlock()) {
            if (isa<AllocaInst>(&I)) {
                setAllocaInst.insert(&I);
            }
        }
        return !setAllocaInst.empty();
    }

    static bool mapAllocaToDrop(const std::set<Instruction *> &setAllocaInst, std::map<Instruction *, std::set<Instruction *>> &mapAllocaToDropInst) {
        for (Instruction *I : setAllocaInst) {
            for (User *U : I->users()) {
                if (Instruction *UI = dyn_cast<Instruction>(U)) {
                    if (isDropInst(UI)) {
                        CallSite CS(UI);
                        if (Value *CV = CS.getCalledValue()) {
                            if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
                                if (isDropContainsDealloc(Callee)) {
//                                    errs() << Callee->getName() << "\n";
                                    mapAllocaToDropInst[I].insert(UI);
                                }
                            }
                        }
                    }
                }
            }
        }
        return !mapAllocaToDropInst.empty();
    }

    // Drop, Write, Read, New
    // ptr = New()
    // Write(ptr->ptr2)
    // Drop(ptr)
    // Use(ptr2): ERR
    // Write(ptr3->ptr): OK
    static bool killUses(std::set<Use *> &setUse) {
        // ptr = New()
        // Write(ptr3->ptr) ;ptr=>ptr.0
        // Drop(ptr.0)
        // Use(ptr.0)
        return false;
    }

    static Instruction *selectFirstWrite(std::set<Instruction *> &setWriteInst) {

        std::map<BasicBlock *, Instruction *> mapBBToInst;
        for (Instruction *WI : setWriteInst) {
            BasicBlock *BB = WI->getParent();
            if (mapBBToInst.find(BB) == mapBBToInst.end()) {
                mapBBToInst[BB] = WI;
            } else {
                if (isReachableInBB(WI, mapBBToInst[BB])) {
                    mapBBToInst[BB] = WI;
                }
            }
        }

        if (mapBBToInst.size() == 1) {
            return mapBBToInst.begin()->second;
        }

        Function *F = mapBBToInst.begin()->first->getParent();
        BasicBlock &BB = F->getEntryBlock();
        std::list<BasicBlock *> WorkList;
        std::set<BasicBlock *> Visited;
        WorkList.push_back(&BB);
        Visited.insert(&BB);

        while (!WorkList.empty()) {
            BasicBlock *Curr = WorkList.front();
            WorkList.pop_front();
            if (mapBBToInst.find(Curr) != mapBBToInst.end()) {
                return mapBBToInst[Curr];
            }
            for (auto it = succ_begin(Curr); it != succ_end(Curr); ++it) {
                if (Visited.find(Curr) == Visited.end()) {
                    WorkList.push_back(*it);
                    Visited.insert(*it);
                }
            }
        }

        return nullptr;
    }

    static bool trackDropDataDep(std::set<Instruction *> &setDropInst) {
        for (Instruction *DI : setDropInst) {
            Value *DV = DI->getOperand(0);

            std::list<Value *> WorkList;
            std::set<Value *> Visited;

            std::set<Use *> Uses;
            std::set<Instruction *> setWriteInst;
            for (Use &US : DV->uses()) {
                Value *USV = US.get();
                User *U = US.getUser();
                if (Instruction *UI = dyn_cast<Instruction>(U)) {
                    if (UI == DI) {
                        continue;
                    }
                    if (StoreInst *SI = dyn_cast<StoreInst>(UI)) {
                        if (SI->getOperand(1) == USV) {
                            setWriteInst.insert(SI);
//                            errs() << "Write\n";
//                            SI->print(errs());
//                            errs() << "\n";
                            Uses.insert(&US);
                        }
                    }
                }
                Uses.insert(&US);
            }

            Instruction *FirstWriteInst;
            if (setWriteInst.size() > 1) {
                FirstWriteInst = selectFirstWrite(setWriteInst);
            } else {
                FirstWriteInst = *setWriteInst.begin();
            }

            std::set<Use *> setFilteredUses;
            for (Use *US : Uses) {
                Value *USV = US->get();
                User *U = US->getUser();
                Instruction *UI = dyn_cast<Instruction>(U);
                bool ShouldFilter = false;
                if (UI) {
                    if (setWriteInst.find(UI) != setWriteInst.end()) {
                        ShouldFilter = true;
                    } else {
                        for (Instruction *WI : setWriteInst) {
                            if (WI == FirstWriteInst) {
                                continue;
                            }
                            if (isReachableInst(WI, UI)) {
//                            errs() << "Remove\n";
//                            WI->print(errs());
//                            errs() << "\n";
//                            UI->print(errs());
//                            errs() << "\n";
                                ShouldFilter = true;
                                break;
                            }
                        }
                    }
                }
                if (!ShouldFilter) {
                    setFilteredUses.insert(US);
                }
            }

//            errs() << "Users\n";
//            for (Use *U : setFilteredUses) {
//                U->getUser()->print(errs());
//                errs() << "\n";
//            }

            for (Use *US : setFilteredUses) {
                Value *USV = US->get();
                User *U = US->getUser();
                if (Value *UV = dyn_cast<User>(U)) {
                    if (Instruction *UI = dyn_cast<Instruction>(UV)) {
                        if (UI == DI) {
                            continue;
                        }
                        if (StoreInst *SI = dyn_cast<StoreInst>(UI)) {
                            if (SI->getPointerOperand() == USV) {
                                continue;
                            }
                        }
                        // TODO: add only write insts: e.g. memory copy/move dest
                    }
                    WorkList.push_back(UV);
                    Visited.insert(UV);
                }
            }

            while (!WorkList.empty()) {
                Value *Curr = WorkList.front();
                WorkList.pop_front();

                if (Instruction *CI = dyn_cast<Instruction>(Curr)) {
//                    if (isa<LoadInst>(CI)
//                            || isa<BitCastInst>(CI) || isa<GetElementPtrInst>(CI)
//                                    || (isa<PHINode>(CI) && isa<PointerType>(CI->getType()))) {
                        if (isEscapeInst(CI, DI)) {
                            printUseAfterFreeDebugInfo(DI, CI);
                            break;
                        }
//                    }
                }

                for (Use &US : Curr->uses()) {
                    Value *USV = US.get();
                    User *U = US.getUser();
                    if (Value *V = dyn_cast<Value>(U)) {
                        if (StoreInst *SI = dyn_cast<StoreInst>(V)) {
                            if (SI->getPointerOperand() == USV) {
                                continue;
                            }
                            // TODO: add only write insts: e.g. memory copy/move dest
                        }
                        if (Visited.find(V) == Visited.end()) {
                            WorkList.push_back(V);
                            Visited.insert(V);
                        }
                    }
                }
            }
        }

        return false;
    }

    static bool trackAliasedInst(std::map<Instruction *, std::set<Instruction *>> &mapAllocaToDropInst,
            AliasAnalysis &AA) {

        for (auto &kv : mapAllocaToDropInst) {
            Instruction *AI = kv.first;

            std::list<Value *> WorkList;
            std::set<Value *> Visited;

            for (User *U : AI->users()) {
                if (Value *UV = dyn_cast<Value>(U)) {
                    if (Instruction *UI = dyn_cast<Instruction>(U)) {
                        if (kv.second.find(UI) != kv.second.end()) {
                            continue;
                        }
                    }
                    WorkList.push_back(UV);
                    Visited.insert(UV);
                }
            }

            while (!WorkList.empty()) {
                Value *Curr = WorkList.front();
//                errs() << "Track\n";
//                Curr->print(errs());
//                errs() << "\n";
                WorkList.pop_front();
//                if (isa<GlobalVariable>(Curr)) {
//                    errs() << "Use After Free: Global Value!\n";
//                    Curr->print(errs());
//                    errs() << "\n";
//                    continue;
////                    return true;
//
//                }
                auto result = AA.alias(Curr, AI);
//                errs() << "Result:\n";
                Curr->print(errs());
                errs() << "\n";
                errs() << result << "\n";
//                if (result != NoAlias) {
                    if (Instruction *CI = dyn_cast<Instruction>(Curr)) {
                        for (Instruction *DI : kv.second) {
                            if (AA.alias(Curr, AI) != NoAlias) {
                                if (isEscapeInst(CI, DI)) {
                                    printUseAfterFreeDebugInfo(DI, CI);
                                    break;
//                                continue;
                                }
                            }
                        }
                    }
                    for (User *U : Curr->users()) {
                        errs() << "Users:\n";
                        U->print(errs());
                        errs() << "\n";

                        if (Value *V = dyn_cast<Value>(U)) {
                            if (Visited.find(V) == Visited.end()) {
                                WorkList.push_back(V);
                                Visited.insert(V);
                            }
                        }
                    }
                }
            }
        return true;
    }

    static bool calcAllocaAlias(std::map<Instruction *, std::set<Instruction *>> &mapAllocaToDropInst,
            const std::set<Instruction *> &setAllocaInst,
            AliasAnalysis &AA) {
        for (auto &kv : mapAllocaToDropInst) {
            Instruction *I = kv.first;
            for (User *U : I->users()) {
                Instruction *UI = dyn_cast<Instruction>(U);
                if (UI) {
                auto result = AA.alias(I, UI);
                if (result != NoAlias) {
                    errs() << "AliasAnalysis:\n";
                    I->print(errs());
                    errs() << "\n";
                    UI->print(errs());
                    errs() << "\n";
                    errs() << "AliasResult:" << result << "\n";
                    for (User *NU : UI->users()) {
                        for (Instruction *DI : kv.second) {
                            if (Instruction *NUI = dyn_cast<Instruction>(NU)) {
                                if (isReachableInst(DI, NUI)) {
                                    errs() << "Use After Free!\n";
                                    DI->print(errs());
                                    NUI->print(errs());
                                    errs() << "\n";
                                    return true;
                                }
                            }
                        }
                    }
                }
                }
            }
        }
//        for (auto &kv: mapAllocaToDropInst) {
//            for (const Instruction *I2 : setAllocaInst) {
//                const Instruction *I1 = *kv.second.begin();
//                if (I1 == I2) {
//                    continue;
//                }
//                auto result = AA.alias(I1, I2);
//                if (result != NoAlias) {
//                    errs() << "AliasAnalysis:\n";
//                    I1->print(errs());
//                    errs() << "\n";
//                    I2->print(errs());
//                    errs() << "\n";
//                    errs() << "AliasResult:" << result << "\n";
//                }
//            }
//        }
        return true;
    }



    static bool trackDroppedPointerSpecial(Instruction *DropInst) {
        Value *DroppedPtr = DropInst->getOperand(0);

        if (!DroppedPtr) {
            return false;
        }
        for (User *U : DroppedPtr->users()) {
            if (Instruction *UI = dyn_cast<Instruction>(U)) {
                if (isFunctionByName(UI, AsSliceName)) {
                    // Debug
//                    errs() << "As Slice" << "\n";
//                    UI->print(errs());
//                    errs() << "\n";
                    for (User * U2: UI->users()) {
                        if (Instruction *UI2 = dyn_cast<Instruction>(U2)) {
                            if (isa<ExtractValueInst>(UI2)) {
                                for (User *U3 : UI2->users()) {
                                    if (Instruction *UI3 = dyn_cast<Instruction>(U3)) {
                                        if (isFunctionByName(UI3, AsPtrName)) {
                                            errs() << "As Ptr" << "\n";
                                            printDebugInfo(UI3);
//                                            UI3->print(errs());
//                                            errs() << "\n";
                                            for (User *U4 : UI3->users()) {
                                                if (Instruction *UI4 = dyn_cast<Instruction>(U4)) {
//                                                    errs() << "Use:\n";
//                                                    UI4->print(errs());
//                                                    errs() << "\n";
                                                    if (isEscapeInst(UI4, DropInst)) {
                                                        printUseAfterFreeDebugInfo(DropInst, UI4);
                                                        // Debug
                                                        UI3->print(errs());
                                                        errs() << "\n";
                                                        UI2->print(errs());
                                                        errs() << "\n";
                                                        UI->print(errs());
                                                        errs() << "\n";
                                                        return true;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if (isFunctionByName(UI, AsPtrName)) {
                    errs() << "As Ptr" << "\n";
                    printDebugInfo(UI);
//                    UI->print(errs());
//                    errs() << "\n";
                    for (User *U2 : UI->users()) {
                        if (Instruction *UI2 = dyn_cast<Instruction>(U2)) {
                            if (isEscapeInst(UI2, DropInst)) {
                                printUseAfterFreeDebugInfo(DropInst, UI2);
                                // Debug
                                UI2->print(errs());
                                errs() << "\n";
                                UI->print(errs());
                                errs() << "\n";
                                return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static bool trackDroppedPointerAll(Instruction *DropInst) {
        Value *DroppedPtr = DropInst->getOperand(0);
        if (DroppedPtr) {
            std::list<Value *> WorkList;
            std::set<Value *> Visited;
            WorkList.push_back(DroppedPtr);
            while (!WorkList.empty()) {
                Value *Curr = WorkList.front();
                WorkList.pop_front();
                Instruction *CurrInst = dyn_cast<Instruction>(Curr);
                if (CurrInst && Curr->getType()->isPointerTy() && isReachableInst(DropInst, CurrInst)) {
                    printUseAfterFreeDebugInfo(DropInst, CurrInst);
                    return true;
                }
                for (User *U : Curr->users()) {
                    if (Visited.find(U) == Visited.end()) {
                        WorkList.push_back(U);
                        Visited.insert(U);
                    }
                }
            }
            return false;
        }
        return false;
    }

    static bool trackDroppedPointerBak(Instruction *I) {
        Value *V = I->getOperand(0);
        for (User *U : V->users()) {
            if (Instruction *UI = cast<Instruction>(U)) {
                UI->print(errs());
                errs() << '\n';
                for (User *U2 : UI->users()) {
                    if (Instruction *UI2 = cast<Instruction>(U2)) {
                        errs() << "\t";
                        UI2->print(errs());
                        errs() << "\t\n";
                        for (User *U3 : UI2->users()) {
                            if (Instruction *UI3 = cast<Instruction>(U3)) {
                                errs() << "\t\t";
                                UI3->print(errs());
                                errs() << "\t\t\n";
                            }
                            for (User *U4 : U3->users()) {
                                if (Instruction *UI4 = cast<Instruction>(U4)) {
                                    errs() << "\t\t\t";
                                    UI4->print(errs());
                                    errs() << "\t\t\n";
                                    if (isReachableInBB(I, UI4) || isReachableAcrossBB(I, UI4)) {
                                        errs() << "Reachable!\n";
                                        I->print(errs());
                                        errs() << "\n";
                                        UI4->print(errs());
                                        errs() << "\n";
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return true;
    }

//    static bool detectFunction(Function *F) {
//        // Function *F = M.getFunction("_ZN10servo_522216FontTemplateData4new217h11560e7ba0956712E");
//        if (F && F->begin() != F->end()) {
//            std::set<Instruction *> setDropInst;
//            collectDropInsts(F, setDropInst);
//            for (Instruction *I : setDropInst) {
//                trackDroppedPointerSpecial(I);
//            }
//            return true;
//        }
//        return false;
//    }

    static bool isResultOption(StructType *ST) {
        return ST->getName().startswith("core::option::Option<")
        || ST->getName().startswith("core::result::Result<");
    }

    static bool isResultOptionObj(StructType *ST) {
        return !ST->getName().startswith("core::option::Option<*")
        && !ST->getName().startswith("core::option::Option<()")
        && !ST->getName().startswith("core::result::Result<*")
        && !ST->getName().startswith("core::result::Result<()");
    }

    static bool detectAliasFunction(Function *F, AliasAnalysis &AA) {
        if (!F || F->begin() == F->end()) {
            return false;
        }
//        errs() << F->getName() << "\n";
//        if (F->getName() != "_ZN7openssl3cms14CmsContentInfo7encrypt17h3ef6cac406f7cd43E") {
//            return false;
//        }
        std::set<Instruction *> setAllocaInst;
        if (!collectAllocaInst(F, setAllocaInst)) {
            return false;
        }
//        errs() << "Alloca\n";
//        for (Instruction *I : setAllocaInst) {
//            I->print(errs());
//            errs() << "\n";
//        }
        std::map<Instruction *, std::set<Instruction *>> mapAllocaToDropInst;
        if (!mapAllocaToDrop(setAllocaInst, mapAllocaToDropInst)) {
            return false;
        }

        errs() << "Alloca\n";
        for (Instruction *I : setAllocaInst) {
            I->print(errs());
            errs() << "\n";
        }

//        errs() << "Alloca has drop\n";
//        std::map<Instruction *, std::set<Instruction *>> mapAllocaToDropInstFiltered;
//        for (const auto &kv : mapAllocaToDropInst) {
//            Type *ActualTy = kv.first->stripPointerCasts()->getType();
////            ActualTy->print(errs());
////            errs() << "\n";
//            if (ActualTy->isPointerTy()) {
////                errs() << "Strip Pointer\n";
//                Type *PointeeTy = ActualTy->getPointerElementType();
////                PointeeTy->print(errs());
////                errs() << "\n";
//                if (isa<PointerType>(PointeeTy)) {
//                    errs() << "Pointer to Pointer\n";
//                    PointeeTy->print(errs());
//                    errs() << "\n";
//                    kv.first->print(errs());
//                    errs() << "\n";
//                    mapAllocaToDropInstFiltered[kv.first] = mapAllocaToDropInst[kv.first];
//                } else if (StructType *ST = dyn_cast<StructType>(PointeeTy)) {
//                    if(ST->getStructName().startswith("alloc::")) {
//                        errs() << "Alloc::\n";
//                        ST->print(errs());
//                        errs() << "\n";
//                        kv.first->print(errs());
//                        errs() << "\n";
//                        mapAllocaToDropInstFiltered[kv.first] = mapAllocaToDropInst[kv.first];
//                    }  else if (isResultOption(ST)) {
//                        if (isResultOptionObj(ST)) {
//                            if (ST->getStructNumElements() > 1) {
//                                if (Type *InnerTy = ST->getStructElementType(1)) {
//                                    if (InnerTy->isPointerTy()) {
//                                        errs() << "Option/Result\n";
//                                        ST->print(errs());
//                                        errs() << "\n";
//                                        kv.first->print(errs());
//                                        errs() << "\n";
//                                        mapAllocaToDropInstFiltered[kv.first] = mapAllocaToDropInst[kv.first];
//                                    }
//                                }
//                            }
//                        }
//                    }
//                }
//            }

//            errs() << "AllocaToDropInst Begins\n";
//            for (auto &kv : mapAllocaToDropInstFiltered) {
//                kv.first->print(errs());
//                errs() << "\n";
//                Instruction *DI = *kv.second.begin();
//                DI->print(errs());
//                errs() << "\n";
//            }
//            errs() << "AllocaToDropInst Ends\n";

//            Type *InnerTy = kv.first->stripPointerCasts()->getType()->getContainedType(0);
////            InnerTy->print(errs());
////            errs() << "\n";
//            if (StructType *ST = dyn_cast<StructType>(InnerTy)) {
//                ST->print(errs());
//                errs() << "\n";
//                if (ST->getName().startswith("core::result::Result")) {
//                    //kv.first->print(errs());
//                    errs() << "Result:\n";
//                    ST->print(errs());
//                    errs() << "\n";
//                    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
//                        if (StructType *ST2 = dyn_cast<StructType>(ST->getStructElementType(i))) {
//                            errs() << ST2->getStructName() << "\n";
//                            errs() << "\n";
//                        }
//                    }
////                }
//                }
//            }
//        }
//        calcAllocaAlias(mapAllocaToDropInst, setAllocaInst, AA);
//        trackAliasedInst(mapAllocaToDropInstFiltered, AA);
        return true;
    }

    bool UseAfterFreeDetector::runOnModule(llvm::Module &M) {
        for (Function &F : M) {
            if (F.begin() == F.end()) {
                continue;
            }
//            if (F.getName() != "_ZN9crossbeam13treiber_stack21TreiberStack$LT$T$GT$7try_pop17h798713a4d2453146E") {
//                continue;
//            }
//            if (F.getName().startswith("_ZN4core") ||
//                    F.getName().startswith("_ZN5alloc") ||
//                    F.getName().contains("new")) {
//                continue;
//            }
//            if (F.getName() != "_ZN7openssl3cms14CmsContentInfo7encrypt17h3ef6cac406f7cd43E") {
//                continue;
//            }
            LoopInfo &LoopInfo = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
            std::set<Instruction *> setDropInst;
            collectDropInsts(&F, setDropInst, LoopInfo);
//            errs() << F.getName() << "\n";
//            for (Instruction *I : setDropInst) {
//                I->print(errs());
//                errs() << "\n";
//            }
            trackDropDataDep(setDropInst);
//            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(F).getAAResults();
//            detectAliasFunction(&F, AA);
//            if (F.getName().contains("gethostent")) {
//                detectFunction(&F);
//            }
        }
        return false;
    }

//    bool UseAfterFreeDetector::runOnModule(Module &M) {
//        pModule = &M;
//
//        std::set<Instruction *> setAllocaInst;
//        for (Function &F : M) {
//            if (F.getName() == "_ZN10servo_522216FontTemplateData4new217h11560e7ba0956712E") {
//            // if (F.begin() != F.end()) {
//                setAllocaInst.clear();
//                for (BasicBlock &B : F) {
//                    for (Instruction &I : B) {
//                        if (isa<AllocaInst>(&I)) {
//                            setAllocaInst.insert(&I);
//                        } else if (isa<ExtractValueInst>(&I)) {
//                            errs() << "ExtractValue:\n";
//                            (&I)->print(errs());
//                            errs() << '\n';
//                            Value *V = (&I)->getOperand(0);
//                            V->print(errs());
//                            errs() << '\n';
//                        }
//                    }
//                }
//                PostDominatorTree &PDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();
//                for (Instruction *AI : setAllocaInst) {
//                    trackAllocaInst(AI, PDT);
//                }
//            }
//        }
//        return false;
//    }

    static bool hasDropInsts(Value *V, std::set<Instruction *> &setReturn, PostDominatorTree& PDT) {
        for (User *U: V->users()) {
            Instruction *UI = dyn_cast<Instruction>(U);
            if (UI) {
                if (isCallOrInvokeInst(UI)) {
                    CallSite CS;
                    if (Function *F = getCalledFunc(UI, CS)) {
                        if (F->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                            for (Instruction *R: setReturn) {
                                if (PDT.dominates(R->getParent(), UI->getParent())) {
                                    // Debug
                                    errs() << "Return: ";
                                    R->print(errs());
                                    errs() << "postdom\n";
                                    UI->print(errs());
                                    errs() << '\n';
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static bool escapeDetect(Function *F, std::set<Value *> &setMayEscape, PostDominatorTree &PDT) {

        assert(F);

        std::set<Value *> setValue;
        std::set<Instruction *> setReturn;
        for (BasicBlock &B: *F) {
            for (Instruction &I: B) {
                Instruction *II = &I;
                if (isa<AllocaInst>(II)) {
                    setValue.insert(II);
                } else if (isa<ReturnInst>(II)) {
                    setReturn.insert(II);
                }
            }
        }

        bool hasEscape = false;
//        errs() << "Num of Value: " << setValue.size() << '\n';
        // Debug
        for (Value *V : setValue) {
//            V->print(errs());
//            errs() << "\tMayBeCaptured:";
            if (PointerMayBeCaptured(V, true, false)) {
                if (hasDropInsts(V, setReturn, PDT)) {
                    setMayEscape.insert(V);
                    hasEscape = true;
//                errs() << "Y\n";
                } else {
//                    errs() << "N\n";
                }
            } else {
//                errs() << "N\n";
            }
        }

        return hasEscape;
    }

//    bool UseAfterFreeDetector::runOnModule(Module &M) {
//        this->pModule = &M;
//
//        std::set<Value *> MayEscape;
//        for (Function &F : M) {
//            MayEscape.clear();
//            if (F.begin() == F.end()) {
//                continue;
//            }
//            PostDominatorTree &PDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();
//            if (escapeDetect(&F, MayEscape, PDT)) {
//                errs() << F.getName() << "\n";
//                for (Value *V: MayEscape) {
//                    errs() << '\t';
//                    V->print(errs());
//                    errs() << '\n';
//                }
//            }
//        }
//        return false;
//    }

}  // namespace detector


static RegisterPass<detector::UseAfterFreeDetector> X(
        "detect",
        "Detect Use After Free",
        false,
        true);
