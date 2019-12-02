#include "NewCellIMDetector/NewCellIMDetector.h"

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

#define DEBUG_TYPE "CellIMDetector"

using namespace llvm;

namespace detector {

    char NewCellIMDetector::ID = 0;

    NewCellIMDetector::NewCellIMDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializePostDominatorTreeWrapperPassPass(Registry);
        initializeDominatorTreeWrapperPassPass(Registry);
        initializeAAResultsWrapperPassPass(Registry);
    }

    void NewCellIMDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<PostDominatorTreeWrapperPass>();
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<AAResultsWrapperPass>();
    }

    static bool isAtomicAPI(Function *F) {
        return F->getName().startswith("_ZN4core4sync6atomic");
    }

    // A: call atomic API
    // B: call Cell API
    // A -> ? -> cmp -> branch -> ... -> B
    static bool collectBranchForAtomicCall(Instruction *AtomicCallInst, std::set<Instruction *> &setBranchInst) {
        std::list<Instruction *> WorkList;
        std::set<Instruction *> Visited;
        WorkList.push_back(AtomicCallInst);
        Visited.insert(AtomicCallInst);

        for (User *U : AtomicCallInst->users()) {
            Instruction *I = dyn_cast<Instruction>(U);
            WorkList.push_back(I);
            Visited.insert(I);
        }

        while (!WorkList.empty()) {
            Instruction *CurrInst = WorkList.front();
            WorkList.pop_front();
            for (User *U : CurrInst->users()) {
                if (CmpInst *CI = dyn_cast<CmpInst>(U)) {
                    for (User *U2 : CI->users()) {
                        if (BranchInst *BI = dyn_cast<BranchInst>(U2)) {
                            setBranchInst.insert(BI);
                        }
                    }
                }
            }
        }

        return !setBranchInst.empty();
    }

    static bool isReachableAcrossBB(Instruction *BI, Instruction *CellCallInst) {
        if (BI->getParent() == CellCallInst->getParent()) {
            return false;
        }

        std::list<BasicBlock *> WorkList;
        std::set<BasicBlock *> Visited;

        WorkList.push_back(BI->getParent());
        Visited.insert(BI->getParent());

        while (!WorkList.empty()) {
            BasicBlock *Curr = WorkList.front();
            WorkList.pop_front();
            if (Curr == CellCallInst->getParent()) {
                return true;
            }
            Instruction *pTerm = Curr->getTerminator();
            if (!pTerm) {
                continue;
            }
            for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
                BasicBlock *Succ = pTerm->getSuccessor(i);
                if (Visited.find(Succ) == Visited.end()) {
                    WorkList.push_back(Succ);
                    Visited.insert(Succ);
                }
            }
        }
        return false;
    }

    static bool skipInst(Instruction *I) {
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

    static bool readSyncImmuFunc(std::set<std::string> &setImmuFunc) {
        std::ifstream myfile("SyncImmuFunc.info");
        std::string line;
        if (myfile.is_open()) {
//            errs() << "SyncImmuFunc:\n";
            while (getline(myfile, line)) {
                if (line.find("//", 0) == 0) {
                    continue;
                }
//                errs() << line << "\n";
                setImmuFunc.insert(line);
            }
            myfile.close();
            return !setImmuFunc.empty();
        } else {
            errs() << "Cannot open SyncImmuFunc.info" << "\n";
            return false;
        }
    }

    static bool isCellIMFunc(Function *F) {
        static std::set<StringRef> CellIMFuncPrefixes{
//                // Cell
//                "_ZN4core4cell13Cell$LT$T$GT$3set",
//                "_ZN4core4cell13Cell$LT$T$GT$4swap",
//                "_ZN4core4cell13Cell$LT$T$GT$7replace",
//                "_ZN4core4cell13Cell$LT$T$GT$12replace_with",
//                "_ZN4core4cell13Cell$LT$T$GT$4take",
                // RefCell
                "_ZN4core4cell16RefCell$LT$T$GT$7replace",
                "_ZN4core4cell16RefCell$LT$T$GT$7replace_with",
                "_ZN4core4cell16RefCell$LT$T$GT$4swap",
                "_ZN4core4cell16RefCell$LT$T$GT$10borrow_mut"
        };
        StringRef Name = F->getName();
        for (StringRef Prefix : CellIMFuncPrefixes) {
            if (Name.contains(Prefix)) {
                return true;
            }
        }
        return false;
    }

    static bool isCellPossbileIMFunc(Function *F) {
        static std::set<StringRef> CellIMFuncPrefixes{
                // UnsfeCell
                "_ZN4core4cell19UnsafeCell$LT$T$GT$3get",
                // Cell
                "_ZN4core4cell13Cell$LT$T$GT$6as_ptr",
                // RefCell
//                "_ZN4core4cell16RefCell$LT$T$GT$7replace",
//                "_ZN4core4cell16RefCell$LT$T$GT$7replace_with",
//                "_ZN4core4cell16RefCell$LT$T$GT$4swap",
//                "_ZN4core4cell16RefCell$LT$T$GT$10borrow_mut",
        };
        StringRef Name = F->getName();
        for (StringRef Prefix : CellIMFuncPrefixes) {
            if (Name.contains(Prefix)) {
                return true;
            }
        }
        return false;
    }

    static bool isSemaphoreIMFunc(Function *F) {
        return F->getName().startswith("_ZN10tokio_sync9semaphore6Permit11is_acquired17h");
    }

    static bool collectCallees(Function *F,
                               std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallee) {
        if (!F || F->isDeclaration()) {
            return false;
        }

        for (BasicBlock &BB : *F) {
            for (Instruction &II : BB) {
                Instruction *I = &II;
                if (!skipInst(I)) {
                    if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
                        CallSite CS(I);
                        Function *Callee = CS.getCalledFunction();
                        if (Callee && !Callee->isDeclaration()) {
                            mapCallerCallee[F].insert(std::make_pair(I, Callee));
                        }
                    }
                }
            }
        }

        return true;
    }

    static bool trackDataDep(Value *Src, Value *Target) {
        Value *Stripped = Target->stripPointerCasts();
        if (Stripped->getType()->isPointerTy()) {
            Type *InnerTy = Stripped->getType()->getContainedType(0);
            if (!isa<StructType>(InnerTy)) {
                return false;
            }
        } else {
            return false;
        }

        std::list<Value *> WorkList;
        std::set<Value *> Visited;
        std::map<Value *, Value *> Parents;
        WorkList.push_back(Target);
        Visited.insert(Target);

        while (!WorkList.empty()) {
            Value *Curr = WorkList.front();
            WorkList.pop_front();
            for (Use &US : Curr->uses()) {
                Value *USV = US.get();
                User *U = US.getUser();
                if (USV == Src) {
//                    errs() << "Track\n";
//                    Value *Track = USV;
//                    while (Track != Target) {
//                        Track = Parents[Track];
//                        Track->print(errs());
//                        errs() << "\n";
//                    }
                    return true;
                }
                if (Value *UV = dyn_cast<Value>(U)) {
                    if (UV == Target) {
                        continue;
                    }
                    if (Visited.find(UV) != Visited.end()) {
                        continue;
                    }

                    WorkList.push_back(UV);
                    Visited.insert(UV);
                    Parents[UV] = Curr;
                }
            }
        }
        return false;
    }

    static bool isSelfToSelfCI(Instruction *CI) {
        CallSite CS(CI);
        if (CS.getNumArgOperands() > 0) {
            Value *FirstOp = CS.getArgOperand(0);
            Function *Caller = CI->getParent()->getParent();
            if (Caller->arg_size() > 0) {
                Argument *FirstArg = Caller->arg_begin();
                if (trackDataDep(FirstOp, FirstArg)) {
                    return true;
                }
            }
        }
        return false;
    }

    static bool containsCellIM(
            Function *SyncImmuFunc,
            std::set<Function *> &setCellIMFunc,
            std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallSites,
            std::vector<Function *> &vecTrack
    ) {

        std::list<Function *> WorkList;
        std::set<Function *> Visited;
        std::map<Function *, Function *> CalleeTracker;

        WorkList.push_back(SyncImmuFunc);
        Visited.insert(SyncImmuFunc);

        while (!WorkList.empty()) {
            Function *Curr = WorkList.front();
            WorkList.pop_front();
            if (setCellIMFunc.find(Curr) != setCellIMFunc.end()) {
                return true;
            }
            if (mapCallerCallSites.find(Curr) == mapCallerCallSites.end()) {
                continue;
            }
            for (auto &kv : mapCallerCallSites[Curr]) {
                if (setCellIMFunc.find(kv.second) != setCellIMFunc.end()) {
//                    // Track
                    vecTrack.push_back(kv.second);
                    Function *TrackCurr = Curr;
                    while (TrackCurr != SyncImmuFunc) {
                        vecTrack.push_back(TrackCurr);
                        TrackCurr = CalleeTracker[TrackCurr];
                    }
                    vecTrack.push_back(SyncImmuFunc);
                    return true;
                }
                if (isSelfToSelfCI(kv.first)) {
                    if (Visited.find(kv.second) == Visited.end()) {
                        WorkList.push_back(kv.second);
                        Visited.insert(kv.second);
                        CalleeTracker[kv.second] = Curr;
                    }
                }
            }
        }
        return false;
    }

    static bool printDebugInfo(Instruction *I) {
        const llvm::DebugLoc &lockInfo = I->getDebugLoc();
//        I->print(errs());
//        errs() << "\n";
        auto di = lockInfo.get();
        if (di) {
            errs() << " " << lockInfo->getDirectory() << ' '
                   << lockInfo->getFilename() << ' '
                   << lockInfo.getLine() << "\n";
            return true;
        } else {
            return false;
        }
    }

    static bool isWriteOrEscape(Instruction *CellCallInst) {
        for (User *U : CellCallInst->users()) {
            if (Instruction *I = dyn_cast<Instruction>(U)) {
                if (skipInst(I)) {
                    continue;
                }
                if (isa<ReturnInst>(I)) {
                    return true;
                }
                if (isa<LoadInst>(I)) {
                    for (User *U2 : I->users()) {
                        if (isa<StoreInst>(U2)) {
                            return true;
                        }
                    }
                }
                if (isCallOrInvokeInst(I)) {
                    CallSite CS(I);
                    if (Function *F = CS.getCalledFunction()) {
                        if (!F->getName().contains("Deref")) {
                            continue;
                        }
                        for (User *U2 : I->users()) {
                            if (isa<ReturnInst>(U2)) {
                                return true;
                            } else if (isa<StoreInst>(U2)) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    static bool collectCellIMCallers(
            std::set<Function *> &setSyncImmuFunc,
            std::set<Function *> &setCellIMFunc,
            std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallSites) {
        for (Function *SyncImmuFunc : setSyncImmuFunc) {
            std::vector<Function *> vecTracker;
            if (containsCellIM(SyncImmuFunc, setCellIMFunc, mapCallerCallSites, vecTracker)) {
                if (Instruction *FirstInst = SyncImmuFunc->getEntryBlock().getFirstNonPHIOrDbgOrLifetime()) {
                    printDebugInfo(FirstInst);
                }
                errs() << "\nSync Func Contains Interior Mutability\n";
                errs().write_escaped(SyncImmuFunc->getName()) << "\n";
                errs() << "Track:\n";
                for (Function *F : vecTracker) {
                    errs() << "\t";
                    errs().write_escaped(F->getName()) << "\n";
                    printDebugInfo(F->getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
                }
            }
        }
        return true;
    }

    static bool isHandOverHandMutex(Function *F) {
        return F->getName().startswith("_ZN13servo_remutex17HandOverHandMutex5owner17h");
    }

    static bool isProtected(Instruction *UnprotectedCellCallInst, std::set<BasicBlock *> &setBranchBBs,
                            ControlDependenceGraphBase &CDG) {
        for (User *U : UnprotectedCellCallInst->users()) {
            if (Instruction *I = dyn_cast<Instruction>(U)) {
                if (isCallOrInvokeInst(I)) {
                    CallSite CS(I);
                    if (Function *F = CS->getFunction()) {
                        if (F->getName() == "sem_post" || F->getName() == "sem_wait") {
                            return true;
                        }
                    }
                }
            }
        }
        bool Influenced = false;
        for (BasicBlock *BranchBB : setBranchBBs) {
            if (CDG.influences(BranchBB, UnprotectedCellCallInst->getParent())) {
                Influenced = true;
                break;
            }
        }
        return Influenced;
    };

    static bool isLockFunc(Function *F) {
        if (!F) {
            return false;
        }
        StringRef Name = F->getName();
        // Check Mutex
        if (Name.find("mutex") != StringRef::npos || Name.find("Mutex") != StringRef::npos) {
            if (Name.find("raw_mutex") != StringRef::npos || Name.find("RawMutex") != StringRef::npos) {
                return false;
            } else if (Name.find("GT$4lock") != StringRef::npos) {
                return true;
            }
        } else if (Name.find("rwlock") != StringRef::npos || Name.find("RwLock") != StringRef::npos) {
            if (Name.startswith("HandyRwLock$LT$T$GT$$GT$2rl")
                || Name.startswith("HandyRwLock$LT$T$GT$$GT$2wl")) {
                return true;
            } else if (Name.find("raw_rwlock") != StringRef::npos || Name.find("RawRwLock") != StringRef::npos) {
                return false;
            } else if (Name.find("$GT$4read") != StringRef::npos || Name.find("$GT$5write") != StringRef::npos) {
                return true;
            }
        }
        return false;
    }

    static bool isAutoDropAPI(StringRef FuncName) {
        return FuncName.startswith("_ZN4core3ptr18real_drop_in_place17h");
    }

    static bool isManualDropAPI(StringRef FuncName) {
        return FuncName.startswith("_ZN4core3mem4drop17h");
    }

    static bool isProtectedByMutex(Instruction *CellAPI, Instruction *MutexAPI, std::set<Instruction *> &setDropAPI) {
        std::list<BasicBlock *> WorkList;
        std::set<BasicBlock *> Visited;
        std::set<BasicBlock *> setDropBB;
        for (Instruction *I : setDropAPI) {
            setDropBB.insert(I->getParent());
        }
        BasicBlock *CellBB = CellAPI->getParent();
        WorkList.push_back(CellAPI->getParent());
        Visited.insert(CellAPI->getParent());

        while (!WorkList.empty()) {
            BasicBlock *Curr = WorkList.front();
            WorkList.pop_front();
            if (Curr == CellBB) {
                return true;
            }
        }
        return false;
    }

    bool NewCellIMDetector::runOnModule(Module &M) {
        std::set<Function *> setCellIMFunc;
        std::set<Function *> setAtomicFunc;
        std::set<Function *> setHandOverHandFunc;
        std::set<Function *> setCellPossibleIMFunc;
        std::set<Function *> setSemaphoreFunc;

        for (Function &F : M) {
            if (isCellIMFunc(&F)) {
                setCellIMFunc.insert(&F);
            } else if (isAtomicAPI(&F)) {
                setAtomicFunc.insert(&F);
            } else if (isHandOverHandMutex(&F)) {
                setHandOverHandFunc.insert(&F);
            } else if (isCellPossbileIMFunc(&F)) {
//                setCellPossibleIMFunc.insert(&F);
            } else if (isSemaphoreIMFunc(&F)) {
                setSemaphoreFunc.insert(&F);
            }
        }

        std::map<Function *, std::set<Instruction *>> mapCalleeCallSites;
        for (Function &F : M) {
            if (F.begin() == F.end()) {
                continue;
            }
            for (BasicBlock &B : F) {
                for (Instruction &I : B) {
                    if (skipInst(&I)) {
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

        std::map<Function *, std::set<Instruction *>> mapAtomicCallerCallSites;
        for (Function *F : setAtomicFunc) {
            for (Instruction *I : mapCalleeCallSites[F]) {
                Function *Caller = I->getFunction();
                mapAtomicCallerCallSites[Caller].insert(I);
            }
        }

//        std::map<Function *, std::set<Instruction *>> mapCallerBranchInsts;
//        for (auto &kv : mapAtomicCallerCallSites) {
//            for (Instruction *AtomicCallInst : kv.second) {
//                collectBranchForAtomicCall(AtomicCallInst, mapCallerBranchInsts[kv.first]);
//            }
//        }

        std::map<Function *, std::set<Instruction *>> mapSemaphoreCallerCallSites;
        for (Function *F : setSemaphoreFunc) {
            for (Instruction *I: mapCalleeCallSites[F]) {
                mapSemaphoreCallerCallSites[I->getFunction()].insert(I);
            }
        }

        std::map<Function *, std::set<Instruction *>> mapHandOverHandMutexCallerCallSites;
        for (Function *F : setHandOverHandFunc) {
            for (Instruction *I : mapCalleeCallSites[F]) {
                Function *Caller = I->getFunction();
                mapHandOverHandMutexCallerCallSites[Caller].insert(I);
            }
        }

        std::map<Function *, std::set<BasicBlock *>> mapCallerBranchBBs;
        for (auto &kv : mapSemaphoreCallerCallSites) {
            for (Instruction *SemaphoreCallInst : kv.second) {
                for (User *U : SemaphoreCallInst->users()) {
                    if (Instruction *I = dyn_cast<Instruction>(U)) {
                        mapCallerBranchBBs[kv.first].insert(I->getParent());
                    }
                }
            }
        }
        for (auto &kv : mapAtomicCallerCallSites) {
            for (Instruction *AtomicCallInst : kv.second) {
                for (User *U : AtomicCallInst->users()) {
                    if (Instruction *I = dyn_cast<Instruction>(U)) {
                        mapCallerBranchBBs[kv.first].insert(I->getParent());
                    }
                }
            }
        }

        for (auto &kv : mapHandOverHandMutexCallerCallSites) {
            for (Instruction *HandOverhandMutexCallInst : kv.second) {
                for (User *U : HandOverhandMutexCallInst->users()) {
                    if (Instruction *I = dyn_cast<Instruction>(U)) {
                        mapCallerBranchBBs[kv.first].insert(I->getParent());
                        for (User *U2 : I->users()) {
                            if (Instruction *I2 = dyn_cast<Instruction>(U2)) {
                                mapCallerBranchBBs[kv.first].insert(I2->getParent());
                                for (User *U3 : I2->users()) {
                                    if (Instruction *I3 = dyn_cast<Instruction>(U3)) {
                                       mapCallerBranchBBs[kv.first].insert(I3->getParent());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        std::set<Instruction *> setUnprotectedCellAPICallSites;
        std::list<Instruction *> WorkList;
        std::set<Instruction *> Visited;
        for (Function *F : setCellIMFunc) {
            for (Instruction *CI : mapCalleeCallSites[F]) {
                WorkList.push_back(CI);
                Visited.insert(CI);
            }
        }
        for (Function *F : setCellPossibleIMFunc) {
            for (Instruction *CI : mapCalleeCallSites[F]) {
                if(isWriteOrEscape(CI)) {
                    WorkList.push_back(CI);
                    Visited.insert(CI);
                }
            }
        }
        while (!WorkList.empty()) {
            Instruction *CurrInst = WorkList.front();
            WorkList.pop_front();
            Function *CurrFunc = CurrInst->getFunction();
            PostDominatorTree *PDT = &getAnalysis<PostDominatorTreeWrapperPass>(*CurrFunc).getPostDomTree();
            auto ItCallerBranchBB = mapCallerBranchBBs.find(CurrFunc);
            if (ItCallerBranchBB != mapCallerBranchBBs.end()) {
                ControlDependenceGraphBase CDG;
                CDG.graphForFunction(*CurrFunc, *PDT);
                if (isProtected(CurrInst, ItCallerBranchBB->second, CDG)) {
//                    errs() << CurrFunc->getName() << "\n";
//                    printDebugInfo(CurrFunc->getEntryBlock().getFirstNonPHIOrDbgOrLifetime());
//                    errs() << "Protected:\n";
//                    CurrInst->print(errs());
//                    errs() << "\n";
                    continue;
                }
            }
            setUnprotectedCellAPICallSites.insert(CurrInst);
            auto IterCallSites = mapCalleeCallSites.find(CurrFunc);
            if (IterCallSites == mapCalleeCallSites.end()) {
                continue;
            }
            for (Instruction *CI : IterCallSites->second) {
                if (Visited.find(CI) != Visited.end()) {
                    continue;
                }
                WorkList.push_back(CI);
//                setUnprotectedCellAPICallSites.insert(CI);
                Visited.insert(CI);
            }
        }

        std::set<Function *> setUnprotectedCellAPICallers;
        for (Instruction *I : setUnprotectedCellAPICallSites) {
//            if (isWriteOrEscape(I)) {
            if (mapHandOverHandMutexCallerCallSites.find(I->getFunction()) != mapHandOverHandMutexCallerCallSites.end()) {
                errs() << "Protected by Mutex\n";
                continue;
            }
            setUnprotectedCellAPICallers.insert(I->getFunction());
//            }
        }

        errs() << "# of Unprotected Cell API Callers: " << setUnprotectedCellAPICallers.size() << "\n";
        for (Function *F : setUnprotectedCellAPICallers) {
            errs().write_escaped(F->getName()) << "\n";
            Instruction *PrintInst = F->getEntryBlock().getFirstNonPHIOrDbgOrLifetime();
            while (!printDebugInfo(PrintInst)) {
                PrintInst = PrintInst->getNextNode();
            }
        }
        return false;
    }

}  // namespace detector


static RegisterPass<detector::NewCellIMDetector> X(
        "detect",
        "Detect Cell-based Interior Mutability",
        false,
        true);
