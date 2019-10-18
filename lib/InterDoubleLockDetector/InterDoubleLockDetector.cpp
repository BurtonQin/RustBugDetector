#include "InterDoubleLockDetector/InterDoubleLockDetector.h"

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "InterDoubleLockDetector"

using namespace llvm;

namespace detector {

    char InterDoubleLockDetector::ID = 0;

    InterDoubleLockDetector::InterDoubleLockDetector() : ModulePass(ID) {}

    void InterDoubleLockDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<AAResultsWrapperPass>();
    }

    struct LockInfo {
        Value *result;
        Value *mutex;

        LockInfo() : result(nullptr), mutex(nullptr) {
        }
    };

    static bool isFuncUnwrap(Instruction *I) {
        if (isCallOrInvokeInst(I)) {
            CallSite CS;
            if (Function *F = getCalledFunc(I, CS)) {
                if (F->getName().startswith("_ZN4core6result19Result$LT$T$C$E$GT$6unwrap")) {
                    return true;
                } else if (F->getName().startswith("_ZN4core6result19Result$LT$T$C$E$GT$6expect")) {
                    return true;
                }
            }
        }
        return false;
    }

    static bool handleStdMutexLock(Instruction *I, LockInfo &LI) {
        CallSite CS(I);
        if (CS.getNumArgOperands() < 2) {
            return false;
        }
        LI.result = CS.getArgOperand(0);
        LI.mutex = CS.getArgOperand(1);
        return true;
    }

    static bool handleStdWriteLock(Instruction *I, LockInfo &LI) {
        CallSite CS(I);
        if (CS.getNumArgOperands() < 2) {
            return false;
        }
        LI.result = CS.getArgOperand(0);
        LI.mutex = CS.getArgOperand(1);
        return true;
    }

    static bool handleStdReadLock(Instruction *I, LockInfo &LI) {
        CallSite CS(I);
        if (CS.getNumArgOperands() < 1) {
            return false;
        }
        for (auto it = I->user_begin(); it != I->user_end(); ++it) {
            if (isa<ExtractValueInst>(*it)) {
                for (auto it2 = (*it)->user_begin(); it2 != (*it)->user_end(); ++it2) {
                    if (Instruction *UI = dyn_cast<Instruction>(*it2)) {
                        if (isFuncUnwrap(UI)) {
                            LI.result = UI;
                            break;
                        }
                    }
                }
            }
        }
        if (!LI.result) {
            LI.result = I;
        }
        LI.mutex = CS.getArgOperand(0);
        return true;
    }

    static bool handleLockAPIMutexLock(Instruction *I, LockInfo &LI) {
        CallSite CS(I);
        if (CS.getNumArgOperands() < 1) {
            return false;
        }
        Value *V = CS.getArgOperand(0);
        LI.result = I;
        LI.mutex = V;
        return true;
    }

    static bool findAllLocks(Function *F, std::map<Instruction *, LockInfo> &mapLockInfo) {
        for (BasicBlock &BI : *F) {
            for (Instruction &II : BI) {
                Instruction *I = &II;
                if (isCallOrInvokeInst(I)) {
                    CallSite CS;
                    if (Function *Callee = getCalledFunc(I, CS)) {
                        StringRef Name = Callee->getName();
                        if (Name.startswith("_ZN8lock_api5mutex18Mutex$LT$R$C$T$GT$4lock")) {
//                            I->print(errs());
//                            errs() << "\n";
                            LockInfo LI;
                            if (handleLockAPIMutexLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.startswith("_ZN11parking_lot6rwlock15RwLock$LT$T$GT$4read")) {
                            LockInfo LI;
                            if (handleLockAPIMutexLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.startswith("_ZN11parking_lot6rwlock15RwLock$LT$T$GT$5write")) {
                            LockInfo LI;
                            if (handleLockAPIMutexLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.startswith("_ZN3std4sync5mutex14Mutex$LT$T$GT$4lock")) {
//                            I->print(errs());
//                            errs() << "\n";
                            LockInfo LI;
                            if (handleStdMutexLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$4read")) {
//                            I->print(errs());
//                            errs() << "\n";
                            LockInfo LI;
                            if (handleStdReadLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$5write")) {
//                            I->print(errs());
//                            errs() << "\n";
                            LockInfo LI;
                            if (handleStdWriteLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("HandyRwLock$LT$T$GT$$GT$2wl") != std::string::npos) {
                            LockInfo LI;
                            if (handleStdWriteLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("HandyRwLock$LT$T$GT$$GT$2rl") != std::string::npos) {
                            LockInfo LI;
                            if (handleStdReadLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("_ZN9tokio_net6driver14sharded_rwlock15RwLock$LT$T$GT$4read") != std::string::npos) {
                            LockInfo LI;
                            if (handleStdReadLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("_ZN9tokio_net6driver14sharded_rwlock15RwLock$LT$T$GT$5write") != std::string::npos) {
                            LockInfo LI;
                            if (handleStdWriteLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("_ZN10tokio_sync4mpsc5block14Block$LT$T$GT$4read") != std::string::npos) {
                            LockInfo LI;
                            if (handleStdReadLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("_ZN10tokio_sync4mpsc5block14Block$LT$T$GT$5write") != std::string::npos) {
                            LockInfo LI;
                            if (handleStdWriteLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("_ZN17crossbeam_channel5utils17Spinlock$LT$T$GT$4lock") != std::string::npos) {
                            LockInfo LI;
                            if (handleLockAPIMutexLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("_ZN16len_caching_lock5mutex24LenCachingMutex$LT$T$GT$4lock") != std::string::npos) {
                            LockInfo LI;
                            if (handleLockAPIMutexLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        } else if (Name.find("_ZN8lock_api5mutex18Mutex$LT$R$C$T$GT$4lock") != std::string::npos) {
                            LockInfo LI;
                            if (handleLockAPIMutexLock(I, LI)) {
                                mapLockInfo[I] = LI;
                            }
                        }
                    }
                }
            }
        }
        return !mapLockInfo.empty();
    }

    static bool getAliasedLocks(AliasAnalysis &AA,
                                std::map<Instruction *, LockInfo> &mapLockInfo,
                                std::map<Instruction *, std::set<Instruction *>> &mapAliasLock,
                                std::map<Instruction *, std::set<BasicBlock *>> &mapAliasLockBB) {

        std::map<Instruction *, std::set<Instruction *>> mapLocalAliasLock;
        std::map<Instruction *, std::set<BasicBlock *>> mapLocalAliasLockBB;
        for (auto &kv : mapLockInfo) {
            mapAliasLock[kv.first] = std::set<Instruction *>();
            mapAliasLockBB[kv.first] = std::set<BasicBlock *>();
            for (auto &kv2 : mapLockInfo) {
                if (kv.first == kv2.first) {
                    continue;
                }
                auto result = AA.alias(kv.second.mutex, kv2.second.mutex);
                if (result == AliasResult::MustAlias) {
                    mapAliasLock[kv.first].insert(kv2.first);
                    mapAliasLockBB[kv.first].insert(kv2.first->getParent());
                }
            }
        }
        for (auto &kv: mapLocalAliasLock) {
            if (!kv.second.empty()) {
                mapAliasLock[kv.first] = kv.second;
            }
        }
        for (auto &kv: mapLocalAliasLockBB) {
            if (!kv.second.empty()) {
                mapAliasLockBB[kv.first] = kv.second;
            }
        }
        return !mapAliasLock.empty();
    }

    static bool isDropInst(Instruction *NI) {
        if (isCallOrInvokeInst(NI)) {
            CallSite CS;
            if (Function *F = getCalledFunc(NI, CS)) {
                if (F->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                    return true;
                }
            }
        }
        return false;
    }

    static bool trackStore(Value *V, std::set<Instruction *> &setDropInst) {
        if (StoreInst *SI = dyn_cast<StoreInst>(V)) {
//            errs() << "Track Store:\n";
//            SI->print(errs());
//            errs() << '\n';
            Value *Next = SI->getOperand(1);
            for (auto NU = Next->user_begin(); NU != Next->user_end(); ++NU) {
                Instruction *NI = dyn_cast<Instruction>(*NU);
//                NI->print(errs());
//                errs() << '\n';
                if (isDropInst(NI)) {
                    setDropInst.insert(NI);
                }
            }
        } else if (Instruction *II = dyn_cast<Instruction>(V)) {
            if (isDropInst(II)) {
                setDropInst.insert(II);
                return true;
            } else {
//                errs() << "Not Store\n";
//                II->print(errs());
//                errs() << '\n';
            }
        } else {
//            errs() << "Not Store\n";
//            II->print(errs());
//            errs() << '\n';
        }
        return !setDropInst.empty();
    }

    static bool trackResult(Value *result, std::set<Instruction *> &setDropInst) {
        for (auto U = result->user_begin(); U != result->user_end(); ++U) {
            Value *V = *U;
            Instruction *I = dyn_cast<Instruction>(V);
//            I->print(errs());
//            errs() << '\n';
            if (isFuncUnwrap(I)) {
                for (auto NU = I->user_begin(); NU != I->user_end(); ++NU) {
//                    (*NU)->print(errs());
                    std::set<Instruction *> setLocalDropInst;
                    if (trackStore(*NU, setLocalDropInst)) {
                        setDropInst.insert(setLocalDropInst.begin(), setLocalDropInst.end());
                    }
                }
            } else {
                std::set<Instruction *> setLocalDropInst;
                if (trackStore(V, setLocalDropInst)) {
                    setDropInst.insert(setLocalDropInst.begin(), setLocalDropInst.end());
                }
            }
        }
        return !setDropInst.empty();
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

    struct MutexSource {
        Value *direct;
        Type *structTy;
        std::vector<APInt> index;

        MutexSource() : direct(nullptr), structTy(nullptr), index(std::vector<APInt>()) {
        }
    };

    bool operator==(const MutexSource& lhs, const MutexSource& rhs) {
        if (lhs.direct == rhs.direct) {
            return true;
        }
        if (lhs.structTy != rhs.structTy) {
            return false;
        }
        if (lhs.index.size() != rhs.index.size()) {
            return false;
        }
        for (std::size_t i = 0; i < lhs.index.size(); ++i) {
            if (lhs.index[i] != rhs.index[i]) {
                return false;
            }
        }
        return true;
    }

    static bool trackMutexToSelf(Value *mutex, MutexSource &MS) {
        if (!mutex) {
            return false;
        }
        MS.direct = mutex;
        for (auto it = mutex->use_begin(); it != mutex->use_end(); ++it) {
            if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(it->get())) {
                Value *Self = GEP->getOperand(0);
                Type *structTy = Self->stripPointerCasts()->getType()->getContainedType(0);
//                structTy->print(errs());
//                errs() << "\n";
                if (!isa<StructType>(structTy)) {
//                    errs() << "Self not Struct" << "\n";
                    continue;
                }
                MS.structTy = structTy;
//                Self->print(errs());
//                errs() << "\n";
                for (unsigned i = 1; i < GEP->getNumOperands(); ++i) {
//                    errs() << "index: ";
                    APInt idx = dyn_cast<ConstantInt>(GEP->getOperand(i))->getValue();
                    MS.index.push_back(idx);
//                    GEP->getOperand(i)->getType()->print(errs());
//                    errs() << "\n";
//                    GEP->getOperand(i)->print(errs());
//                    errs() << "\n";
                }
                return true;
            } else if (BitCastInst *BCI = dyn_cast<BitCastInst>(it->get())) {
                errs() << "BitCast\n";
                BCI->print(errs());
                Value *V = BCI->getOperand(0);
                if (V) {
                    V->print(errs());
                    Instruction *Deref = dyn_cast<Instruction>(V);
                    if (Deref) {
                        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(it->get())) {
                            Value *Self = GEP->getOperand(0);
                            Type *structTy = Self->stripPointerCasts()->getType()->getContainedType(0);
                            errs() << "Struct Type:\n";
                structTy->print(errs());
                errs() << "\n";
                            if (!isa<StructType>(structTy)) {
                    errs() << "Self not Struct" << "\n";
                                continue;
                            }
                            MS.structTy = structTy;
                            return true;
                        }
                    } else {
                        if (Deref->getNumOperands() > 1) {
                            Value *PossibleGEP = Deref->getOperand(0);
                            if (PossibleGEP) {
                                if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(it->get())) {
                                    Value *Self = GEP->getOperand(0);
                                    Type *structTy = Self->stripPointerCasts()->getType()->getContainedType(0);
                                    errs() << "Struct Type:\n";
                                    structTy->print(errs());
                                    errs() << "\n";
                                    if (!isa<StructType>(structTy)) {
//                    errs() << "Self not Struct" << "\n";
                                        continue;
                                    }
                                    MS.structTy = structTy;
                                    return true;
                                }
                            }
                        }
                    }
                }
                return false;
            }
        }
        return false;
    }

    static void trackBBForDirectFn(BasicBlock *B, std::set<Function *> &DirectCallees) {
        for (Instruction &II : *B) {
            Instruction *I = &II;
            if (isCallOrInvokeInst(I)) {
                CallSite CS;
                Function *F = getCalledFunc(I, CS);
                if (F) {
                    DirectCallees.insert(F);
                }
            }
        }
    }

    static void trackCallerCallees(Module &M, std::map<Function *, std::set<Function *>> &mapCallerCallees,
            std::map<Function *, std::map<Instruction *, Function *>> &mapCallInsts) {
        for (Function &F: M) {
            for (BasicBlock &B : F) {
                for (Instruction &I : B) {
                    if (isCallOrInvokeInst(&I)) {
                        CallSite CS;
                        Function *Callee = getCalledFunc(&I, CS);
                        if (Callee) {
                            mapCallerCallees[&F].insert(Callee);
                            mapCallInsts[&F][&I] = Callee;
                        }
                    }
                }
            }
        }
    }

    static void trackRecurCallees(Function *Caller, const std::map<Function *, std::set<Function *>> &mapCallerCallees,
            std::set<Function *> &Visited, std::map<Function *, Function *> &Parents) {
        std::list<Function *> WorkList;
        WorkList.push_back(Caller);
        while (!WorkList.empty()) {
            Function *Curr = WorkList.front();
            WorkList.pop_front();
            auto it = mapCallerCallees.find(Curr);
            if (it != mapCallerCallees.end()) {
                for (Function *Callee: it->second) {
                    if (Visited.find(Callee) == Visited.end()) {
                        WorkList.push_back(Callee);
                        Visited.insert(Callee);
                        Parents[Callee] = Curr;
                    }
                }
            }
        }
    }

    static bool trackBBForDoubleLock(BasicBlock *B, std::map<Function *, std::set<Function *>> &mapCallerCallees, const std::set<Function *> &setShareLockFn, std::set<Function *> &setDoubleLockFn, std::map<Function *, std::vector<Function *>> &CallChain) {
        std::set<Function *> DirectCallees;
        trackBBForDirectFn(B, DirectCallees);
        for (Function *Callee: DirectCallees) {
            if (setShareLockFn.find(Callee) != setShareLockFn.end()) {
                setDoubleLockFn.insert(Callee);
            }
        }
        std::set<Function *> Visited;
        std::map<Function *, Function *> Parents;
        for (Function *Callee: DirectCallees) {
            trackRecurCallees(Callee, mapCallerCallees, Visited, Parents);
            Parents[Callee] = B->getParent();
//            errs() << "Parents\n";
//            for (auto &kv: Parents) {
//                errs() << kv.first->getName() << " -> " << kv.second->getName() << '\n';
//            }
//            errs() << "End of Parents\n";
        }
        for (Function *Callee: Visited) {
            if (setShareLockFn.find(Callee) != setShareLockFn.end()) {
                setDoubleLockFn.insert(Callee);
//                errs() << "Callee\n";
//                errs() << Callee->getName() << '\n';
//                errs() << Parents[Callee]->getName() << '\n';
//                errs() << "Parents\n";
//                for (auto &kv: Parents) {
//                    errs() << kv.first << " -> " << kv.second << '\n';
//                }
//                errs() << "End of Parents\n";
                auto it = Parents.find(Callee);
                std::set<Function *> localVisited;
                while (it != Parents.end() && localVisited.find(it->second) == localVisited.end()) {
//                    errs() << "Track: " << it->second->getName() << '\n';
                    CallChain[Callee].push_back(it->second);
                    localVisited.insert(it->second);
                    it = Parents.find(it->second);
                }
            }
        }
        return !setDoubleLockFn.empty();
    }

    struct FnLockMatch {
        Function *F;
        MutexSource MS;
    };

    bool InterDoubleLockDetector::runOnModule(Module &M) {
        this->pModule = &M;

        std::map<Function *, std::set<Function *>> mapCallerCallees;
        std::map<Function *, std::map<Instruction *, Function *>> mapCallInsts;
        trackCallerCallees(M, mapCallerCallees, mapCallInsts);

//        for (const auto &kv: mapCallerCallees) {
//            errs() << kv.first->getName() << '\n';
//            for (Function *F : kv.second) {
//                errs() << '\t' << F->getName() << '\n';
//            }
//        }

//        Function *Caller = M.getFunction("_ZN11double_lock5Miner10lock_first17hf8cb7f51cb321f9aE");
//        errs() << Caller->getName() << "\n";
//        std::set<Function *> setRecurCallees;
//        trackRecurCallees(Caller, mapCallerCallees, setRecurCallees);
//        for (Function *F: setRecurCallees) {
//            errs() << '\t' << F->getName() << '\n';
//        }

        std::vector<MutexSource> vecMS;
        std::map<Instruction *, MutexSource> mapLockInstMutexSource;
        std::map<Function *, std::map<Instruction *, std::set<Instruction *>>> mapAllAliasLock;
        std::map<Function *, std::map<Instruction *, std::set<BasicBlock *>>> mapAllAliasLockBB;
        std::map<Function *, std::map<Instruction *, std::set<BasicBlock *>>> mapAllDropBB;

        std::map<Function *, std::map<Instruction *, std::set<BasicBlock *>>> mapLockProtectedBB;

        for (Function &FI: M) {
            if (FI.isDeclaration()) {
                continue;
            }
            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(FI).getAAResults();
            Function *F = &FI;
            std::map<Instruction *, LockInfo> mapLockInfo;
            bool ContainLock = findAllLocks(F, mapLockInfo);
            if (ContainLock) {
//                errs() << F->getName() << " contains lock\n";
                MutexSource MS;
                for (auto &kv : mapLockInfo) {
                    if (trackMutexToSelf(kv.second.mutex, MS)) {
                        vecMS.push_back(MS);
                        mapLockInstMutexSource[kv.first] = MS;
                    } else {
                        errs() << "Cannot Track to Self\n";
                        if (Instruction *I = dyn_cast<Instruction>(kv.second.mutex)) {
                            I->print(errs());
                            printDebugInfo(I);
                            errs() << '\n';
                        }
                    }
                }
                std::map<Instruction *, std::set<Instruction *>> mapAliasLock;
                std::map<Instruction *, std::set<BasicBlock *>> mapAliasLockBB;
                std::map<Instruction *, std::set<BasicBlock *>> mapDropBB;
                getAliasedLocks(AA, mapLockInfo, mapAliasLock, mapAliasLockBB);
                {
                    //errs() << "\nFuncName:" << F->getName() << "\n";
                    for (auto &kv : mapAliasLock) {
//                        if (kv.second.empty()) {
//                            continue;
//                        }
//                        Instruction *LockInst = kv.first;
//                        LockInst->print(errs());
//                        errs() << "\n Alias with \n";
//                        for (Instruction *I : kv.second) {
//                            errs() << '\t';
//                            I->print(errs());
//                            errs() << '\n';
//                        }
                        std::set<Instruction *> setDropInst;
                        trackResult(mapLockInfo[kv.first].result, setDropInst);
//                        errs() << "Drop: ";
//                        for (Instruction *dropInst : setDropInst) {
//                            dropInst->print(errs());
//                            errs() << "\n";
//                        }
//                        errs() << '\n';
                        if (!setDropInst.empty()) {
                            std::set<BasicBlock *> setDropBB;
                            for (Instruction *dropInst : setDropInst) {
                                setDropBB.insert(dropInst->getParent());
                            }
                            mapDropBB[kv.first] = setDropBB;
                        }
                    }

                    mapAllAliasLock[F] = mapAliasLock;
                    mapAllAliasLockBB[F] = mapAliasLockBB;
                    mapAllDropBB[F] = mapDropBB;
                }
//                for (auto &kv : mapAliasLockBB) {
//                    kv.first->print(errs());
//                    errs() << "\n";
//                    errs() << "Alias\n";
//                    for (BasicBlock *AB: kv.second) {
//                        errs() << AB->getName() << '\n';
//                    }
//                    errs() << "Drop\n";
//                    for (BasicBlock *DB: mapDropBB[kv.first]) {
//                        errs() << DB->getName() << '\n';
//                    }
//                }

                for (auto &kv : mapAliasLockBB) {
                    Instruction *LockInst = kv.first;
                    std::set<BasicBlock *> &AliasedLockBB = kv.second;
                    std::set<Instruction *> &AliasedLockInst = mapAliasLock[LockInst];
                    std::set<BasicBlock *> &DropBB = mapDropBB[LockInst];
                    std::list<BasicBlock *> WorkList;
                    std::set<BasicBlock *> Visited;
                    WorkList.push_back(LockInst->getParent());
                    while (!WorkList.empty()) {
                        BasicBlock *B = WorkList.front();
                        WorkList.pop_front();
                        auto itAlias = AliasedLockBB.find(B);
                        if (itAlias != AliasedLockBB.end()) {
                            errs() << "Double Lock Happens!" << "\n";
                            printDebugInfo(LockInst);
                            errs() << B->getName() << "\n";
                            for (Instruction *ALI : AliasedLockInst) {
                                if (ALI->getParent() == B) {
                                    printDebugInfo(ALI);
                                }
                            }
                            break;
                        }
                        auto itDrop = DropBB.find(B);
                        if (itDrop != DropBB.end()) {
                            continue;
                        } else {
                            Instruction *pTerm = B->getTerminator();
                            for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
                                BasicBlock *Succ = pTerm->getSuccessor(i);
                                if (Visited.find(Succ) == Visited.end()) {
                                    WorkList.push_back(Succ);
                                    Visited.insert(Succ);
                                }
                            }
                        }
                    }
                }
            }
        }

//        errs() << "mapLockProtectedBB\n";
//        for (const auto &kv: mapLockProtectedBB) {
//            errs() << kv.first->getName() << '\n';
//            for (const auto &kv2 : kv.second) {
//                kv2.first->print(errs());
//                errs() << '\n';
//                for (BasicBlock *B : kv2.second) {
//                    errs() << B->getName() << '\n';
//                }
//            }
//        }
//        errs() << "End of mapLockProtectedBB\n";

        errs() << "Mutex Source\n";
        std::map<Function *, std::vector<FnLockMatch>> mapFnLock;
        for (std::size_t i = 0; i < vecMS.size(); ++i) {
            for (std::size_t j = i+1; j < vecMS.size(); ++j) {
                if (vecMS[i] == vecMS[j]) {
                    Function *F1 = nullptr;
                    Function *F2 = nullptr;
                    if (vecMS[i].direct && vecMS[j].direct) {
                        Instruction *I = dyn_cast<Instruction>(vecMS[i].direct);
                        if (I) {
                            F1 = I->getParent()->getParent();
                            errs() << F1->getName() << '\n';
                        }
                        Instruction *J = dyn_cast<Instruction>(vecMS[j].direct);
                        if (J) {
                            F2 = J->getParent()->getParent();
                            errs() << F2->getName() << '\n';
                        }
                        mapFnLock[F1].push_back(FnLockMatch {F2, vecMS[i]});
                        mapFnLock[F2].push_back(FnLockMatch {F1, vecMS[j]});
                    }
                    errs() << '\n';
                }
            }
        }
//        for (auto &kv: mapFnLock) {
//            errs() << kv.first->getName() << " match with \n";
//            errs() << (*kv.second.begin()).F->getName() << '\n';
//        }

        // std::map<Function *, std::set<Function *>> mapDoubleLock;
        for (auto &kv1: mapFnLock) {
            Function *F = kv1.first;
            std::set<Function *> setSharedLockFn;
            for (auto& Match : kv1.second) {
                setSharedLockFn.insert(Match.F);
            }
            std::set<Function *> setDoubleLockFn;
            std::map<Function *, std::map<Function *, std::vector<Function *>>> CallChain;
            if (mapLockProtectedBB.find(F) != mapLockProtectedBB.end()) {
                Value *V = (*kv1.second.begin()).MS.direct;
                if (V) {
                    Instruction *I = dyn_cast<Instruction>(V);
                    if (I) {
//                        errs() << "Conflict Inst:\n";
//                        I->print(errs());
//                        errs() << "\n";
                        Instruction *LockInst = nullptr;
                        for (auto &kv : mapLockInstMutexSource) {
                            if (kv.second.direct == I) {
                                LockInst = kv.first;
                                break;
                            }
                        }
                        for (BasicBlock *B : mapLockProtectedBB[F][LockInst]) {
//                            errs() << B->getName() << '\n';
                            trackBBForDoubleLock(B, mapCallerCallees, setSharedLockFn, setDoubleLockFn, CallChain[F]);
                        }
                        if (!setDoubleLockFn.empty()) {
                            errs() << "Double Lock Happens!";
                            errs() << kv1.first->getName() << '\n';
                            printDebugInfo(LockInst);
                            errs() << "With Func: \n";
                            for (Function *FD: setDoubleLockFn) {
                                errs() << FD->getName() << '\n';
                                errs() << "Trace:" << '\n';

                                Function *Parent = F;
                                for (auto rit = CallChain[kv1.first][FD].rbegin(); rit != CallChain[kv1.first][FD].rend(); ++rit) {
                                    errs() << '\t' << (*rit)->getName() << '\n';
                                    for (auto &iterInstCall : mapCallInsts[Parent]) {
                                        if (iterInstCall.second == *rit) {
                                            printDebugInfo(iterInstCall.first);
                                        }
                                        Parent = *rit;
                                    }
                                }
//                                auto it = CallChain[kv1.first][FD].begin();
                            }
                        }
                    }
                }
            }
        }

        return false;
    }

//    bool InterDoubleLockDetector::runOnModule(Module &M) {
//
//        std::vector<MutexSource> vecMS;
//        std::map<Function *, std::map<Instruction *, std::set<Instruction *>>> mapAllAliasLock;
//        std::map<Function *, std::map<Instruction *, std::set<BasicBlock *>>> mapAllAliasLockBB;
//        std::map<Function *, std::map<Instruction *, std::set<BasicBlock *>>> mapAllDropBB;
//
//        for (Function &FI: M) {
//            if (FI.isDeclaration()) {
//                continue;
//            }
//            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(FI).getAAResults();
//            Function *F = &FI;
//            std::map<Instruction *, LockInfo> mapLockInfo;
//            bool ContainLock = findAllLocks(F, mapLockInfo);
//            if (ContainLock) {
//                errs() << F->getName() << " contains lock\n";
//                MutexSource MS;
//                for (auto &kv : mapLockInfo) {
//                    if (trackMutexToSelf(kv.second.mutex, MS)) {
//                        vecMS.push_back(MS);
//                    }
//                }
//                std::map<Instruction *, std::set<Instruction *>> mapAliasLock;
//                std::map<Instruction *, std::set<BasicBlock *>> mapAliasLockBB;
//                std::map<Instruction *, std::set<BasicBlock *>> mapDropBB;
//                if (getAliasedLocks(AA, mapLockInfo, mapAliasLock, mapAliasLockBB)) {
//                    //errs() << "\nFuncName:" << F->getName() << "\n";
//                    for (auto &kv : mapAliasLock) {
//                        if (kv.second.empty()) {
//                            continue;
//                        }
////                        Instruction *LockInst = kv.first;
////                        LockInst->print(errs());
////                        errs() << "\n Alias with \n";
////                        for (Instruction *I : kv.second) {
////                            errs() << '\t';
////                            I->print(errs());
////                            errs() << '\n';
////                        }
//                        std::set<Instruction *> setDropInst;
//                        trackResult(mapLockInfo[kv.first].result, setDropInst);
////                        errs() << "Drop: ";
////                        for (Instruction *dropInst : setDropInst) {
////                            dropInst->print(errs());
////                            errs() << "\n";
////                        }
////                        errs() << '\n';
//                        if (!setDropInst.empty()) {
//                            std::set<BasicBlock *> setDropBB;
//                            for (Instruction *dropInst : setDropInst) {
//                                setDropBB.insert(dropInst->getParent());
//                            }
//                            mapDropBB[kv.first] = setDropBB;
//                        }
//                    }
//
//                    mapAllAliasLock[F] = mapAliasLock;
//                    mapAllAliasLockBB[F] = mapAliasLockBB;
//                    mapAllDropBB[F] = mapDropBB;
//                }
////                for (auto &kv : mapAliasLockBB) {
////                    kv.first->print(errs());
////                    errs() << "\n";
////                    errs() << "Alias\n";
////                    for (BasicBlock *AB: kv.second) {
////                        errs() << AB->getName() << '\n';
////                    }
////                    errs() << "Drop\n";
////                    for (BasicBlock *DB: mapDropBB[kv.first]) {
////                        errs() << DB->getName() << '\n';
////                    }
////                }
//
//                for (auto &kv : mapAliasLockBB) {
//                    Instruction *LockInst = kv.first;
//                    std::set<BasicBlock *> &AliasedLockBB = kv.second;
//                    std::set<Instruction *> &AliasedLockInst = mapAliasLock[LockInst];
//                    std::set<BasicBlock *> &DropBB = mapDropBB[LockInst];
//                    std::list<BasicBlock *> WorkList;
//                    std::set<BasicBlock *> Visited;
//                    WorkList.push_back(LockInst->getParent());
//                    while (!WorkList.empty()) {
//                        BasicBlock *B = WorkList.front();
//                        WorkList.pop_front();
//                        auto itAlias = AliasedLockBB.find(B);
//                        if (itAlias != AliasedLockBB.end()) {
//                            errs() << "Double Lock Happens!" << "\n";
//                            printDebugInfo(LockInst);
//                            errs() << B->getName() << "\n";
//                            for (Instruction *ALI : AliasedLockInst) {
//                                if (ALI->getParent() == B) {
//                                    printDebugInfo(ALI);
//                                }
//                            }
//                            break;
//                        }
//                        auto itDrop = DropBB.find(B);
//                        if (itDrop != DropBB.end()) {
//                            continue;
//                        } else {
//                            Instruction *pTerm = B->getTerminator();
//                            for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
//                                BasicBlock *Succ = pTerm->getSuccessor(i);
//                                if (Visited.find(Succ) == Visited.end()) {
//                                    WorkList.push_back(Succ);
//                                    Visited.insert(Succ);
//                                }
//                            }
//                        }
//                    }
//                }
//            }
//        }
//
//        std::map<Function *, std::vector<FnLockMatch>> mapFnLock;
//        for (std::size_t i = 0; i < vecMS.size(); ++i) {
//            for (std::size_t j = i+1; j < vecMS.size(); ++j) {
//                if (vecMS[i] == vecMS[j]) {
//                    Function *F1 = nullptr;
//                    Function *F2 = nullptr;
//                    if (vecMS[i].direct && vecMS[j].direct) {
//                        Instruction *I = dyn_cast<Instruction>(vecMS[i].direct);
//                        if (I) {
//                            F1 = I->getParent()->getParent();
//                            errs() << F1->getName() << '\n';
//                        }
//                        Instruction *J = dyn_cast<Instruction>(vecMS[j].direct);
//                        if (J) {
//                            F2 = J->getParent()->getParent();
//                            errs() << F2->getName() << '\n';
//                        }
//                        mapFnLock[F1].push_back(FnLockMatch {F2, vecMS[i]});
//                        mapFnLock[F2].push_back(FnLockMatch {F1, vecMS[j]});
//                    }
//                    errs() << '\n';
//                }
//            }
//        }
//        for (auto &kv: mapFnLock) {
//            errs() << kv.first->getName() << " match with \n";
//            errs() << (*kv.second.begin()).F->getName() << '\n';
//        }
//
//
//
//        for (auto &kv : mapFnLock) {
//            auto itAliasInst = mapAllAliasLock.find(F);
//            if (itAliasInst != mapAllAliasLock.end()) {
//                auto &mapAliasLock = *itAliasInst;
//                auto &mapAliasLockBB = mapAllAliasLockBB[F];
//                auto &mapDropBB = mapAllDropBB[F];
//
//                for (auto &kvBB : mapAliasLockBB) {
//                    Instruction *LockInst = kvBB.first;
//                    std::set<BasicBlock *> &AliasedLockBB = kvBB.second;
//                    std::set<Instruction *> &AliasedLockInst = mapAliasLock[LockInst];
//                    std::set<BasicBlock *> &DropBB = mapDropBB[LockInst];
//                    std::list<BasicBlock *> BBWorkList;
//                    std::set<BasicBlock *> BBVisited;
//                    WorkList.push_back(LockInst->getParent());
//                    while (!WorkList.empty()) {
//                        BasicBlock *B = WorkList.front();
//                        WorkList.pop_front();
//                        auto itAlias = AliasedLockBB.find(B);
//                        if (itAlias != AliasedLockBB.end()) {
//                            errs() << "Double Lock Happens!" << "\n";
//                            printDebugInfo(LockInst);
//                            errs() << B->getName() << "\n";
//                            for (Instruction *ALI : AliasedLockInst) {
//                                if (ALI->getParent() == B) {
//                                    printDebugInfo(ALI);
//                                }
//                            }
//                            break;
//                        }
//                        auto itDrop = DropBB.find(B);
//                        if (itDrop != DropBB.end()) {
//                            continue;
//                        } else {
//                            Instruction *pTerm = B->getTerminator();
//                            for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
//                                BasicBlock *Succ = pTerm->getSuccessor(i);
//                                if (Visited.find(Succ) == Visited.end()) {
//                                    WorkList.push_back(Succ);
//                                    Visited.insert(Succ);
//                                }
//                            }
//                        }
//                    }
//                }
//            }
//
//        }
//        return false;
//    }
}  // namespace detector

static RegisterPass<detector::InterDoubleLockDetector> X(
        "detect",
        "Detect Double Lock",
        false,
        true);
