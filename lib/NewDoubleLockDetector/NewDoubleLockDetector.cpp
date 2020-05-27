#include "NewDoubleLockDetector/NewDoubleLockDetector.h"

#include <set>
#include <stack>

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "NewDoubleLockDetector"

using namespace llvm;

namespace detector {

    char NewDoubleLockDetector::ID = 0;

    NewDoubleLockDetector::NewDoubleLockDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializeAAResultsWrapperPassPass(Registry);
    }

    void NewDoubleLockDetector::getAnalysisUsage(AnalysisUsage &AU) const {
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
                } else if (F->getName().startswith("_ZN4core3mem4drop17h")) {
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
            I->print(errs());
            errs() << '\n';
            if (isFuncUnwrap(I)) {
                for (auto NU = I->user_begin(); NU != I->user_end(); ++NU) {
                    (*NU)->print(errs());
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

    static bool isLocalCrateInst(Instruction *I) {
        const llvm::DebugLoc &lockInfo = I->getDebugLoc();
        auto di = lockInfo.get();
        if (di) {
            if (lockInfo->getDirectory() == "") {
                return false;
            } else {
                return true;
            }
        } else {
            return false;
        }
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

    // bool operator<(const MutexSource& lhs, const MutexSource& rhs) {
    //     if (lhs.direct == rhs.direct) {
    //         return false;
    //     }
    //     if ((unsigned long)lhs.structTy < (unsigned long)rhs.structTy) {
    //         return true;
    //     } else if ((unsigned long)lhs.structTy > (unsigned long)rhs.structTy) {
    //         return false;
    //     } else {
    //         if (lhs.index.size() < rhs.index.size()) {
    //             return true;
    //         } else if (lhs.index.size() > rhs.index.size()) {
    //             return false;
    //         } else {
    //             for (std::size_t i = 0; i < lhs.index.size(); ++i) {
    //                 if (lhs.index[i] < rhs.index[i]) {
    //                     return true;
    //                 }
    //             }
    //             return false;
    //         }
    //     }
    // }

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
                //    errs() << "index: ";
                   APInt idx = dyn_cast<ConstantInt>(GEP->getOperand(i))->getValue();
                   MS.index.push_back(idx);
                //    GEP->getOperand(i)->getType()->print(errs());
                //    errs() << "\n";
                //    GEP->getOperand(i)->print(errs());
                //    errs() << "\n";
               }
                return true;
            } else if (BitCastOperator *BCO = dyn_cast<BitCastOperator>(it->get())) {
                // TODO;
                Value *Self = BCO->getOperand(0);
                Type *structTy = Self->stripPointerCasts()->getType()->getContainedType(0);
//                structTy->print(errs());
//                errs() << "\n";
                if (!isa<StructType>(structTy)) {
//                    errs() << "Self not Struct" << "\n";
                    continue;
                }
                MS.structTy = structTy;
                return true;
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

    static bool isLockFunc(Function *F) {
        if (!F) {
            return false;
        }
        StringRef Name = F->getName();
        // Check Mutex
        if (Name.find("mutex") != StringRef::npos || Name.find("Mutex") != StringRef::npos) {
            if (Name.find("raw_mutex") != StringRef::npos|| Name.find("RawMutex") != StringRef::npos) {
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

    struct stLockInfo {
        Instruction *LockInst;
        Value *ReturnValue;
        Value *LockValue;
    };

    static bool parseLockInst(Instruction *LockInst, stLockInfo &LockInfo) {
        if (!LockInst) {
            return false;
        }
        CallSite CS(LockInst);
        // Mutex
        if (CS.getCalledFunction()->getReturnType()->isVoidTy()) {
            if (CS.getNumArgOperands() > 1) {
                LockInfo.ReturnValue = CS.getArgOperand(0);
                LockInfo.LockValue = CS.getArgOperand(1);
                return true;
            } else {
                errs() << "Void-return Lock\n";
                LockInst->print(errs());
                errs() << "\n";
                return false;
            }
        } else {  // Non-mutex
            LockInfo.ReturnValue = LockInst;
            if (CS.getNumArgOperands() > 0) {
                LockInfo.LockValue = CS.getArgOperand(0);
                return true;
            } else {
                errs() << "Non-parameter Lock\n";
                LockInst->print(errs());
                errs() << "\n";
                return false;
            }
        }
    }

    static bool trackDownToDropInsts(Instruction *RI, std::set<Instruction *> &setDropInst) {
        if (!RI) {
            return false;
        }
        errs() << "LockInst:\n";
        RI->print(errs());
        errs() << "\n";
        setDropInst.clear();

        std::list<Instruction *> WorkList;
        std::set<Instruction *> Visited;
        WorkList.push_back(RI);
        bool Stop = false;
        while (!WorkList.empty() && !Stop) {
            Instruction *Curr = WorkList.front();
            WorkList.pop_front();
            for (User *U: Curr->users()) {
                if (Instruction *UI = dyn_cast<Instruction>(U)) {
                    if (Visited.find(UI) == Visited.end()) {
                        if (isDropInst(UI)) {
                            errs() << "DropInst\n";
                           UI->print(errs());
                           errs() << '\n';
                            setDropInst.insert(UI);
                            Value *V = UI->getOperand(0);
                            assert(V);
                            for (User *UV: V->users()) {
                                if (Instruction *UVI = dyn_cast<Instruction>(UV)) {
                                    if (Visited.find(UVI) == Visited.end()) {
                                        if (isDropInst(UVI)) {
                                            setDropInst.insert(UVI);
                                        }
                                    }
                                }
                            }
                            return true;
                        } else if (StoreInst *SI = dyn_cast<StoreInst>(UI)) {
                            if (Instruction *Dest = dyn_cast<Instruction>(SI->getPointerOperand())) {
                                WorkList.push_back(Dest);
                            } else {
                                errs() << "StoreInst Dest is not a Inst\n";
                                printDebugInfo(Curr);
                            }
                        } else if (LoadInst *LI = dyn_cast<LoadInst>(UI)) {
                            errs() << "LoadInst:\n";
                            for (User *UV: LI->users()) {
                                if (Instruction *UVI = dyn_cast<Instruction>(UV)) {
                                    if (isDropInst(UVI)) {
                                        setDropInst.insert(UVI);
                                    }
                                }
                                Value *V = UI->getOperand(0);
                                assert(V);
                                for (User *UV2: V->users()) {
                                    if (Instruction *UVI2 = dyn_cast<Instruction>(UV2)) {
                                        if (Visited.find(UVI2) == Visited.end()) {
                                            if (isDropInst(UVI2)) {
                                                setDropInst.insert(UVI2);
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            WorkList.push_back(UI);
                        }
                        Visited.insert(UI);
                    }
                }
            }
        }
        return false;
    }

    static bool parseFunc(Function *F,
            std::map<Instruction *, Function *> &mapCallInstCallee,
            std::map<Instruction *, stLockInfo> &mapLockInfo,
            std::map<Instruction *, std::pair<Function *, std::set<Instruction *>>> &mapLockDropInfo) {
        if (!F || F->isDeclaration()) {
            return false;
        }

        for (BasicBlock &BB : *F) {
            for (Instruction &II : BB) {
                Instruction *I = &II;
                if (!skipInst(I)) {
                    if (!isLocalCrateInst(I)) {
                        continue;
                    }
                    if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
                        CallSite CS(I);
                        Function *Callee = CS.getCalledFunction();
                        if (Callee && !Callee->isDeclaration()) {
                            if (isLockFunc(Callee)) {
                                stLockInfo LockInfo { nullptr, nullptr, nullptr };
                                if (!parseLockInst(I, LockInfo)) {
                                    errs() << "Cannot Parse Lock Inst\n";
                                    printDebugInfo(I);
                                    continue;
                                }
                                Instruction *RI = dyn_cast<Instruction>(LockInfo.ReturnValue);
                                if (!RI) {
                                    errs() << "Return Value is not Inst\n";
                                    LockInfo.ReturnValue->print(errs());
                                    errs() << '\n';
                                    continue;
                                }
                                mapLockInfo[I] = LockInfo;
                                std::set<Instruction *> setDropInst;
                                if (trackDownToDropInsts(RI, setDropInst)) {
                                    mapLockDropInfo[I] = std::make_pair(Callee, setDropInst);
//                                    // Debug
//                                    I->print(errs());
//                                    errs() << '\n';
//                                    for (Instruction *DropInst: setDropInst) {
//                                        errs() << '\t';
//                                        DropInst->print(errs());
//                                        errs() << '\n';
//                                    }
                                } else {
                                    errs() << "Cannot find Drop for Inst:\n";
                                    errs() << I->getParent()->getParent()->getName() << '\n';
                                    I->print(errs());
                                    printDebugInfo(I);
                                    errs() << '\n';
                                    mapLockDropInfo[I] = std::make_pair(Callee, setDropInst);
                                }

                            } else {
                                mapCallInstCallee[I] = Callee;
                            }
                        }
                    }
                }
            }
        }

        return true;
    }


    static bool trackCallee(Instruction *LockInst,
            std::pair<Instruction *, Function *> &DirectCalleeSite,
            std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallees,
            std::map<Function *, std::set<Instruction *>> &mapAliasFuncLock) {

        bool HasDoubleLock = false;

        Function *DirectCallee = DirectCalleeSite.second;

        if (mapAliasFuncLock.find(DirectCallee) != mapAliasFuncLock.end()) {
            HasDoubleLock = true;
            errs() << "Double Lock Happens! First Lock:\n";
            printDebugInfo(LockInst);
            errs() << DirectCallee->getName() << '\n';
            // Debug Require
            LockInst->print(errs());
            errs() << '\n';
            printDebugInfo(DirectCalleeSite.first);
            errs() << "Second Lock(s):\n";
            for (Instruction *AliasLock : mapAliasFuncLock[DirectCallee]) {
                printDebugInfo(AliasLock);
                AliasLock->print(errs());
                errs() << '\n';
            }
            errs() << '\n';
        }

        std::stack<Function *> WorkList;
        std::set<Function *> Visited;

        std::map<Function *, Instruction *> mapParentInst;

        WorkList.push(DirectCallee);
        Visited.insert(DirectCallee);

        mapParentInst[DirectCallee] = DirectCalleeSite.first;

        while (!WorkList.empty()) {
            Function *Curr = WorkList.top();
            WorkList.pop();
//            errs() << Curr->getName() << '\n';
            auto itCallerCallInst = mapCallerCallees.find(Curr);
            if (itCallerCallInst != mapCallerCallees.end()) {
//                errs() << "Caller Found\n";
                std::map<Instruction *, Function *> &mapCallInstCallee = itCallerCallInst->second;
                for (auto &CallInstCallee : mapCallInstCallee) {
                    Instruction *CallInst = CallInstCallee.first;
                    Function *Callee = CallInstCallee.second;
//                    errs() << "Callee Found " << Callee->getName() << '\n';
                    if (Visited.find(Callee) == Visited.end()) {
//                        errs() << "Not Visited\n";
                        if (mapAliasFuncLock.find(Callee) != mapAliasFuncLock.end()) {
                            errs() << "Double Lock Happens! First Lock:\n";
                            errs() << LockInst->getParent()->getParent()->getName() << '\n';
                            printDebugInfo(LockInst);
                            LockInst->print(errs());
                            errs() << '\n';
                            errs() << Callee->getName() << '\n';
                            errs() << "Second Lock(s):\n";
                            for (Instruction *AliasLock : mapAliasFuncLock[Callee]) {
                                printDebugInfo(AliasLock);
                                LockInst->print(errs());
                                errs() << '\n';
                            }
                            errs() << '\n';
                            // backtrace print
                            mapParentInst[Callee] = CallInst;
                            std::set<Function *> TraceVisited;
                            auto it = mapParentInst.find(Callee);
                            while (it != mapParentInst.end()) {
                                Instruction *ParentInst = it->second;
                                printDebugInfo(ParentInst);
                                errs() << ParentInst->getParent()->getName() << ": ";
                                ParentInst->print(errs());
                                errs() << '\n';
                                Function *ParentFunc = ParentInst->getParent()->getParent();
                                it = mapParentInst.find(ParentFunc);
                                if (it != mapParentInst.end()) {
                                    if (TraceVisited.find(it->first) != TraceVisited.end()) {
                                        break;
                                    } else {
                                        TraceVisited.insert(it->first);
                                    }
                                }
                            }
                            // end of backtrack
                            HasDoubleLock = true;
                        }
                        WorkList.push(Callee);
                        mapParentInst[Callee] = CallInst;
                        Visited.insert(Callee);
                    }
                }
            }
        }

        return HasDoubleLock;
    }

    static bool trackCalleeDepracated(Instruction *LockInst,
            std::set<Instruction *> &setMayAliasLock,
            std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallees) {

        std::stack<Function *> WorkList;
        std::set<Function *> Visited;

//        std::map<Instruction *, Instruction *> Parents;

        Function *LockResideFunc = LockInst->getParent()->getParent();
        WorkList.push(LockResideFunc);
        Visited.insert(LockResideFunc);
        bool StopPropagation = false;
        while (!WorkList.empty()) {
            Function *Curr = WorkList.top();
            WorkList.pop();
            auto itCallInstCallee = mapCallerCallees.find(Curr);
            for (BasicBlock &BB : *Curr) {
                for (Instruction &II : BB) {
                    Instruction *I = &II;
                    if (setMayAliasLock.find(I) != setMayAliasLock.end()) {
                        errs() << "Double Lock Happens! First Lock:\n";
                        printDebugInfo(LockInst);
                        errs() << "Second Lock(s):\n";
                        printDebugInfo(I);
                        // Debug, Required
                        // LockInst->print(errs());
                        // errs() << '\n';
                        StopPropagation = true;
                    } else if (itCallInstCallee != mapCallerCallees.end()) {
                        std::map<Instruction *, Function *> &mapCallInstCallee = itCallInstCallee->second;
                        auto it = mapCallInstCallee.find(I);
                        if (it != mapCallInstCallee.end()) {
                            if (Visited.find(it->second) == Visited.end()) {
                                WorkList.push(it->second);
                            }
                        }
                    }
                }
            }
        }

        return StopPropagation;
    }

    static bool trackLockInst(Instruction *LockInst,
            std::set<Instruction *> setMayAliasLock,
            std::set<Instruction *> setDrop,
            std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallees) {

//        std::set<Function *> setMayAliasFunc;
//        for (Instruction *I : setMayAliasLock) {
//            if (I != LockInst) {
//                setMayAliasFunc.insert(I->getParent()->getParent());
//            }
//        }
        std::map<Function *, std::set<Instruction *>> mapMayAliasFuncLock;
        for (Instruction *I : setMayAliasLock) {
            if (I != LockInst) {
                Function *AliasFunc = I->getParent()->getParent();
                mapMayAliasFuncLock[AliasFunc].insert(I);
            }
        }
//        // Debug
//        printDebugInfo(LockInst);
//        for (Function *F : setMayAliasFunc) {
//            errs() << F->getName() << '\n';
//        }
        std::stack<BasicBlock *> WorkList;
        std::set<BasicBlock *> Visited;

        Function *Caller = LockInst->getParent()->getParent();
        auto &mapCallInstCallee = mapCallerCallees[Caller];

//        // Debug
//        for (auto &kv : mapCallInstCallee) {
//            kv.first->print(errs());
//            errs() << '\n';
//        }

        WorkList.push(LockInst->getParent());
        Visited.insert(LockInst->getParent());
        while (!WorkList.empty()) {
            BasicBlock *Curr = WorkList.top();
            WorkList.pop();
            bool StopPropagation = false;
            for (Instruction &II: *Curr) {
                Instruction *I = &II;
                // contains same Lock
                if (setMayAliasLock.find(I) != setMayAliasLock.end()) {
                    errs() << "Double Lock Happens! First Lock:\n";
                    printDebugInfo(LockInst);
                    errs() << "Second Lock(s):\n";
                    printDebugInfo(I);
                    // Debug Require
                    // LockInst->print(errs());
                    errs() << '\n';
                    StopPropagation = true;
                    // break;
                } else if (setDrop.find(I) != setDrop.end()) {
                    // contains same Drop
                    StopPropagation = true;
                    break;
                } else {
                    // is a CallInst
                    auto it = mapCallInstCallee.find(I);
                    if (it == mapCallInstCallee.end()) {
                        continue;
                    } else {
                        Instruction *CI = it->first;
                        Function *Callee = it->second;
//                        errs() << Callee->getName() << "\n";
                        auto CalleeSite = std::make_pair(CI, Callee);
//                        if (trackCallee(LockInst, CalleeSite, mapCallerCallees, setMayAliasFunc)) {
//                            StopPropagation = true;
//                            break;
//                        }
                        if (trackCallee(LockInst, CalleeSite, mapCallerCallees, mapMayAliasFuncLock)) {
                            StopPropagation = true;
                            break;
                        }
                    }
                }
            }

            if (!StopPropagation) {
                Instruction *pTerm = Curr->getTerminator();
                for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
                    BasicBlock *Succ = pTerm->getSuccessor(i);
                    if (Visited.find(Succ) == Visited.end()) {
                        WorkList.push(Succ);
                        Visited.insert(Succ);
                    }
                }
            }
        }

        return true;
    }

    bool NewDoubleLockDetector::runOnModule(Module &M) {
        this->pModule = &M;

        std::map<Instruction *, Function *> mapCallInstCallee;
        std::map<Instruction *, stLockInfo> mapLockInfo;
        std::map<Instruction *, std::pair<Function *, std::set<Instruction *>>> mapLockDropInfo;

        for (Function &F: M) {
            parseFunc(&F, mapCallInstCallee, mapLockInfo, mapLockDropInfo);
        }

        std::map<Type *, std::map<Instruction *, stLockInfo>> mapMayAliasLock;
        for (auto &InstLI: mapLockInfo) {
            Type *Ty = InstLI.second.LockValue->getType();
            if (!Ty) {
                errs() << "Cannot get Type of LockValue of Inst\n";
                printDebugInfo(InstLI.first);
                continue;
            }
            mapMayAliasLock[Ty][InstLI.first] = InstLI.second;
        }

        // std::map<MutexSource, std::map<Instruction *, stLockInfo>> mapStructAliasLock;
        // for (auto &kv : mapMayAliasLock) {
        //     for (auto &kv2 : kv.second) {
        //         MutexSource MS;
        //         kv2.first
        //     }
        // }

//        // Debug
//        for (auto &TyLI : mapMayAliasLock) {
//            errs() << "Type: ";
//            TyLI.first->print(errs());
//            errs() << '\n';
////            if (TyLI.second.size() <= 1) {
////                continue;
////            }
//            for (auto &LI : TyLI.second) {
//                errs() << '\t';
//                LI.first->print(errs());
//                errs() << '\n';
//                printDebugInfo(LI.first);
//                StringRef Name = LI.first->getParent()->getParent()->getName();
//                errs() << Name << "\n";
////                if (Name.contains("closure")) {
////                    errs() << "Double Lock Might Happens!\n";
////                }
//            }
//        }

        std::map<Function *, std::map<Instruction *, Function *>> mapCallerCallee;
        for (auto &CallInstCallee : mapCallInstCallee) {
            Instruction *CI = CallInstCallee.first;
            Function *F = CallInstCallee.second;
            Function *Caller = CI->getParent()->getParent();
            mapCallerCallee[Caller][CI] = F;
        }

        for (auto &TyResult: mapMayAliasLock) {
            for (auto &InstLI : TyResult.second) {
                Instruction *LockInst = InstLI.first;
                std::set<Instruction *> setMayAliasLock;
                for (auto &OtherInstLI : TyResult.second) {
                    if (OtherInstLI.first != LockInst) {
                        setMayAliasLock.insert(OtherInstLI.first);
                    }
                }

                std::set<Instruction *> setLockDrop;
                if (mapLockDropInfo.find(LockInst) != mapLockDropInfo.end()) {
                    for (Instruction *DropInst : mapLockDropInfo[LockInst].second) {
                        setLockDrop.insert(DropInst);
                    }
                }

                trackLockInst(LockInst, setMayAliasLock, setLockDrop, mapCallerCallee);
            }
        }

        return false;
    }

}  // namespace detector

static RegisterPass<detector::NewDoubleLockDetector> X(
        "detect",
        "Detect Double Lock",
        false,
        true);
