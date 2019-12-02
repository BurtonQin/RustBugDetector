#include "SameLockInSameFuncDetector/SameLockInSameFuncDetector.h"

#include <set>
#include <stack>

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/ValueTracking.h"

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "SameLockInSameFuncDetector"

using namespace llvm;

namespace detector {

    char SameLockInSameFuncDetector::ID = 0;

    SameLockInSameFuncDetector::SameLockInSameFuncDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializeAAResultsWrapperPassPass(Registry);
    }

    void SameLockInSameFuncDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<AAResultsWrapperPass>();
    }

    static bool printDebugInfo(Instruction *I) {
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

//    static bool trackMutexToSelf(Value *mutex, MutexSource &MS) {
//        if (!mutex) {
//            return false;
//        }
//        MS.direct = mutex;
//        for (auto it = mutex->use_begin(); it != mutex->use_end(); ++it) {
//            if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(it->get())) {
//                Value *Self = GEP->getOperand(0);
//                Type *structTy = Self->stripPointerCasts()->getType()->getContainedType(0);
////                structTy->print(errs());
////                errs() << "\n";
//                if (!isa<StructType>(structTy)) {
////                    errs() << "Self not Struct" << "\n";
//                    continue;
//                }
//                MS.structTy = structTy;
////                Self->print(errs());
////                errs() << "\n";
////                for (unsigned i = 1; i < GEP->getNumOperands(); ++i) {
////                    errs() << "index: ";
////                    APInt idx = dyn_cast<ConstantInt>(GEP->getOperand(i))->getValue();
////                    MS.index.push_back(idx);
////                    GEP->getOperand(i)->getType()->print(errs());
////                    errs() << "\n";
////                    GEP->getOperand(i)->print(errs());
////                    errs() << "\n";
////                }
//                return true;
//            } else if (BitCastInst *BCI = dyn_cast<BitCastInst>(it->get())) {
//                // TODO;
//                return false;
//            }
//        }
//        return false;
//    }

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
//                            UI->print(errs());
//                            errs() << '\n';
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
                    if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
                        CallSite CS(I);
                        Function *Callee = CS.getCalledFunction();
                        if (Callee && !Callee->isDeclaration()) {
                            if (isLockFunc(Callee)) {
                                stLockInfo LockInfo{nullptr, nullptr, nullptr};
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

    enum class LockShareType {
        SharedLock = 0,
        ExclusiveLock = 1,
    };

    struct ResultLockInfo {
        Value *ResultValue;
        Value *LockValue;
        LockShareType LockType;
        bool Wrapped;
    };

    // std::sync::Mutex::lock()
    // _ZN3std4sync5mutex14Mutex$LT$T$GT$4lock17h(Result<MutexGuard, PoisonError>, Mutex) -> void
    static bool parseStdSyncMutexLock(Instruction *LockInst, ResultLockInfo &LI) {
        if (!LockInst) {
            return false;
        }
        CallSite CS(LockInst);
        if (CS.getNumArgOperands() < 2) {
            return false;
        }
        LI.ResultValue = CS.getArgOperand(0);
        LI.LockValue = CS.getArgOperand(1);
        LI.LockType = LockShareType::ExclusiveLock;
        LI.Wrapped = true;
        return true;
    }

    // std::sync::RwLock::read()
    // _ZN3std4sync6rwlock15RwLock$LT$T$GT$4read17h(RwLock) -> Result<RwLockReadGuard, PoisonError>
    static bool parseStdSyncRwLockRead(Instruction *LockInst, ResultLockInfo &LI) {
        if (!LockInst) {
            return false;
        }
        CallSite CS(LockInst);
        if (CS.getNumArgOperands() < 1) {
            return false;
        }
        LI.ResultValue = LockInst;
        LI.LockValue = CS.getArgOperand(0);
        LI.LockType = LockShareType::SharedLock;
        LI.Wrapped = true;
        return true;
    }

    // std::sync::RwLock::write()
    // _ZN3std4sync6rwlock15RwLock$LT$T$GT$5write17h(Result<RwLockReadGuard, PoisonError>, RwLock) -> void
    static bool parseStdSyncRwLockWrite(Instruction *LockInst, ResultLockInfo &LI) {
        if (!LockInst) {
            return false;
        }
        CallSite CS(LockInst);
        if (CS.getNumArgOperands() < 2) {
            return false;
        }
        LI.ResultValue = CS.getArgOperand(0);
        LI.LockValue = CS.getArgOperand(1);
        LI.LockType = LockShareType::ExclusiveLock;
        LI.Wrapped = true;
        return true;
    }

    // parking_lot::Mutex::lock()
    // _ZN8lock_api5mutex18Mutex$LT$R$C$T$GT$4lock17h(Mutex) -> MutexGuard
    static bool parseParkingLotMutexLock(Instruction *LockInst, ResultLockInfo &LI) {
        if (!LockInst) {
            return false;
        }
        CallSite CS(LockInst);
        if (CS.getNumArgOperands() < 1) {
            return false;
        }
        LI.ResultValue = LockInst;
        LI.LockValue = CS.getArgOperand(0);
        LI.LockType = LockShareType::ExclusiveLock;
        LI.Wrapped = false;
        return true;
    }

    // parking_lot::RwLock::read()
    // _ZN8lock_api6rwlock19RwLock$LT$R$C$T$GT$4read17h(RwLock) -> RwLockReadGuard
    static bool parseParkingLotRwLockRead(Instruction *LockInst, ResultLockInfo &LI) {
        if (!LockInst) {
            return false;
        }
        CallSite CS(LockInst);
        if (CS.getNumArgOperands() < 1) {
            return false;
        }
        LI.ResultValue = LockInst;
        LI.LockValue = CS.getArgOperand(0);
        LI.LockType = LockShareType::ExclusiveLock;  // Two parking_lot::read() in one thread is not allowed
        LI.Wrapped = false;
        return true;
    }

    // parking_lot::RwLock::write()
    // _ZN8lock_api6rwlock19RwLock$LT$R$C$T$GT$5write17h(RwLock) -> RwLockWriteGuard
    static bool parseParkingLotRwLockWrite(Instruction *LockInst, ResultLockInfo &LI) {
        if (!LockInst) {
            return false;
        }
        CallSite CS(LockInst);
        if (CS.getNumArgOperands() < 1) {
            return false;
        }
        LI.ResultValue = LockInst;
        LI.LockValue = CS.getArgOperand(0);
        LI.LockType = LockShareType::SharedLock;
        LI.Wrapped = false;
        return true;
    }

    static bool dispatchLockInst(Instruction *I, ResultLockInfo &LI) {
        if (!isCallOrInvokeInst(I)) {
            return false;
        }
        CallSite CS(I);
        if (Function *F = getCalledFunc(I, CS)) {
            StringRef FuncName = F->getName();
            if (FuncName.startswith("_ZN3std4sync5mutex14Mutex$LT$T$GT$4lock17h")) {
                return parseStdSyncMutexLock(I, LI);
            } else if (FuncName.startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$4read17h")) {
                return parseStdSyncRwLockRead(I, LI);
            } else if (FuncName.startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$5write17h")) {
                return parseStdSyncRwLockWrite(I, LI);
            } else if (FuncName.startswith("_ZN8lock_api5mutex18Mutex$LT$R$C$T$GT$4lock17h")) {
                return parseParkingLotMutexLock(I, LI);
            } else if (FuncName.startswith("_ZN8lock_api6rwlock19RwLock$LT$R$C$T$GT$4read17h")) {
                return parseParkingLotRwLockRead(I, LI);
            } else if (FuncName.startswith("_ZN8lock_api6rwlock19RwLock$LT$R$C$T$GT$5write17h")) {
                return parseParkingLotRwLockWrite(I, LI);
            } else {
                return false;
            }
        }
        return false;
    }

    static bool isFuncUnwrap(Instruction *I) {
        if (isCallOrInvokeInst(I)) {
            CallSite CS;
            if (Function *F = getCalledFunc(I, CS)) {
                if (F->getName().startswith("_ZN4core6result19Result$LT$T$C$E$GT$6unwrap17h")) {
                    return true;
                } else if (F->getName().startswith("_ZN4core6result19Result$LT$T$C$E$GT$6expect17h")) {
                    return true;
                }
            }
        }
        return false;
    }

    enum class GuardDest {
        Unknown = 0,
        AutoDrop = 1,
        ManualDrop = 2,
        Return = 3,
        Move = 4,
    };

    static bool isResultToInnerAPI(StringRef FuncName) {
        return FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$6unwrap17h")
               || FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$9unwrap_or17h")
               || FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$14unwrap_or_else17h")
               || FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$17unwrap_or_default17h")
               || FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$6expect17h");
    }

    static bool isResultToResultAPI(StringRef FuncName) {
        return FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$7map_err17h")
               || FuncName.startswith(
                "_ZN73_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try..Try$GT$11into_result17h");
//        FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$3map17h") -> T->U
//        || FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$2ok17h") -> Option
    }

    static bool isAutoDropAPI(StringRef FuncName) {
        return FuncName.startswith("_ZN4core3ptr18real_drop_in_place17h");
    }

    static bool isManualDropAPI(StringRef FuncName) {
        return FuncName.startswith("_ZN4core3mem4drop17h");
    }

    static bool isDerefAPI(StringRef FuncName) {
        return FuncName.startswith(
                "_ZN81_$LT$std..sync..mutex..MutexGuard$LT$T$GT$$u20$as$u20$core..ops..deref..Deref$GT$5deref17h")
               || FuncName.startswith(
                "_ZN84_$LT$std..sync..mutex..MutexGuard$LT$T$GT$$u20$as$u20$core..ops..deref..DerefMut$GT$9deref_mut17h")
               || FuncName.startswith(
                "_ZN84_$LT$lock_api..mutex..MutexGuard$LT$R$C$T$GT$$u20$as$u20$core..ops..deref..Deref$GT$5deref17h")
               || FuncName.startswith(
                "_ZN87_$LT$lock_api..mutex..MutexGuard$LT$R$C$T$GT$$u20$as$u20$core..ops..deref..DerefMut$GT$9deref_mut17h")
               || FuncName.startswith(
                "_ZN88_$LT$std..sync..rwlock..RwLockWriteGuard$LT$T$GT$$u20$as$u20$core..ops..deref..Deref$GT$5deref17h")
               || FuncName.startswith(
                "_ZN91_$LT$std..sync..rwlock..RwLockWriteGuard$LT$T$GT$$u20$as$u20$core..ops..deref..DerefMut$GT$9deref_mut17h")
               || FuncName.startswith(
                "_ZN87_$LT$std..sync..rwlock..RwLockReadGuard$LT$T$GT$$u20$as$u20$core..ops..deref..Deref$GT$5deref17h")
               || FuncName.startswith(
                "_ZN90_$LT$std..sync..rwlock..RwLockReadGuard$LT$T$GT$$u20$as$u20$core..ops..deref..DerefMut$GT$9deref_mut17h")
               || FuncName.startswith(
                "_ZN90_$LT$lock_api..rwlock..RwLockReadGuard$LT$R$C$T$GT$$u20$as$u20$core..ops..deref..Deref$GT$5deref17h")
               || FuncName.startswith(
                "_ZN93_$LT$lock_api..rwlock..RwLockReadGuard$LT$R$C$T$GT$$u20$as$u20$core..ops..deref..DerefMut$GT$9deref_mut17h")
               || FuncName.startswith(
                "_ZN91_$LT$lock_api..rwlock..RwLockWriteGuard$LT$R$C$T$GT$$u20$as$u20$core..ops..deref..Deref$GT$5deref17h")
               || FuncName.startswith(
                "_ZN94_$LT$lock_api..rwlock..RwLockWriteGuard$LT$R$C$T$GT$$u20$as$u20$core..ops..deref..DerefMut$GT$9deref_mut17h");
    }

    enum class ResultState {
        WrappedInResult = 0,  // Init
        MovedToOtherInst = 1,
        Unwrapped = 2,  // Term
        AutoDropped = 3,  // Term
        ManualDropped = 4,  // Term
        MovedToOtherFunc = 5, // Term  // consider as unlock
        Returned = 6,  // Term
        Overwritten = 7,  // Term
        Unknown = 8  // Term
    };

    static bool getNextValueForResult(Use *InputUse, Value *&Output, ResultState &RS, const DataLayout &DL) {
        User *InputUser = InputUse->getUser();
        if (Instruction *I = dyn_cast<Instruction>(InputUser)) {
            if (isCallOrInvokeInst(I)) {
                CallSite CS;
                if (Function *F = getCalledFunc(I, CS)) {
                    StringRef FuncName = F->getName();
                    if (isResultToInnerAPI(FuncName)) {
                        if (F->getReturnType()->isVoidTy()) {
                            Output = GetUnderlyingObject(I->getOperand(0), DL);
                        } else {
                            Output = I;
                        }
                        RS = ResultState::Unwrapped;
                        return false;
                    } else if (isResultToResultAPI(FuncName)) {
//                        // Debug
//                        errs() << "Is Result To Result API\n";
//                        I->print(errs());
//                        errs() << "\n";
//                        printDebugInfo(I);
//                        errs().write_escaped(I->getFunction()->getName()) << "\n\n";
                        if (F->getReturnType()->isVoidTy()) {
                            Output = GetUnderlyingObject(I->getOperand(0), DL);
                        } else {
                            Output = I;
                        }
                        RS = ResultState::MovedToOtherInst;
                        return true;
                    } else if (isAutoDropAPI(FuncName)) {
                        Output = I;
                        RS = ResultState::AutoDropped;
                        return false;
                    } else if (isManualDropAPI(FuncName)) {
                        Output = I;
                        RS = ResultState::ManualDropped;
                        return false;
                    } else if (MemTransferInst *MI = dyn_cast<MemTransferInst>(I)) {
                        if (MI->getOperandUse(0) == *InputUse) {
                            Output = I;
                            RS = ResultState::Overwritten;
                            return false;
                        } else {
                            Output = GetUnderlyingObject(MI->getOperand(0), DL);
                            RS = ResultState::MovedToOtherInst;
                            return true;
                        }
                    } else if (isa<MemSetInst>(I)) {
                        Output = I;
                        RS = ResultState::Overwritten;
                        return false;
                    } else {
                        Output = I;
                        RS = ResultState::MovedToOtherFunc;
                        return false;
                    }
                } else {
                    Output = I;
                    RS = ResultState::MovedToOtherFunc;
                    return false;
                }
            } else if (isa<LoadInst>(I)) {
                Output = I;
                RS = ResultState::MovedToOtherInst;
                return true;
            } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                if (SI->getOperandUse(1) == *InputUse) {
                    Output = I;
                    RS = ResultState::Overwritten;
                    return false;
                } else {
                    Output = GetUnderlyingObject(SI->getOperand(1), DL);
                    RS = ResultState::MovedToOtherInst;
                    return true;
                }
            } else if (isa<InsertValueInst>(I)) {
                Output = I;
                RS = ResultState::MovedToOtherInst;
                return true;
            } else if (isa<CastInst>(I)) {
                Output = I;
                RS = ResultState::MovedToOtherInst;
                return true;
            } else if (isa<GetElementPtrInst>(I)) {
                Output = I;
                RS = ResultState::MovedToOtherInst;
                return true;
            } else if (isa<ExtractValueInst>(I)) {
                Output = I;
                RS = ResultState::MovedToOtherInst;
                return true;
            } else if (isa<ReturnInst>(I)) {
                Output = I;
                RS = ResultState::Returned;
                return false;
            } else {
                Output = I;
                RS = ResultState::Unknown;
                return false;
            }
        } else {
            Output = InputUser;
            RS = ResultState::Unknown;
            return false;
        }
    }

    static bool runFSMForResult(Value *ResultValue,
                                std::set<Value *> &setLockGuard,
                                std::set<Value *> &setAutoDrop,
                                std::set<Value *> &setManualDrop,
                                std::set<Value *> &setMovedToOtherFunc,
                                std::set<Value *> &setReturned,
                                std::set<Value *> &setOverwritten,
                                std::set<Value *> &setUnknown,
                                const DataLayout &DL) {

        Value *NextValue = ResultValue;
        std::list<Value *> WorkList;
        std::set<Value *> Visited;
        WorkList.push_back(NextValue);
        Visited.insert(NextValue);
        ResultState RS = ResultState::WrappedInResult;
//        errs() << "NextValue:\n";
//        NextValue->print(errs());
//        errs() << "\n";
        while (!WorkList.empty()) {
            NextValue = WorkList.front();
            WorkList.pop_front();
            if (User *NI = dyn_cast<User>(NextValue)) {
                for (Use &U : NI->uses()) {
                    Value *CurrNextValue = nullptr;
                    if (getNextValueForResult(&U, CurrNextValue, RS, DL)) {
                        if (Visited.find(CurrNextValue) == Visited.end()) {
                            WorkList.push_back(CurrNextValue);
                            Visited.insert(CurrNextValue);
                        }
                    } else {
                        if (RS == ResultState::Unwrapped) {
                            setLockGuard.insert(CurrNextValue);
                        } else if (RS == ResultState::AutoDropped) {
                            setAutoDrop.insert(CurrNextValue);
                        } else if (RS == ResultState::ManualDropped) {
                            setManualDrop.insert(CurrNextValue);
                        } else if (RS == ResultState::MovedToOtherFunc) {
                            setMovedToOtherFunc.insert(CurrNextValue);
                        } else if (RS == ResultState::Returned) {
                            setReturned.insert(CurrNextValue);
                        } else if (RS == ResultState::Overwritten) {
                            setOverwritten.insert(CurrNextValue);
                        } else if (RS == ResultState::Unknown) {
                            setUnknown.insert(CurrNextValue);
                        } else {
                            assert(false && "Cannot Reach to Result Parsing!");
                        }
                    }
                }
            }
        }
        return true;
    }

    enum class LockGuardState {
        Unwrapped = 0,  // Init
        MovedToOtherInst = 1,
        Dereferenced = 2,  // Term  // further drop not related
        AutoDropped = 3,  // Term
        ManualDropped = 4,  // Term
        MovedToOtherFunc = 5, // Term  // consider as unlock
        Returned = 6,  // Term
        Overwritten = 7,  // Term
        Unknown = 8  // Term
    };

    static bool getNextValueForLockGuard(Use *InputUse, Value *&Output, LockGuardState &LGS, const DataLayout &DL) {
        User *InputUser = InputUse->getUser();
        if (Instruction *I = dyn_cast<Instruction>(InputUser)) {
            if (isCallOrInvokeInst(I)) {
                CallSite CS;
                if (Function *F = getCalledFunc(I, CS)) {
                    StringRef FuncName = F->getName();
                    if (isAutoDropAPI(FuncName)) {
                        Output = I;
                        LGS = LockGuardState::AutoDropped;
                        return false;
                    } else if (isManualDropAPI(FuncName)) {
                        Output = I;
                        LGS = LockGuardState::ManualDropped;
                        return false;
                    } else if (isDerefAPI(FuncName)) {
                        if (F->getReturnType()->isVoidTy()) {
                            Output = GetUnderlyingObject(I->getOperand(0), DL);
                        } else {
                            Output = I;
                        }
                        LGS = LockGuardState::Dereferenced;
                        return false;
                    } else if (MemTransferInst *MI = dyn_cast<MemTransferInst>(I)) {
                        if (MI->getOperandUse(0) == *InputUse) {
                            Output = I;
                            LGS = LockGuardState::Overwritten;
                            return false;
                        } else {
                            Output = GetUnderlyingObject(MI->getOperand(0), DL);
                            LGS = LockGuardState::MovedToOtherInst;
                            return true;
                        }
                    } else if (isa<MemSetInst>(I)) {
                        Output = I;
                        LGS = LockGuardState::Overwritten;
                        return false;
                    } else {
                        Output = I;
                        errs() << "Moved to other func\n";
                        I->print(errs());
                        errs() << "\n";
                        printDebugInfo(I);
                        errs().write_escaped(I->getFunction()->getName()) << "\n\n";
                        LGS = LockGuardState::MovedToOtherFunc;
                        return false;
                    }
                } else {
                    Output = I;
                    LGS = LockGuardState::MovedToOtherFunc;
                    return false;
                }
            } else if (isa<LoadInst>(I)) {
                Output = I;
                LGS = LockGuardState::MovedToOtherInst;
                return true;
            } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                if (SI->getOperandUse(1) == *InputUse) {
                    Output = I;
                    LGS = LockGuardState::Overwritten;
                    return false;
                } else {
//                    SI->print(errs());
//                    errs() << "\n";
                    Output = GetUnderlyingObject(SI->getOperand(1), DL);
//                    errs() << "Stored Value\n";
//                    Output->print(errs());
//                    errs() << "\n";
                    LGS = LockGuardState::MovedToOtherInst;
                    return true;
                }
            } else if (isa<InsertValueInst>(I)) {
                Output = I;
                LGS = LockGuardState::MovedToOtherInst;
                return true;
            } else if (isa<CastInst>(I)) {
                Output = I;
                LGS = LockGuardState::MovedToOtherInst;
                return true;
            } else if (isa<GetElementPtrInst>(I)) {
                Output = I;
                LGS = LockGuardState::MovedToOtherInst;
                return true;
            } else if (isa<ExtractValueInst>(I)) {
                Output = I;
                LGS = LockGuardState::MovedToOtherInst;
                return true;
            } else if (isa<ReturnInst>(I)) {
                Output = I;
                LGS = LockGuardState::Returned;
                return false;
            } else {
                Output = I;
                LGS = LockGuardState::Unknown;
                return false;
            }
        } else {
            Output = InputUser;
            LGS = LockGuardState::Unknown;
            return false;
        }
    }

    static bool runFSMForLockGuard(Value *LockGuardValue,
                                   std::set<Value *> &setDeref,
                                   std::set<Value *> &setAutoDrop,
                                   std::set<Value *> &setManualDrop,
                                   std::set<Value *> &setMovedToOtherFunc,
                                   std::set<Value *> &setReturned,
                                   std::set<Value *> &setOverwritten,
                                   std::set<Value *> &setUnknown,
                                   const DataLayout &DL) {

        Value *NextValue = LockGuardValue;
        std::list<Value *> WorkList;
        std::set<Value *> Visited;
        WorkList.push_back(NextValue);
        Visited.insert(NextValue);
        LockGuardState LGS = LockGuardState::Unwrapped;
//        errs() << "NextValue:\n";
//        NextValue->print(errs());
//        errs() << "\n";
        while (!WorkList.empty()) {
            NextValue = WorkList.front();
            WorkList.pop_front();
            if (User *NI = dyn_cast<User>(NextValue)) {
                for (Use &U : NI->uses()) {
                    Value *CurrNextValue = nullptr;
                    if (getNextValueForLockGuard(&U, CurrNextValue, LGS, DL)) {
                        if (Visited.find(CurrNextValue) == Visited.end()) {
                            WorkList.push_back(CurrNextValue);
                            Visited.insert(CurrNextValue);
                        }
                    } else {
                        if (LGS == LockGuardState::Dereferenced) {
                            setDeref.insert(CurrNextValue);
                        } else if (LGS == LockGuardState::AutoDropped) {
                            setAutoDrop.insert(CurrNextValue);
                        } else if (LGS == LockGuardState::ManualDropped) {
                            setManualDrop.insert(CurrNextValue);
                        } else if (LGS == LockGuardState::MovedToOtherFunc) {
//                            errs() << "!!!Moved to Other Func\n";
//                            CurrNextValue->print(errs());
//                            errs() << "\n";
                            setMovedToOtherFunc.insert(CurrNextValue);
                        } else if (LGS == LockGuardState::Returned) {
                            setReturned.insert(CurrNextValue);
                        } else if (LGS == LockGuardState::Overwritten) {
                            setOverwritten.insert(CurrNextValue);
                        } else if (LGS == LockGuardState::Unknown) {
                            setUnknown.insert(CurrNextValue);
                        } else {
                            assert(false && "Cannot Reach to LockGuard Parsing!");
                        }
                    }
                }
            }
        }
        return true;
    }

    static bool collectGlobalCallSite(
            Function *F,  // Input
            std::map<Instruction *, Function *> &mapCallSite  // Output
        ) {
        if (!F || F->isDeclaration()) {
            return false;
        }
        for (BasicBlock &B : *F) {
            for (Instruction &II : B) {
                Instruction *I = &II;
                if (skipInst(I)) {
                    continue;
                }
                if (isCallOrInvokeInst(I)) {
                    CallSite CS;
                    if (Function *Callee = getCalledFunc(I, CS)) {
                        mapCallSite[I] = Callee;
                    }
                }
            }
        }
        return true;
    }

    struct stLockGenKillSet {
        ResultLockInfo RLI;  // Gen
        std::set<Value *> setLockGuard;  // Intermediate Info
        std::set<Value *> setResultAutoDrop;  // Kill
        std::set<Value *> setResultManualDrop;  // Kill
        std::set<Value *> setResultMovedToOtherFunc;  // Kill
        std::set<Value *> setResultReturned;  // To be handled
        std::set<Value *> setResultOverwritten;  // Cannot handle
        std::set<Value *> setResultUnknown;  // Cannot handle
        std::set<Value *> setLockGuardDeref;  // Intermediate Info
        std::set<Value *> setLockGuardAutoDrop;  // Kill
        std::set<Value *> setLockGuardManualDrop;  // Kill
        std::set<Value *> setLockGuardMovedToOtherFunc;  // Kill
        std::set<Value *> setLockGuardReturned;  // To be handled
        std::set<Value *> setLockGuardOverwritten;  // Cannot handle
        std::set<Value *> setLockGuardUnknown;  // Cannot handle
    };

    using LockGenKillInfoMapTy = std::map<Instruction *, stLockGenKillSet>;

    static void collectLockGenKillInfoForLock(Instruction *LockInst,  // Input
            ResultLockInfo &LI,  // Input
            stLockGenKillSet &GKS,  // Output
            const DataLayout &DL
            ) {
        GKS.RLI = LI;
        if (LI.Wrapped) {
            runFSMForResult(LI.ResultValue, GKS.setLockGuard, GKS.setResultAutoDrop,
                            GKS.setResultManualDrop,
                            GKS.setResultMovedToOtherFunc, GKS.setResultReturned,
                            GKS.setResultOverwritten, GKS.setResultUnknown, DL);
            for (Value *LockGuardValue : GKS.setLockGuard) {
                runFSMForLockGuard(LockGuardValue, GKS.setLockGuardDeref, GKS.setLockGuardAutoDrop,
                                   GKS.setLockGuardManualDrop, GKS.setLockGuardMovedToOtherFunc,
                                   GKS.setLockGuardReturned, GKS.setLockGuardOverwritten,
                                   GKS.setLockGuardUnknown, DL);
            }
        } else {  // Result is Unwrapped LockGuard
            runFSMForLockGuard(LI.ResultValue, GKS.setLockGuardDeref, GKS.setLockGuardAutoDrop,
                               GKS.setLockGuardManualDrop, GKS.setLockGuardMovedToOtherFunc,
                               GKS.setLockGuardReturned, GKS.setLockGuardOverwritten,
                               GKS.setLockGuardUnknown, DL);
        }
    }

    static void collectLockGenKillInfo(std::map<Instruction *, Function *> &mapLocalCallSite,  // Input
                                      LockGenKillInfoMapTy &mapGenKillInfo,  // Output
                                      const DataLayout &DL) {  // Input
        for (auto &kv : mapLocalCallSite) {
            Instruction *I = kv.first;
            ResultLockInfo LI = {nullptr, nullptr, LockShareType::SharedLock, true};
            if (dispatchLockInst(I, LI)) {
                stLockGenKillSet &GKS = mapGenKillInfo[I];
                GKS.RLI = LI;
                if (LI.Wrapped) {
                    runFSMForResult(LI.ResultValue, GKS.setLockGuard, GKS.setResultAutoDrop,
                                    GKS.setResultManualDrop,
                                    GKS.setResultMovedToOtherFunc, GKS.setResultReturned,
                                    GKS.setResultOverwritten, GKS.setResultUnknown, DL);
                    for (Value *LockGuardValue : GKS.setLockGuard) {
                        runFSMForLockGuard(LockGuardValue, GKS.setLockGuardDeref, GKS.setLockGuardAutoDrop,
                                           GKS.setLockGuardManualDrop, GKS.setLockGuardMovedToOtherFunc,
                                           GKS.setLockGuardReturned, GKS.setLockGuardOverwritten,
                                           GKS.setLockGuardUnknown, DL);
                    }
                } else {  // Result is Unwrapped LockGuard
                    runFSMForLockGuard(LI.ResultValue, GKS.setLockGuardDeref, GKS.setLockGuardAutoDrop,
                                       GKS.setLockGuardManualDrop, GKS.setLockGuardMovedToOtherFunc,
                                       GKS.setLockGuardReturned, GKS.setLockGuardOverwritten,
                                       GKS.setLockGuardUnknown, DL);
                }
            }
        }
    }

    static bool getNextValue(Use *InputUse, Value *&Output, GuardDest &GD, const DataLayout &DL) {
        User *InputUser = InputUse->getUser();
        InputUser->print(errs());
        errs() << "\n";
        if (Instruction *I = dyn_cast<Instruction>(InputUser)) {
            if (isCallOrInvokeInst(I)) {
                CallSite CS;
                if (Function *F = getCalledFunc(I, CS)) {
                    StringRef FuncName = F->getName();
                    if (FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$6unwrap17h")) {
                        Output = I;
                        return true;
                    } else if (FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$6expect17h")) {
//                        if (I->getOperandUse(1) == *InputUse) {
                        if (F->getReturnType()->isVoidTy()) {
                            Value *Dest = GetUnderlyingObject(I->getOperand(0), DL);
                            errs() << "Result::expect Dest\n";
                            Dest->print(errs());
                            errs() << "\n";
                            Output = Dest;
                        } else {
                            Output = I;
                        }
                        return true;
//                        }
                    } else if (FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$7map_err17h")) {
                        if (F->getReturnType()->isVoidTy()) {
                            Value *Dest = GetUnderlyingObject(I->getOperand(0), DL);
                            errs() << "Result::map_err Dest\n";
                            Dest->print(errs());
                            errs() << "\n";
                            Output = Dest;
                        } else {
                            errs() << "Result::map_err Dest\n";
                            Output = I;
                        }
                        return true;
                    } else if (FuncName.startswith("_ZN4core6result19Result$LT$T$C$E$GT$3map17h")) {
                        if (F->getReturnType()->isVoidTy()) {
                            Value *Dest = GetUnderlyingObject(I->getOperand(0), DL);
                            errs() << "Result::map Dest\n";
                            Dest->print(errs());
                            errs() << "\n";
                            Output = Dest;
                        } else {
                            errs() << "Result::map Dest\n";
                            Output = I;
                        }
                        return true;
                    } else if (FuncName.startswith("_ZN73_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try..Try$GT$11into_result")) {
                        if (F->getReturnType()->isVoidTy()) {
                            Value *Dest = GetUnderlyingObject(I->getOperand(0), DL);
                            errs() << "Result::into_result Dest\n";
                            Dest->print(errs());
                            errs() << "\n";
                            Output = Dest;
                        } else {
                            errs() << "Result::into_result Dest\n";
                            Output = I;
                        }
                        return true;
                    } else if (FuncName.startswith("_ZN4core3ptr18real_drop_in_place17h")) {
//                        errs() << "Auto Drop Guard\n";
                        GD = GuardDest::AutoDrop;
                        Output = nullptr;
                        return false;
                    } else if (FuncName.startswith("_ZN4core3mem4drop17h")) {
//                        errs() << "Manual Drop Guard\n";
                        GD = GuardDest::ManualDrop;
                        Output = nullptr;
                        return false;
                    } else if (MemTransferInst *MI = dyn_cast<MemTransferInst>(I)) {
                        if (MI->getOperandUse(0) == *InputUse) {
                            Output = nullptr;
                            return false;
                        } else {
                            Value *Dest = GetUnderlyingObject(MI->getOperand(0), DL);
//                            errs() << "MemTransferInst Dest\n";
//                            Dest->print(errs());
//                            errs() << "\n";
                            Output = Dest;
                            return true;
                        }
                    } else if (isa<MemSetInst>(I)) {
                        Output = nullptr;
                        return false;
                    }
                }
            } else if (isa<LoadInst>(I)) {
                Output = I;
                return true;
            } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                if (SI->getOperandUse(1) == *InputUse) {
                    Output = nullptr;
                    return false;
                } else {
                    Value *Dest = GetUnderlyingObject(SI->getOperand(1), DL);
//                    errs() << "Store Dest\n";
//                    Dest->print(errs());
//                    errs() << "\n";
                    Output = Dest;
                    return true;
                }
            } else if (isa<InsertValueInst>(I)) {
                Output = I;
                return true;
            } else if (isa<CastInst>(I)) {
                Output = I;
                return true;
            } else if (isa<GetElementPtrInst>(I)) {
                Output = I;
                return true;
            } else if (isa<ExtractValueInst>(I)) {
                Output = I;
                return true;
            } else if (isa<ReturnInst>(I)) {
//                errs() << "Return Guard\n";
                GD = GuardDest::Return;
                Output = nullptr;
                return false;
            } else {
                Output = nullptr;
                return false;
            }
        }
        Output = nullptr;
        return false;
    }

    bool isNewControlFlowDependentOn(Instruction *I1, Instruction *I2) {
        // I1->icmp
        // to I2
        return true;
    }

    static bool collectDropInfo(Value *ResultValue,
                                std::set<Instruction *> &setAutoDropGuard,
                                std::set<Instruction *> &setManualDropGuard,
                                std::set<Instruction *> &setReturnGuard,
                                const DataLayout &DL) {

        Value *NextValue = ResultValue;
        std::list<Value *> WorkList;
        std::set<Value *> Visited;
        WorkList.push_back(NextValue);
        Visited.insert(NextValue);
//        errs() << "NextValue:\n";
//        NextValue->print(errs());
//        errs() << "\n";
        while (!WorkList.empty()) {
            NextValue = WorkList.front();
            WorkList.pop_front();
            if (User *NI = dyn_cast<User>(NextValue)) {
                for (Use &U : NI->uses()) {
                    Value *CurrNextValue = nullptr;
                    GuardDest GD = GuardDest::Unknown;
                    if (getNextValue(&U, CurrNextValue, GD, DL)) {
                        if (Visited.find(CurrNextValue) == Visited.end()) {
                            WorkList.push_back(CurrNextValue);
                            Visited.insert(CurrNextValue);
//                            errs() << "Succ\n";
//                            errs() << "Visited contains\n";
//                            for (Value *V : Visited) {
//                                V->print(errs());
//                                errs() << "\n";
//                            }
//                            errs() << "End of Visited contains\n";
                        }
//                        else {
//                            errs() << "Visited, Stop\n";
//                        }
                    } else {
                        switch (GD) {
                            case GuardDest::AutoDrop: {
                                Instruction *AD = dyn_cast<Instruction>(U.getUser());
                                setAutoDropGuard.insert(AD);
                                break;
                            }
                            case GuardDest::ManualDrop: {
                                Instruction *MD = dyn_cast<Instruction>(U.getUser());
                                setManualDropGuard.insert(MD);
                                break;
                            }
                            case GuardDest::Return: {
                                Instruction *RT = dyn_cast<Instruction>(U.getUser());
                                setReturnGuard.insert(RT);
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    }
                }
            }
        }

        // Debug
        if (!setAutoDropGuard.empty()) {
            errs() << "Auto Drop Guard:\n";
        }
        for (Instruction *I : setAutoDropGuard) {
            I->print(errs());
            errs() << "\n";
        }

        if (!setManualDropGuard.empty()) {
            errs() << "Manual Drop Guard:\n";
        }
        for (Instruction *I : setManualDropGuard) {
            I->print(errs());
            errs() << "\n";
        }

        if (!setReturnGuard.empty()) {
            errs() << "Return Guard:\n";
        }
        for (Instruction *I : setReturnGuard) {
            I->print(errs());
            errs() << "\n";
        }

        return !setAutoDropGuard.empty() || !setManualDropGuard.empty() || !setReturnGuard.empty();
    }

    struct LockDropInfo {
        Instruction *LockInst;
        ResultLockInfo LI;
        std::set<Instruction *> setAutoDropGuard;
        std::set<Instruction *> setManualDropGuard;
        std::set<Instruction *> setReturnGuard;
    };

    static bool collectLockInfo(Function *F,
            std::map<Instruction *, Function *> &mapCallSite,
            std::map<Instruction *, LockDropInfo> &mapLockDropInfo,
            const DataLayout &DL
            ) {
        if (!F || F->isDeclaration()) {
            return false;
        }
        for (BasicBlock &B : *F) {
            for (Instruction &II : B) {
                Instruction *I = &II;
                if (skipInst(I)) {
                    continue;
                }
                if (isCallOrInvokeInst(I)) {
                    CallSite CS;
                    if (Function *Callee = getCalledFunc(I, CS)) {
                        mapCallSite[I] = Callee;
                        ResultLockInfo LI = {nullptr, nullptr, LockShareType::SharedLock};
                        if (dispatchLockInst(I, LI)) {
                            // Found LockInst
                            LockDropInfo LDI;
                            LDI.LockInst = I;
                            LDI.LI = LI;
                            LDI.LockInst->print(errs());
                            errs() << "\n";
                            assert(LI.ResultValue);
                            LI.ResultValue->print(errs());
                            errs() << "\n";
                            // Find drop/return
                            if (!collectDropInfo(LI.ResultValue, LDI.setAutoDropGuard, LDI.setManualDropGuard,
                                                 LDI.setReturnGuard, DL)) {
                                errs() << "Cannot find the Dest of Lock Guard!\n";
                                I->print(errs());
                                errs() << "\n";
                                printDebugInfo(I);
                                errs().write_escaped(I->getFunction()->getName()) << "\n";
                            }
                            mapLockDropInfo[I] = LDI;
                        }
                    }
                }
            }
        }
        return !mapLockDropInfo.empty();
    }

    static bool trackCallee(Instruction *LockInst,
                            std::pair<Instruction *, Function *> &DirectCalleeSite,
                            std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallees,
                            std::map<Function *, std::set<Instruction *>> &mapAliasFuncLock) {

        bool HasDoubleLock = false;

        Function *DirectCallee = DirectCalleeSite.second;

        if (mapAliasFuncLock.find(DirectCallee) != mapAliasFuncLock.end()) {
            // Restore
//            HasDoubleLock = true;
//            errs() << "Double Lock Happens! First Lock:\n";
//            printDebugInfo(LockInst);
//            errs() << DirectCallee->getName() << '\n';
//            // Debug Require
//            LockInst->print(errs());
//            errs() << '\n';
//            printDebugInfo(DirectCalleeSite.first);
//            errs() << "Second Lock(s):\n";
//            for (Instruction *AliasLock : mapAliasFuncLock[DirectCallee]) {
//                printDebugInfo(AliasLock);
//                AliasLock->print(errs());
//                errs() << '\n';
//            }
//            errs() << '\n';
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
                            // Restore
//                            errs() << "Double Lock Happens! First Lock:\n";
//                            errs() << LockInst->getParent()->getParent()->getName() << '\n';
//                            printDebugInfo(LockInst);
//                            LockInst->print(errs());
//                            errs() << '\n';
//                            errs() << Callee->getName() << '\n';
//                            errs() << "Second Lock(s):\n";
//                            for (Instruction *AliasLock : mapAliasFuncLock[Callee]) {
//                                printDebugInfo(AliasLock);
//                                LockInst->print(errs());
//                                errs() << '\n';
//                            }
//                            errs() << '\n';
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
                    // Restore
//                    errs() << "Double Lock Happens! First Lock:\n";
//                    printDebugInfo(LockInst);
//                    errs() << "Second Lock(s):\n";
//                    printDebugInfo(I);
//                    // Debug Require
//                    // LockInst->print(errs());
//                    errs() << '\n';
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

    bool SameLockInSameFuncDetector::runOnModule(Module &M) {
        this->pModule = &M;

        std::map<Function *, std::map<Instruction *, Function *>> mapGlobalCallSite;
        for (Function &F : M) {
            collectGlobalCallSite(&F, mapGlobalCallSite[&F]);
        }

        std::map<Function *, std::set<Instruction *>> mapCalleeToCallSites;
        for (auto &CallerCallSites : mapGlobalCallSite) {
            for (auto &CallInstCallee : CallerCallSites.second) {
                mapCalleeToCallSites[CallInstCallee.second].insert(CallInstCallee.first);
            }
        }

        LockGenKillInfoMapTy mapLockGenKillInfo;
        for (auto &kv : mapGlobalCallSite) {
            collectLockGenKillInfo(kv.second, mapLockGenKillInfo, M.getDataLayout());
        }

        std::map<Type *, std::map<Instruction *, stLockGenKillSet>> mapSameTypeLock;
        for (auto &InstInfo: mapLockGenKillInfo) {
            Type *Ty = InstInfo.second.RLI.LockValue->getType();
            if (!Ty) {
                errs() << "Cannot get Type of LockValue of Inst\n";
                printDebugInfo(InstInfo.first);
                continue;
            }
            mapSameTypeLock[Ty][InstInfo.first] = InstInfo.second;
        }

        LockGenKillInfoMapTy mapWrapperLockGenKillInfo;
        for (auto &kv : mapLockGenKillInfo) {
            if (!kv.second.setResultReturned.empty()) {
                Instruction *CurrInst = kv.first;
                ResultLockInfo InnerRLI = kv.second.RLI;
                Function *LockWrapper = CurrInst->getFunction();
                if (mapCalleeToCallSites.find(LockWrapper) == mapCalleeToCallSites.end()) {
                    continue;
                }

                for (Instruction *WrapperLockInst : mapCalleeToCallSites[LockWrapper]) {
                    ResultLockInfo RLI;
                    RLI.ResultValue = WrapperLockInst;
                    RLI.LockType = InnerRLI.LockType;
                    RLI.Wrapped = true;
                    RLI.LockValue = InnerRLI.LockValue;
                    stLockGenKillSet &GKS = mapWrapperLockGenKillInfo[WrapperLockInst];
                    collectLockGenKillInfoForLock(WrapperLockInst, RLI, GKS, M.getDataLayout());
                }
            }
            if (!kv.second.setLockGuardReturned.empty()) {
                Instruction *CurrInst = kv.first;
                ResultLockInfo InnerRLI = kv.second.RLI;
                Function *LockWrapper = CurrInst->getFunction();
                if (mapCalleeToCallSites.find(LockWrapper) == mapCalleeToCallSites.end()) {
                    continue;
                }

                for (Instruction *WrapperLockInst : mapCalleeToCallSites[LockWrapper]) {
                    ResultLockInfo RLI;
                    RLI.ResultValue = WrapperLockInst;
                    RLI.LockType = InnerRLI.LockType;
                    RLI.Wrapped = false;
                    RLI.LockValue = InnerRLI.LockValue;
                    stLockGenKillSet &GKS = mapWrapperLockGenKillInfo[WrapperLockInst];
                    collectLockGenKillInfoForLock(WrapperLockInst, RLI, GKS, M.getDataLayout());
                }
            }
        }

        for (auto &kv : mapWrapperLockGenKillInfo) {
            errs() << "Wrapper LockInst:\n";
            kv.first->print(errs());
            errs() << "\n";
            errs() << "Result Returned:" << kv.second.setResultReturned.size() << "\n";
            errs() << "LockGuard Returned:" << kv.second.setLockGuardReturned.size() << "\n";
        }

        std::map<Type *, std::map<Instruction *, stLockGenKillSet>> mapWrapperSameTypeLock;
        for (auto &InstInfo: mapWrapperLockGenKillInfo) {
            Type *Ty = InstInfo.second.RLI.LockValue->getType();
            if (!Ty) {
                errs() << "Cannot get Type of LockValue of Inst\n";
                printDebugInfo(InstInfo.first);
                continue;
            }
            mapWrapperSameTypeLock[Ty][InstInfo.first] = InstInfo.second;
        }

//        // LockInst->Func->CallSite
//        // TODO: use a WorkList to propagate lock
//        for (auto &kv : mapLockGenKillInfo) {
//            if (!kv.second.setResultReturned.empty()) {
//                std::list<Instruction *> WorkList;
//                std::set<Instruction *> Visited;
//                WorkList.push_back(kv.first);
//                Visited.insert(kv.first);
//                bool WrappedInResult = true;
//                while (!WorkList.empty()) {
//                    Instruction *CurrInst = WorkList.front();
//                    WorkList.pop_front();
//                    Function *LockWrapper = CurrInst->getFunction();
//                    if (mapCalleeToCallSites.find(LockWrapper) == mapCalleeToCallSites.end()) {
//                        continue;
//                    }
//                    for (Instruction *WrapperLockInst : mapCalleeToCallSites[LockWrapper]) {
//                        ResultLockInfo LI = kv.second.RLI;
//                        LI.Wrapped = WrappedInResult;
//                        LI.ResultValue = WrapperLockInst;
//                        collectLockGenKillInfoForLock(WrapperLockInst, LI, mapLockGenKillInfo, M.getDataLayout());
//                        // For simplicity, we did not consider returning Result & LockGuard at the same time
//                        if (!mapLockGenKillInfo[WrapperLockInst].setResultReturned.empty()) {
//                            WorkList.push_back(WrapperLockInst);
//                            Visited.insert(WrapperLockInst);
//                            WrappedInResult = true;
//                        } else if (!mapLockGenKillInfo[WrapperLockInst].setLockGuardReturned.empty()) {
//                            WorkList.push_back(WrapperLockInst);
//                            Visited.insert(WrapperLockInst);
//                            WrappedInResult = false;
//                        }
//                    }
//                }
//            }
//            if (!kv.second.setLockGuardReturned.empty()) {
//                std::list<Instruction *> WorkList;
//                std::set<Instruction *> Visited;
//                WorkList.push_back(kv.first);
//                Visited.insert(kv.first);
//                bool WrappedInResult = false;
//                while (!WorkList.empty()) {
//                    Instruction *CurrInst = WorkList.front();
//                    WorkList.pop_front();
//                    Function *LockWrapper = CurrInst->getFunction();
//                    if (mapCalleeToCallSites.find(LockWrapper) == mapCalleeToCallSites.end()) {
//                        continue;
//                    }
//                    for (Instruction *WrapperLockInst : mapCalleeToCallSites[LockWrapper]) {
//                        ResultLockInfo LI = kv.second.RLI;
//                        LI.Wrapped = WrappedInResult;
//                        LI.ResultValue = WrapperLockInst;
//                        collectLockGenKillInfoForLock(WrapperLockInst, LI, mapLockGenKillInfo, M.getDataLayout());
//                        // For simplicity, we did not consider returning Result & LockGuard at the same time
//                        if (!mapLockGenKillInfo[WrapperLockInst].setResultReturned.empty()) {
//                            WorkList.push_back(WrapperLockInst);
//                            Visited.insert(WrapperLockInst);
//                            WrappedInResult = true;
//                        } else if (!mapLockGenKillInfo[WrapperLockInst].setLockGuardReturned.empty()) {
//                            WorkList.push_back(WrapperLockInst);
//                            Visited.insert(WrapperLockInst);
//                            WrappedInResult = false;
//                        }
//                    }
//                }
//            }
//        }

        for (auto &TyResult: mapSameTypeLock) {
            for (auto &InstLI : TyResult.second) {
                Instruction *CurrLockInst = InstLI.first;
                Value *CurrLockValue = InstLI.second.RLI.LockValue;
                LockShareType CurrLockShareType = InstLI.second.RLI.LockType;
                Function *CurrFunc = CurrLockInst->getFunction();
                std::set<Instruction *> setMayAliasLock;
                for (auto &OtherInstLI : TyResult.second) {
                    if (OtherInstLI.first != CurrLockInst) {
                        if (CurrFunc == OtherInstLI.first->getFunction()) {  // In same function, use Alias
                            errs() << "In the Same Function\n";
                            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(*CurrFunc).getAAResults();
                            if (AA.alias(CurrLockValue, OtherInstLI.second.RLI.LockValue) == MustAlias) {
                                if (CurrLockShareType == LockShareType::SharedLock
                                && OtherInstLI.second.RLI.LockType == LockShareType::SharedLock) {  // both shared lock
                                    continue;
                                } else {
                                    setMayAliasLock.insert(OtherInstLI.first);
                                }
                            }
                        } else {  // In different function, track self same field, but
                            setMayAliasLock.insert(OtherInstLI.first);
                        }
                    }
                }

                std::set<Instruction *> setLockDrop;
                for (Value *V : InstLI.second.setResultAutoDrop) {
                    if (Instruction *I = dyn_cast<Instruction>(V)) {
                        setLockDrop.insert(I);
                    }
                }
                for (Value *V : InstLI.second.setResultManualDrop) {
                    if (Instruction *I = dyn_cast<Instruction>(V)) {
                        setLockDrop.insert(I);
                    }
                }
                for (Value *V : InstLI.second.setResultMovedToOtherFunc) {
                    if (Instruction *I = dyn_cast<Instruction>(V)) {
                        setLockDrop.insert(I);
                    }
                }
                for (Value *V : InstLI.second.setLockGuardAutoDrop) {
                    if (Instruction *I = dyn_cast<Instruction>(V)) {
                        setLockDrop.insert(I);
                    }
                }
                for (Value *V : InstLI.second.setLockGuardManualDrop) {
                    if (Instruction *I = dyn_cast<Instruction>(V)) {
                        setLockDrop.insert(I);
                    }
                }
                for (Value *V : InstLI.second.setLockGuardMovedToOtherFunc) {
                    if (Instruction *I = dyn_cast<Instruction>(V)) {
                        setLockDrop.insert(I);
                    }
                }

                trackLockInst(CurrLockInst, setMayAliasLock, setLockDrop, mapGlobalCallSite);
            }
        }



//        this->pModule = &M;
////        this->pDL = &M.getDataLayout();
//
//        std::map<Function *, std::map<Instruction *, Function *>> mapAllCallSite;
//        std::map<Function *, std::map<Instruction *, LockDropInfo>> mapAllLockDropInfo;
//        for (Function &F : M) {
////            if (F.getName().startswith("_ZN7devices3bus3Bus4read17hedc46889f014412fE")) {
//                collectLockInfo(&F, mapAllCallSite[&F], mapAllLockDropInfo[&F], M.getDataLayout());
////            }
//            if (mapAllCallSite[&F].empty()) {
//                continue;
//            }
//            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(F).getAAResults();
//            for (auto &kv : mapAllLockDropInfo[&F]) {
//                Value *LockValue1 = kv.second.LI.LockValue;
//                for (auto &kv2 : mapAllLockDropInfo[&F]) {
//                    if (kv.first != kv2.first) {
//                        Value *LockValue2 = kv2.second.LI.LockValue;
//                        if (AA.alias(LockValue1, LockValue2) == MustAlias) {
//                            if (isNewControlFlowDependentOn(kv.first, kv2.first)) {
//                                errs() << "Same Lock in Same Func\n";
//                                errs().write_escaped(F.getName()) << "\n";
//                                kv.first->print(errs());
//                                errs() << "\n";
//                                printDebugInfo(kv.first);
//                                kv2.first->print(errs());
//                                errs() << "\n";
//                                printDebugInfo(kv2.first);
//                            }
//                        }
//                    }
//                }
//            }
//        }




//        std::map<Instruction *, Function *> mapCallInstCallee;
//        std::map<Instruction *, stLockInfo> mapLockInfo;
//        std::map<Instruction *, std::pair<Function *, std::set<Instruction *>>> mapLockDropInfo;

//        for (Function &F: M) {
//        Function *F1 = M.getFunction("_ZN160_$LT$ethcore_secretstore..key_server_cluster..cluster..ClusterClientImpl$LT$C$GT$$u20$as$u20$ethcore_secretstore..key_server_cluster..cluster..ClusterClient$GT$22new_generation_session17ha7b4ea0a914cf791E");
//        Function *F2 = M.getFunction("_ZN19ethcore_secretstore18key_server_cluster16cluster_sessions38ClusterSessionsContainer$LT$S$C$SC$GT$6insert17hb5586ff06e7c9c74E");
//        parseFunc(F1, mapCallInstCallee, mapLockInfo, mapLockDropInfo);
//        parseFunc(F2, mapCallInstCallee, mapLockInfo, mapLockDropInfo);
//        }
//        for (Function &F : M) {
//            parseFunc(&F, mapCallInstCallee, mapLockInfo, mapLockDropInfo);
//        }
//
//        std::set<Instruction *> setAutoDropGuard;
//        std::set<Instruction *> setManualDropGuard;
//        std::set<Instruction *> setReturnGuard;
//
//        Instruction *LockInst = mapLockInfo.begin()->first;
//        Value *NextValue = LockInst->getOperand(0);
//        std::list<Value *> WorkList;
//        std::set<Value *> Visited;
//        WorkList.push_back(NextValue);
//        Visited.insert(NextValue);
//        while (!WorkList.empty()) {
//            NextValue = WorkList.front();
//            WorkList.pop_front();
//            if (User *NI = dyn_cast<User>(NextValue)) {
//                for (Use &U : NI->uses()) {
//                    Value *CurrNextValue = nullptr;
//                    GuardDest GD = GuardDest::Unknown;
//                    if (getNextValue(&U, CurrNextValue, GD, M.getDataLayout())) {
//                        if (Visited.find(CurrNextValue) == Visited.end()) {
//                            WorkList.push_back(CurrNextValue);
//                            Visited.insert(CurrNextValue);
////                            errs() << "Succ\n";
////                            errs() << "Visited contains\n";
////                            for (Value *V : Visited) {
////                                V->print(errs());
////                                errs() << "\n";
////                            }
////                            errs() << "End of Visited contains\n";
//                        }
////                        else {
////                            errs() << "Visited, Stop\n";
////                        }
//                    } else {
//                        switch (GD) {
//                            case GuardDest::AutoDrop: {
//                                Instruction *AD = dyn_cast<Instruction>(U.getUser());
//                                setAutoDropGuard.insert(AD);
//                                break;
//                            }
//                            case GuardDest::ManualDrop: {
//                                Instruction *MD = dyn_cast<Instruction>(U.getUser());
//                                setManualDropGuard.insert(MD);
//                                break;
//                            }
//                            case GuardDest::Return: {
//                                Instruction *RT = dyn_cast<Instruction>(U.getUser());
//                                setReturnGuard.insert(RT);
//                                break;
//                            }
//                            default: {
//                                break;
//                            }
//                        }
//                    }
//                }
//            }
//        }
//
//        // Debug
//        errs() << "Auto Drop Guard:\n";
//        for (Instruction *I : setAutoDropGuard) {
//            I->print(errs());
//            errs() << "\n";
//        }
//
//        errs() << "Manual Drop Guard:\n";
//        for (Instruction *I : setManualDropGuard) {
//            I->print(errs());
//            errs() << "\n";
//        }
//
//        errs() << "Return Guard:\n";
//        for (Instruction *I : setReturnGuard) {
//            I->print(errs());
//            errs() << "\n";
//        }

//        std::map<Function *, std::map<Instruction *, Function *>> mapCallerCallee;
//
//        for (Function &F : M) {
//            if (F.begin() == F.end()) {
//                continue;
//            }
//
//            for (BasicBlock &B : F) {
//                for (Instruction &I : B) {
//                    if (isa<CallInst>(&I) || isa<InvokeInst>(&I)) {
//                        CallSite CS(&I);
//                        if (Value *CV = CS.getCalledValue()) {
//                            if (Function *Callee = dyn_cast<Function>(CV->stripPointerCasts())) {
//                                mapCallerCallee[&F][&I] = Callee;
//                            } else {
////                                printErrMsg(&I, "Callee Not Found:");
//                            }
//                        } else {
////                            printErrMsg(&I, "Callee Not Found:");
//                        }
//                    }
//                }
//            }
//        }

//        for (auto &kv : mapLockInfo) {
//            Function *Caller = kv.first->getFunction();
//            for (auto &kv2 : mapCallerCallee[Caller]) {
//                kv2.first = 0;
//            }
//        }

//        for (auto &kv : mapLockInfo) {
//            for (auto &kv2 : mapLockInfo) {
//                if (kv.first != kv2.first) {
//                    if (kv.first->getParent()->getParent() == kv2.first->getParent()->getParent()) {
//                        Function *F = kv.first->getParent()->getParent();
//                        AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(*F).getAAResults();
//                        if (AA.alias(kv.second.LockValue, kv2.second.LockValue) == MustAlias) {
//                            errs() << "Two Locks are in the same Func\n";
//                            errs().write_escaped(F->getName()) << "\n";
//                            printDebugInfo(kv.first);
//                            printDebugInfo(kv2.first);
//                        }
//                    }
//                }
//            }
//        }

        return false;
    }

}  // namespace detector

static RegisterPass<detector::SameLockInSameFuncDetector> X(
        "detect",
        "Detect Same Lock/Atomic",
        false,
        true);