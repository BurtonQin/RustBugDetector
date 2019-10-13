#include "DoubleLockDetector/DoubleLockDetector.h"

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "DoubleLockDetector"

using namespace llvm;

namespace detector {

    char DoubleLockDetector::ID = 0;

    DoubleLockDetector::DoubleLockDetector() : ModulePass(ID) {}

    void DoubleLockDetector::getAnalysisUsage(AnalysisUsage &AU) const {
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
        I->print(errs());
        errs() << "\n";
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
    };

    static bool trackMutexToSelf(Value *mutex, MutexSource &MS) {
        if (!mutex) {
            return false;
        }
        for (auto it = mutex->use_begin(); it != mutex->use_end(); ++it) {
            if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(it->get())) {
                Value *Self = GEP->getOperand(0);
                Type *structTy = Self->stripPointerCasts()->getType()->getContainedType(0);
                structTy->print(errs());
                errs() << "\n";
                if (!isa<StructType>(structTy)) {
                    errs() << "Self not Struct" << "\n";
                    continue;
                }
                MS.structTy = structTy;
                Self->print(errs());
                errs() << "\n";
                for (unsigned i = 1; i < GEP->getNumOperands(); ++i) {
                    errs() << "index: ";
                    APInt idx = dyn_cast<ConstantInt>(GEP->getOperand(i))->getValue();
                    MS.index.push_back(idx);
                    GEP->getOperand(i)->getType()->print(errs());
                    errs() << "\n";
                    GEP->getOperand(i)->print(errs());
                    errs() << "\n";
                }
                return true;
            } else if (BitCastInst *BCI = dyn_cast<BitCastInst>(it->get())) {
                // TODO;

            }
        }
        return false;
    }

    bool DoubleLockDetector::runOnModule(Module &M) {
        this->pModule = &M;
        for (Function &FI: M) {
            if (FI.isDeclaration()) {
                continue;
            }
            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(FI).getAAResults();
            Function *F = &FI;
            std::map<Instruction *, LockInfo> mapLockInfo;
            bool ContainLock = findAllLocks(F, mapLockInfo);
            if (ContainLock) {
                errs() << "contains:" << F->getName() << "\n";
                std::map<Instruction *, std::set<Instruction *>> mapAliasLock;
                std::map<Instruction *, std::set<BasicBlock *>> mapAliasLockBB;
                std::map<Instruction *, std::set<BasicBlock *>> mapDropBB;
                if (getAliasedLocks(AA, mapLockInfo, mapAliasLock, mapAliasLockBB)) {
                    errs() << "\nFuncName:" << F->getName() << "\n";
                    for (auto &kv : mapAliasLock) {
                        if (kv.second.empty()) {
                            continue;
                        }
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
        return false;
    }
}  // namespace detector

static RegisterPass<detector::DoubleLockDetector> X(
        "detect",
        "Detect Double Lock",
        false,
        true);
