#include "PrintPass/PrintPass.h"

#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <memory>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Analysis/AliasSetTracker.h"

using namespace llvm;

namespace printpass {

//    static int GetFunctionID(Function *F) {
//        if (F->begin() == F->end()) {
//            return -1;
//        }
//
//        BasicBlock *EntryBB = &(F->getEntryBlock());
//
//        if (EntryBB) {
//
//            for (BasicBlock::iterator II = EntryBB->begin(); II != EntryBB->end(); II++) {
//                Instruction *Inst = &*II;
//                MDNode *Node = Inst->getMetadata("func_id");
//                if (!Node) {
//                    continue;
//                }
//                assert(Node->getNumOperands() == 1);
//                const Metadata *MD = Node->getOperand(0);
//                if (auto *MDV = dyn_cast<ValueAsMetadata>(MD)) {
//                    Value *V = MDV->getValue();
//                    ConstantInt *CI = dyn_cast<ConstantInt>(V);
//                    assert(CI);
//                    return CI->getZExtValue();
//                }
//            }
//        }
//
//        return -1;
//    }

//    static int GetInstructionID(Instruction *II) {
//
//        MDNode *Node = II->getMetadata("ins_id");
//        if (!Node) {
//            return -1;
//        }
//
//        assert(Node->getNumOperands() == 1);
//        const Metadata *MD = Node->getOperand(0);
//        if (auto *MDV = dyn_cast<ValueAsMetadata>(MD)) {
//            Value *V = MDV->getValue();
//            ConstantInt *CI = dyn_cast<ConstantInt>(V);
//            assert(CI);
//            return CI->getZExtValue();
//        }
//
//        return -1;
//    }

//    static Function *getCalleeFunc(Instruction *pInst) {
//        if (!pInst) {
//            return nullptr;
//        }
//        if (isa<DbgInfoIntrinsic>(pInst)) {
//            return nullptr;
//        } else if (isa<InvokeInst>(pInst) || isa<CallInst>(pInst)) {
//            CallSite cs(pInst);
//            Function *pCalled = cs.getCalledFunction();
//            if (pCalled) {
//                int id = GetFunctionID(pCalled);
//                if (id == -1) {
//                    return nullptr;
//                } else {
//                    errs() << GetFunctionID(pCalled) << '\n';
//                    return pCalled;
//                }
//            } else {
//                errs() << "FuncPtr:" << GetInstructionID(pInst) << '\n';
//                return nullptr;
//            }
//        }
//        return nullptr;
//    }

//    static void FindDirectCallees(const std::set<llvm::BasicBlock *> &setBB,
//                                  std::vector<llvm::Function *> &vecWorkList,
//                                  std::set<llvm::Function *> &setToDo,
//                                  std::map<llvm::Function *, std::set<llvm::Instruction *>> &funcCallSitemapping) {
//        for (BasicBlock *BB : setBB) {
//            if (isa<UnreachableInst>(BB->getTerminator())) {
//                continue;
//            }
//
//            for (Instruction &II : *BB) {
//                Instruction *pInst = &II;
//
//                if (Function *pCalled = getCalleeFunc(pInst)) {
//                    if (pCalled->getName() == "JS_Assert") {
//             /-*/-           continue;
//                    }
//                    if (pCalled->begin() == pCalled->end()) {
//                        continue;
//                    }
//                    if (pCalled->isDeclaration()) {
//                        continue;
//                    }
//                    if (pCalled->getSection().str() == ".text.startup") {
//                        funcCallSitemapping[pCalled].insert(pInst);
//
//                        if (setToDo.find(pCalled) == setToDo.end()) {
//                            setToDo.insert(pCalled);
//                            vecWorkList.push_back(pCalled);
//                        }
//                    }
//                }
//            }
//        }
//    }

    char PrintPass::ID = 0;

    PrintPass::PrintPass() : ModulePass(ID) {}

    void PrintPass::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<AAResultsWrapperPass>();
    }

    struct LockInfo {
        Value *result;
        Value *mutex;
    };

    struct UnwrapInfo {
        Value *result;
    };

    struct DropInfo {
        Value *data;
    };

    static bool isCallOrInvokeInst(Instruction *I) {
        if (!I) {
            return false;
        }
        if (isa<DbgInfoIntrinsic>(I)) {
            return false;
        }
        if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
            return true;
        }
        return false;
    }

    static Function *getCalledFunc(Instruction *pInst) {
        if (!pInst) {
            return nullptr;
        }
        if (isa<DbgInfoIntrinsic>(pInst)) {
            return nullptr;
        } else if (isa<InvokeInst>(pInst) || isa<CallInst>(pInst)) {
            CallSite cs(pInst);
            Function *pCalled = cs.getCalledFunction();
            if (pCalled) {
               return pCalled;
            } else {
                errs() << "Call FuncPtr:" << '\n';
                return nullptr;
            }
        }
        return nullptr;
    }

    static bool getLockInfo(CallSite &CS, LockInfo &LI) {
        Function *F = CS.getCalledFunction();
        if (!F) {
            return false;
        }

//        F->getName().startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$4read") ||
//        F->getName().startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$5write")
        if (F->getName().startswith("_ZN3std4sync5mutex14Mutex$LT$T$GT$4lock")) {
            assert(CS.getNumArgOperands() >= 2);
            LI.result = CS.getArgOperand(0);
            LI.mutex = CS.getArgOperand(1);
            return true;
        }
        return false;
    }

    static bool getUnwrapInfo(CallSite &CS, UnwrapInfo &UI) {
        Function *F = CS.getCalledFunction();
        if (!F) {
            return false;
        }
        if (F->getName().startswith("_ZN4core6result19Result$LT$T$C$E$GT$6unwrap")) {
            assert(CS.getNumArgOperands() >= 1);
            UI.result = CS.getArgOperand(0);
            return true;
        }
        return false;
    }

    static bool getDropInfo(CallSite &CS, DropInfo &DI) {
        Function *F = CS.getCalledFunction();
        if (!F) {
            return false;
        }
        if (F->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
            assert(CS.getNumArgOperands() >= 1);
            DI.data = CS.getArgOperand(0);
            return true;
        }
        return false;
    }

    static void traverseForInfo(Function *F,
                                std::map<Instruction *, LockInfo> &mapLI,
                                std::map<Instruction *, DropInfo> &mapDI,
                                std::map<Instruction *, UnwrapInfo> &mapUI) {

        for (BasicBlock &B : *F) {
            for (Instruction &I : B) {
                if (!isCallOrInvokeInst(&I)) {
                    continue;
                }
                CallSite CS(&I);
                LockInfo LI = {nullptr, nullptr};
                DropInfo DI = {nullptr};
                UnwrapInfo UI = {nullptr};
                if (getLockInfo(CS, LI)) {
                    mapLI[&I] = LI;
                }
//                else if (getDropInfo(CS, DI)) {
//                    mapDI[&I] = DI;
//                } else if (getUnwrapInfo(CS, UI)) {
//                    mapUI[&I] = UI;
//                }
            }
        }
    }

//    static void detectOneBB(BasicBlock *B) {
//
//        std::set<LockInfo> setLI;
//        std::set<DropInfo> setDI;
//
//        for (Instruction &I : *B) {
//            if (!isCallOrInvokeInst(&I)) {
//                continue;
//            }
//            CallSite CS(&I);
//            LockInfo LI = {nullptr, nullptr };
//            DropInfo DI = { nullptr };
//            if (getLockInfo(CS, LI)) {
//                setLI.insert(LI);
//            } else if (getDropInfo(CS, DI)) {
//                setDI.insert(DI);
//            }
//        }
//    }

    static int getLockOrDropInst(Instruction *pInst) {
        if (!pInst) {
            return 0;
        }
        if (isa<DbgInfoIntrinsic>(pInst)) {
            return 0;
        } else if (isa<InvokeInst>(pInst) || isa<CallInst>(pInst)) {
            CallSite cs(pInst);
            Function *pCalled = cs.getCalledFunction();
            if (pCalled) {
                if (pCalled->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                    assert(cs.getNumArgOperands() >= 1);
                    Value *data = cs.getArgOperand(0);
                    return 2;
                } else if (pCalled->getName().startswith("_ZN3std4sync5mutex14Mutex$LT$T$GT$4lock")) {
                    assert(cs.getNumArgOperands() >= 2);
                    Value *result = cs.getArgOperand(0);
                    Value *mutex = cs.getArgOperand(1);
                    return 1;
                }
            } else {
                errs() << "Call FuncPtr:" << '\n';
                return 0;
            }
        }
        return 0;
    }

    static int containsLockOrDrop(BasicBlock *B) {
        for (Instruction &I : *B) {
            int flag = getLockOrDropInst(&I);
            if (flag == 1) {
                errs() << I << '\n';
                return 1;
            } else if (flag == 2) {
                errs() << I << '\n';
                return 2;
            }
        }
        return 0;
    }

    static void detectDeadlockIntra(Function *F) {

        // find BBs that contains "call Mutex::lock()".
        // group them by arg.
        // find drop_in_place() that takes arg.
        // start from entry, find next lock.
        std::list<BasicBlock *> WorkList;
        std::set<BasicBlock *> Visited;
        WorkList.push_back(&F->getEntryBlock());
        int double_lock = 0;
        while (!WorkList.empty()) {
            BasicBlock *B = WorkList.front();
            WorkList.pop_front();
            int flag = containsLockOrDrop(B);
            if (flag == 1) {
                errs() << "Lock: " << B->getName() << "\n";
                if (double_lock == 0) {
                    ++double_lock;
                    Instruction *pTerm = B->getTerminator();
                    for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
                        BasicBlock *Succ = pTerm->getSuccessor(i);
                        if (Visited.find(Succ) == Visited.end()) {
                            errs() << "Succ:" << Succ->getName() << '\n';
                            WorkList.push_back(Succ);
                            Visited.insert(Succ);
                        }
                    }
                } else if (double_lock == 1) {
                    errs() << "Double Lock: " << F->getName() << "\n";
                    return;
                }
            } else if (flag == 2) {
                errs() << "Drop: " << B->getName() << "\n";
                continue;
            } else if (flag == 0) {
                errs() << "None: " << B->getName() << "\n";
                Instruction *pTerm = B->getTerminator();
                for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
                    BasicBlock *Succ = pTerm->getSuccessor(i);
                    if (Visited.find(Succ) == Visited.end()) {
                        errs() << "Succ:" << Succ->getName() << '\n';
                        WorkList.push_back(Succ);
                        Visited.insert(Succ);
                    }
                }
            } else {
                assert(false);
            }
        }
    }

    struct MutexSource {
        Value *direct;
        Type *structTy;
        std::vector<APInt> index;
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

//    static void detectBugs(Function *F, ) {
//
//    }



//    static void findLockLockPairs(Function *F,
//                                  std::map<Instruction *, MutexSource> mapMS,
//                                  std::map<Instruction *, DropInfo> &mapDI,
//                                  std::map<Instruction *, UnwrapInfo> &mapUI) {
//
//        // key: BB, value: mutexes
//        std::map<BasicBlock *, std::set<MutexSource>> mapBBMS;
//        for (auto &kv : mapMS) {
//            BasicBlock *BB = kv.first->getParent();
//            if (mapBBMS.find(BB) == mapBBMS.end()) {
//                mapBBMS[BB] = std::set<MutexSource>();
//            }
//            mapBBMS[BB].insert(kv.second);
//        }
//
//        std::list<BasicBlock *> WorkList;
//        // key: BB, value: current mutexes (inherit mutexes from parent, remove if dropped)
//        std::map<BasicBlock *, std::set<MutexSource>> Visited;
//        std::map<BasicBlock *, BasicBlock *> Parent;
//
//        // MutexSource
//        BasicBlock *EntryBB = &F->getEntryBlock();
//        WorkList.push_back(EntryBB);
//        while (!WorkList.empty()) {
//            BasicBlock *B = WorkList.front();
//            WorkList.pop_front();
//
//            Instruction *pTerm = B->getTerminator();
//            for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
//                BasicBlock *Succ = pTerm->getSuccessor(i);
//                if (Visited.find(Succ) == Visited.end()) {
//                    errs() << "Succ:" << Succ->getName() << '\n';
//                    Parent[Succ] = B;
//                    WorkList.push_back(Succ);
//                    Visited[Succ] = ;
//                }
//            }
//        }
//    }

    bool PrintPass::runOnModule(Module &M) {
        this->pModule = &M;

//        std::set<Function *> setNonSysFunc;
//        for (Module::iterator FI = M.begin(); FI != M.end(); ++FI) {
//            Function *F = &*FI;
//
//            //errs().write_escaped(F->getName());
//
//            bool non_sys = false;
//            for (Function::iterator BI = F->begin(); BI != F->end(); ++BI) {
//                BasicBlock *BB = &*BI;
//
//                for (BasicBlock::iterator II = BB->begin(); II != BB->end(); ++II) {
//                    Instruction *I = &*II;
//
//                    if (isa<DbgInfoIntrinsic>(II)) {
//                        continue;
//                    }
//                    const llvm::DebugLoc &debugInfo = I->getDebugLoc();
//                    auto di = debugInfo.get();
//                    if (di == nullptr) {
//                        continue;
//                    } else {
////                        errs() << " " << debugInfo->getDirectory() << ' '
////                               << debugInfo->getFilename() << ' '
////                               << debugInfo.getLine() << '\n';
////                        break;
//                        if (debugInfo->getDirectory().startswith("/home/")) {
//                            non_sys = true;
//                            errs() << " " << debugInfo->getDirectory() << ' '
//                                   << debugInfo->getFilename() << ' '
//                                   << debugInfo.getLine() << '\n';
//                            break;
//                        } else {
//                            non_sys = false;
//                            break;
//                        }
//                    }
//                }
//                break;
//            }
//            if (non_sys) {
//                setNonSysFunc.insert(F);
//            }
//        }
//        for (Function *F : setNonSysFunc) {
        for (Function &FI : M) {
            Function *F = &FI;
            if (F->isDeclaration()) {
                continue;
            }
            errs() << "FuncName: " << F->getName() << '\n';
            AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(*F).getAAResults();
//            std::unique_ptr<AliasSetTracker> CurAST = make_unique<AliasSetTracker>(AA);
            // detectDeadlockIntra(F);
            std::map<Instruction *, LockInfo> mapLI;
            std::map<Instruction *, DropInfo> mapDI;
            std::map<Instruction *, UnwrapInfo> mapUI;
            traverseForInfo(F, mapLI, mapDI, mapUI);

            std::map<Instruction *, std::set<Instruction *>> mapAliasLock;
            std::map<Instruction *, std::set<BasicBlock *>> mapAliasLockBB;
            for (auto &kv : mapLI) {
                mapAliasLock[kv.first] = std::set<Instruction *>();
                for (auto &kv2 : mapLI) {
                    if (kv.first == kv2.first) {
                        continue;
                    }
//                    kv.second.mutex->print(errs());
//                    errs() << "\n";
//                    kv2.second.mutex->print(errs());
//                    errs() << "\n";
                    auto result = AA.alias(kv.second.mutex, kv2.second.mutex);
//                    errs() << result << "\n";
                    if (result == AliasResult::MustAlias) {
                        mapAliasLock[kv.first].insert(kv2.first);
                        mapAliasLockBB[kv.first].insert(kv2.first->getParent());
                    }
                }
            }

            errs() << "result:\n";

            // Inst: Lock, Inst: Drop
            std::map<Instruction *, std::set<Instruction *>> mapLockDrops;
            for (auto &kv : mapLI) {
                mapLockDrops[kv.first] = std::set<Instruction *>();
//                kv.second.result->print(errs());
//                errs() << "\n";
                Value *result = kv.second.result;
                for (auto i = result->user_begin(); i != result->user_end(); ++i) {
//                    errs() << "\t";
//                    if (*i != kv.first) {
//                        (*i)->print(errs());
//                    }
                    Instruction *II = dyn_cast<Instruction>(*i);
                    if (isCallOrInvokeInst(II)) {
                        Function *FF = getCalledFunc(II);
                        if (!FF) {
                            continue;
                        }
                        if (FF->getName().startswith("_ZN4core6result19Result$LT$T$C$E$GT$6unwrap")) {
                            for (auto j = II->user_begin(); j != II->user_end(); ++j) {
//                                errs() << "\nUnwrap: \t";
//                                (*j)->print(errs());
//                                errs() << "\n";
                                Instruction *III = dyn_cast<Instruction>(*j);
                                if (III->getNumOperands() < 2) {
                                    continue;
                                }
                                Value *V = III->getOperand(1);
//                                errs() << "\nStore:\n";
                                for (auto k = V->user_begin(); k != V->user_end(); ++k) {
                                    (*k)->print(errs());
                                    Instruction *IIII = dyn_cast<Instruction>(*k);
                                    Function *FFF = getCalledFunc(IIII);
                                    if (FFF) {
                                        if (FFF->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                                            mapLockDrops[kv.first].insert(IIII);
//                                            errs() << "\nMatch with ";
//                                            IIII->print(errs());
//                                            errs() << "\n";
                                        }
                                    }
//                                    errs() << "\n";
                                }
                            }
                        } else if (FF->getName().startswith("_ZN4core3ptr18real_drop_in_place")) {
                            mapLockDrops[kv.first].insert(II);
//                            errs() << "\nMatch with ";
//                            II->print(errs());
//                            errs() << "\n";
                        }
                    }
                    // if drop_in_place: then match
                    // if unwrap(): then record unwrap, continue track

//                    errs() << '\n';
                }
//                errs() << "\n";
            }

            std::map<BasicBlock *, std::set<BasicBlock *>> mapBBLockDrops;
            for (auto &kv : mapLockDrops) {
                BasicBlock *LB = kv.first->getParent();
                mapBBLockDrops[LB] = std::set<BasicBlock *>();
                for (auto &I : kv.second) {
                    mapBBLockDrops[LB].insert(I->getParent());
                }
            }

            for (auto &kv : mapLockDrops) {
                errs() << "Checking: ";
                kv.first->print(errs());
                errs() << "\n";
                BasicBlock *Lock = kv.first->getParent();
                std::set<BasicBlock *> Drops;
                for (auto &d : kv.second) {
                    Drops.insert(d->getParent());
                }
                std::set<BasicBlock *> &AliasBB = mapAliasLockBB[kv.first];
                std::list<BasicBlock *> WorkList;
                std::set<BasicBlock *> Visited;
                WorkList.push_back(Lock);
                while (!WorkList.empty()) {
                    BasicBlock *B = WorkList.front();
                    WorkList.pop_front();
                    auto itAlias = AliasBB.find(B);
                    if (itAlias != AliasBB.end()) {
                        errs() << "DeadLock Happens!" << "\n";
                        const llvm::DebugLoc &lockInfo = kv.first->getDebugLoc();
                        kv.first->print(errs());
                        errs() << "\n";
                        auto di1 = lockInfo.get();
                        if (di1) {
                            errs() << " " << lockInfo->getDirectory() << ' '
                                   << lockInfo->getFilename() << ' '
                                   << lockInfo.getLine() << "\n";
                        }
                        Instruction *DoubleLock = nullptr;
                        for (Instruction *DL: mapAliasLock[kv.first]) {
                            if (DL->getParent() == B) {
                                DoubleLock = DL;
                            }
                        }
                        if (!DoubleLock) {
                            assert(false);
                        }
                        DoubleLock->print(errs());
                        errs() << "\n";
                        const llvm::DebugLoc &debugInfo = DoubleLock->getDebugLoc();
                        auto di = debugInfo.get();
                        if (di != nullptr) {

                            errs() << " " << debugInfo->getDirectory() << ' '
                                   << debugInfo->getFilename() << ' '
                                   << debugInfo.getLine() << "\n";
                        }
                        break;
                    }
                    auto it = Drops.find(B);
                    if (it == Drops.end()) {
                        errs() << "Continue\n";
                        Instruction *pTerm = B->getTerminator();
                        for (unsigned i = 0; i < pTerm->getNumSuccessors(); ++i) {
                            BasicBlock *Succ = pTerm->getSuccessor(i);
                            if (Visited.find(Succ) == Visited.end()) {
                                errs() << "Succ:" << Succ->getName() << '\n';
                                WorkList.push_back(Succ);
                                Visited.insert(Succ);
                            }
                        }
                    } else {
                        errs() << "Drop:" << B->getName() << "\n";
                        continue;
                    }
                }
            }
        }
        return false;
    }


//            errs() << "LockInfo\n";
//            std::map<Instruction *, MutexSource> mapMS;
//            for (auto &kv : mapLI) {
//                kv.first->print(errs());
//                errs() << "\n\t";
//                kv.second.result->print(errs());
//                errs() << "\n\t";
//                kv.second.mutex->print(errs());
//                errs() << "\n\t\t";
//                errs() << "Trace:\n";
//
//                MutexSource MS;
//                MS.direct = kv.first;
//                bool ok = trackMutexToSelf(kv.second.mutex, MS);
//                mapMS[kv.first] = MS;
//
////                for (auto it = kv.second.mutex->use_begin(); it != kv.second.mutex->use_end(); ++it) {
////                    errs() << "\t\t";
////                    it->get()->print(errs());
////                    errs() << "\n";
////                    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(it->get())) {
////                        Value *Self = GEP->getOperand(0);
////                        Self->stripPointerCasts()->getType()->getContainedType(0)->print(errs());
////                        errs() << "\n";
////                        if (!isa<StructType>(Self->stripPointerCasts()->getType()->getContainedType(0))) {
////                            errs() << "Self not Struct" << "\n";
////                            continue;
////                        }
////                        Self->print(errs());
////                        errs() << "\n";
////                        for (unsigned i = 1; i < GEP->getNumOperands(); ++i) {
////                            errs() << "index: ";
////                            GEP->getOperand(i)->getType()->print(errs());
////                            errs() << "\n";
////                            errs() << dyn_cast<ConstantInt>(GEP->getOperand(i))->getValue();
////                            errs() << "\n";
////                        }
////                    }
////                    errs() << "\n";
////                }
//            }
//
//            errs() << "mapMS:" << mapMS.size() << "\n";
//            for (auto &kv: mapMS) {
//                kv.second.structTy->print(errs());
//                errs() << ' ';
//                for (auto &i : kv.second.index) {
//                    errs() << i << ',';
//                }
//                errs() << '\n';
//                kv.first->print(errs());
//                errs() << '\n';
//            }
//
////            std::vector<MutexSource> vecMS;
////            std::map<std::size_t, std::set<Instruction *>> mapMSInsts;
////            std::size_t idx = 0;
////            for (auto &kv : mapMS) {
////                Instruction *I = kv.first;
////                MutexSource MS = kv.second;
////                bool exists = false;
////                for (auto it = vecMS.begin(); it != vecMS.end(); ++it) {
////                    if (*it == MS) {
////                        exists = true;
////                        break;
////                    }
////                }
////                if (!exists) {
////                    vecMS.push_back(MS);
////                    mapMSInsts[idx] = { I };
////                    ++idx;
////                } else {
////
////                }
////            }
//
//            errs() << "DropInfo\n";
//            for (auto &kv : mapDI) {
//                kv.first->print(errs());
//                errs() << "\n\t";
//                kv.second.data->print(errs());
//                errs() << "\n";
//            }
//            errs() << "UnwrapInfo\n";
//            for (auto &kv : mapUI) {
//                kv.first->print(errs());
//                errs() << "\n\t";
//                kv.second.result->print(errs());
//                errs() << "\n";
//            }
//        }
//
//        return false;
//    }

//    void PrintPass::printCallChain() {
//        Module &M = *pModule;
//
//        for (Module::iterator FI = M.begin(); FI != M.end(); ++FI) {
//            Function *F = &*FI;
//            int id = GetFunctionID(F);
////            if (id == -1 || id == 0) {
////                continue;
////            }
//
//            bool taken = F->hasAddressTaken();
//
//            std::string caller(F->getName());
//            if (caller.empty()) {
//                continue;
//            }
////            errs() << id << ':';
////            errs() << taken << ':';
////            errs().write_escaped(F->getName()) << "\n";
//
////            if (taken) {
////                for (const Use &U : F->uses()) {
////                    const User *FU = U.getUser();
////                    if (isa<BlockAddress>(FU)) {
////                        continue;
////                    }
////                    FU->dump();
////
////                }
////            }
//
//            for (Function::iterator BI = F->begin(); BI != F->end(); ++BI) {
//
//                BasicBlock *BB = &*BI;
//
//                for (BasicBlock::iterator II = BB->begin(); II != BB->end(); ++II) {
//                    Instruction *I = &*II;
//                    Function *Callee = getCalleeFunc(I);
//                    if (Callee) {
//                        bool taken = Callee->hasAddressTaken();
//                        int id = GetFunctionID(F);
////                        if (id == -1 || id == 0) {
////                            continue;
////                        }
//
//
////                        errs() << id << ':';
////                        errs() << 'X' << ':';
//                        std::string callee_name(Callee->getName());
//                        if (callee_name.empty()) {
//                            continue;
//                        }
//                        errs() << caller << ": ";
//                        errs().write_escaped(Callee->getName()) << '\n';
//                    }
//                }
//            }
//        }
//    }
}

static RegisterPass<printpass::PrintPass> X(
        "print",
        "Print function names",
        false,
        true);

#define DEBUG_TYPE "idassigner"