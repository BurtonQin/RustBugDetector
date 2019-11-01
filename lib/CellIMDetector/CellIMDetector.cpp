#include "CellIMDetector/CellIMDetector.h"

#include <fstream>
#include <string>
#include <set>
#include <stack>

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/TypeFinder.h"

#include "Common/CallerFunc.h"

#define DEBUG_TYPE "CellIMDetector"

using namespace llvm;

namespace detector {

    char CellIMDetector::ID = 0;

    CellIMDetector::CellIMDetector() : ModulePass(ID) {
        PassRegistry &Registry = *PassRegistry::getPassRegistry();
        initializeAAResultsWrapperPassPass(Registry);
    }

    void CellIMDetector::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<AAResultsWrapperPass>();
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
            errs() << "SyncImmuFunc:\n";
            while (getline(myfile, line)) {
                if (line.find("//", 0) == 0) {
                    continue;
                }
                errs() << line << "\n";
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
        static std::set<StringRef> CellIMFuncPrefixes {
                // UnsfeCell
                "_ZN4core4cell19UnsafeCell$LT$T$GT$3get",
                // Cell
                "_ZN4core4cell13Cell$LT$T$GT$3set",
                "_ZN4core4cell13Cell$LT$T$GT$4swap",
                "_ZN4core4cell13Cell$LT$T$GT$7replace",
                "_ZN4core4cell13Cell$LT$T$GT$12replace_with",
                "_ZN4core4cell13Cell$LT$T$GT$6as_ptr",
                "_ZN4core4cell13Cell$LT$T$GT$4take",
                // RefCell
                "_ZN4core4cell16RefCell$LT$T$GT$7replace",
                "_ZN4core4cell16RefCell$LT$T$GT$7replace_with",
                "_ZN4core4cell16RefCell$LT$T$GT$4swap",
                "_ZN4core4cell16RefCell$LT$T$GT$10borrow_mut",
                "_ZN4core4cell16RefCell$LT$T$GT$6as_ptr"
        };
        StringRef Name = F->getName();
        for (StringRef Prefix : CellIMFuncPrefixes) {
            if (Name.contains(Prefix)) {
                return true;
            }
        }
        return false;
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

    static bool containsCellIM (
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

    static bool collectCellIMCallers(
            std::set<Function *> &setSyncImmuFunc,
            std::set<Function *> &setCellIMFunc,
            std::map<Function *, std::map<Instruction *, Function *>> &mapCallerCallSites) {
        for (Function *SyncImmuFunc : setSyncImmuFunc) {
            std::vector<Function *> vecTracker;
            if (containsCellIM(SyncImmuFunc, setCellIMFunc, mapCallerCallSites, vecTracker)) {
                errs() << "\nSync Func Contains Interior Mutability\n";
                errs().write_escaped(SyncImmuFunc->getName()) << "\n";
                errs() << "Track:\n";
                for (Function *F : vecTracker) {
                    errs() << "\t";
                    errs().write_escaped(F->getName()) << "\n";
                }
            }
        }
        return true;
    }

    bool CellIMDetector::runOnModule(Module &M) {
        this->pModule = &M;

        std::set<std::string> setSyncImmuFuncName;
        std::set<Function *> setSyncImmuFunc;
        if (!readSyncImmuFunc(setSyncImmuFuncName)) {
            return false;
        }
        std::map<StringRef, Function *> mapFuncName;
        for (Function &F : M) {
            if (F.begin() != F.end()) {
                StringRef FuncName = F.getName();
                mapFuncName[FuncName] = &F;
            }
        }
        for (StringRef FuncName : setSyncImmuFuncName) {
            Function *F = M.getFunction(FuncName);
            if (F) {
                setSyncImmuFunc.insert(F);
            } else {
                bool NotFound = true;
                for (auto &kv : mapFuncName) {
                    if (kv.first.startswith(FuncName)) {
                        setSyncImmuFunc.insert(kv.second);
                        NotFound = false;
                    }
                }
                if (NotFound) {
                    errs() << FuncName << " Cannot Found!\n";
                }
            }
        }

        std::map<Function *, std::map<Instruction *, Function *>> mapCallerCallSites;
        std::map<Function *, Function *> mapCellIMCallerCallee;
        std::set<Function *> setCellIMFunc;
        std::map<Function *, Function *> Parents;
        for (Function &F : M) {
            if (isCellIMFunc(&F)) {
                setCellIMFunc.insert(&F);
            } else {
                collectCallees(&F, mapCallerCallSites);
            }
        }
        errs() << "CellIMFunc:\n";
        for (Function *F : setCellIMFunc) {
            errs().write_escaped(F->getName()) << "\n";
        }
        collectCellIMCallers(setSyncImmuFunc, setCellIMFunc, mapCallerCallSites);
        return false;
    }

}  // namespace detector


static RegisterPass<detector::CellIMDetector> X(
        "detect",
        "Detect Cell-based Interior Mutability",
        false,
        true);
