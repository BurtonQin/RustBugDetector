#include "PrintLock/PrintLock.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"

using namespace llvm;

namespace detector {

    char PrintLock::ID = 0;

    PrintLock::PrintLock() : ModulePass(ID) {}

    void PrintLock::getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
    }

    bool PrintLock::runOnModule(Module &M) {
        this->pModule = &M;

//        for (auto it = M.global_begin(); it != M.global_end(); ++it) {
//            it->print(errs());
//            errs() << '\n';
//        }

        for (Function &F: M) {
            if (F.getName().find("lock17") != -1 ||
                    F.getName().find("read17") != -1 ||
                    F.getName().find("write17") != -1) {
                if (F.getName().startswith("_ZN3std4sync5mutex14Mutex$LT$T$GT$4lock")
                || F.getName().startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$4read")
                || F.getName().startswith("_ZN3std4sync6rwlock15RwLock$LT$T$GT$5write")) {
                    errs() << F.getName() << "\n";
                } else if (F.getName().startswith("_ZN3std") ||
                        F.getName().startswith("_ZN4core3")) {
                    continue;
                } else {
                    auto name = F.getName();
                    auto i = name.find("lock17");
                    if (i != -1 && i > 0) {
                        errs() << i << '\n';
                        if (name[i-1] >= '0' && name[i-1] <= '9') {
                            errs() << name << '\n';
                        }
                    } else {
                        i = name.find("read17");
                        if (i != -1 && i > 0) {
                            if (name[i-1] >= '0' && name[i-1] <= '9') {
                                errs() << name << '\n';
                            }
                        } else {
                            i = name.find("write17");
                            if (i != -1 && i > 0) {
                                if (name[i-1] >= '0' && name[i-1] <= '9') {
                                    errs() << name << '\n';
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }
}

static RegisterPass<detector::PrintLock> X(
        "print",
        "Print related lock funcs",
        false,
        true);