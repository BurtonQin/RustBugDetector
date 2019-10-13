#include "Common/CallerFunc.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/CallSite.h"

using namespace llvm;

bool isCallOrInvokeInst(Instruction *I) {
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

Function *getCalledFunc(Instruction *pInst, CallSite &CS) {
    if (!pInst) {
        return nullptr;
    }
    if (isa<DbgInfoIntrinsic>(pInst)) {
        return nullptr;
    } else if (isa<InvokeInst>(pInst) || isa<CallInst>(pInst)) {
        CS = CallSite(pInst);
        Function *pCalled = CS.getCalledFunction();
        if (pCalled) {
            return pCalled;
        } else {
//            errs() << "Call FuncPtr:" << '\n';
            return nullptr;
        }
    }
    return nullptr;
}
