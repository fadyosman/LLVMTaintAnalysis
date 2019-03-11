#include <llvm/ADT/Statistic.h>
#include <llvm/IR/Function.h>
#include "llvm/IR/CallSite.h"
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>

/*
 * The code works first by analyzing the taint at function level to find if a function passes data to another function using a call instruction
 * the code also detects the "source" and "sink" functions and then uses the function level taint to find if the data is passed from the source
 * directly or through some functions to a dangerous "sink".
 * Currently the code doesn't take into account global variables but it can be added later.
*/

using namespace llvm;

#define DEBUG_TYPE "taintanalyzer"


//Enum with different types of functions.
enum ApiType {
    API_ENTRY,      //Entry functions like main.
    API_SOURCE,     //Source functions where user input enters the applications like "read" and "recv".
    API_SINK,       //Dangerous functions like "strcpy".
    API_SANITIZE,   //Functions that sanitizes inputs.
    API_USERFUNC    //User defined functions.
};

//Struct to define a function.
struct ApiFunc {
    //In case of source function interestingArg is argument that has user tainted data.
    //In case of sink it's the dengerous argument for example the second argument of strcpy.
    int interestingArg;
    //Function name.
    std::string funcName;
    //Function type.
    ApiType type;
};

//Taint Node, a node represents a function in a taint.
struct TaintNode {
    std::string name;
    int arg;
    ApiType type;
};
bool operator==(const TaintNode& n1, const TaintNode& n2)
{
    if(n1.name == n2.name && n1.arg == n2.arg) {
        return true;
    } else {
        return false;
    }
}
//Represents a taint between two functions.
struct TaintEdge {
    TaintNode src;
    TaintNode dst;
};

//TODO : add sanitizer functions (and detect sanitization logic like length checking).

namespace {

struct TaintAnalyzer : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    std::vector<TaintEdge> taintList;
    //Entries for adding an entry for "main" and sink for "strcpy".
    //Those are hardcoded for demonestration purposes but later they will be read from a file (probably protocol buffers file).
    //Vector of the functions to search for (entry, source, sink) later this can be loaded from file, probably I will use protocol buffers.
    std::vector<ApiFunc> apiFuncs;
    //Structs for "strcpy" and "main" functions.
    ApiFunc strcpySink;
    ApiFunc mainEntry;
    TaintAnalyzer() : ModulePass(ID) {}
    bool runOnModule(Module &m) override {
        //strcpy sink.
        strcpySink.interestingArg = 1; //1 is the second argument, so we are interested only if user input reaches the second argument.
        strcpySink.funcName = "strcpy";
        strcpySink.type = API_SINK;
        apiFuncs.push_back(strcpySink);
        //Main function entry.
        mainEntry.interestingArg = 1; //1 is argv, so we are interested in argv.
        mainEntry.funcName = "main";
        mainEntry.type = API_ENTRY;
        apiFuncs.push_back(mainEntry);

        //Looping through functions to find all sources and sinks.
        for (Function &f: m) {
            //Looping through each function argument to analyze the taint.
            for(auto arg = f.arg_begin(); arg != f.arg_end(); ++arg) {
                StringRef argName = arg->getName();
                unsigned argNo = arg->getArgNo();
                //List of local tainted variables.
                std::vector<std::string> taintedVars;
                //The first taint is the function argument.
                taintedVars.push_back(argName);
                //Follow each argument and see if it reaches a sink.
                for (BasicBlock &bb : f) {
                    for (Instruction &i : bb) {
                        unsigned opcode = i.getOpcode();
                        switch (opcode) {
                        case llvm::Instruction::Store:
                        {
                            llvm::StoreInst *storeinst = llvm::dyn_cast<llvm::StoreInst>(&i);
                            //First operand of store.
                            StringRef operand1 = storeinst->getOperand(0)->getName();
                            //Second operand of store.
                            StringRef operand2 = storeinst->getOperand(1)->getName();
                            //Checking if the taintedVars vector contains this input.
                            if (std::find(taintedVars.begin(), taintedVars.end(), operand1) != taintedVars.end())
                            {
                                // Element in vector.
                                // The instruction is loading operand1 into operand2.
                                // So let's add operand2 into our taint list.
                                taintedVars.push_back(operand2);
                            }
                            break;
                        }
                        case llvm::Instruction::Load:
                        {
                            llvm::LoadInst *loadinst = llvm::dyn_cast<llvm::LoadInst>(&i);
                            //Getting the variable that's going to be loaded.
                            StringRef operand = loadinst->getOperand(0)->getName();
                            //Getting the variable that's going to be set.
                            StringRef result = loadinst->getName();
                            if (std::find(taintedVars.begin(), taintedVars.end(), operand) != taintedVars.end())
                            {
                                //The instruction is loading operand into result.
                                //So let's as result into taint list.
                                taintedVars.push_back(result);
                            }
                            break;
                        }
                        case llvm::Instruction::GetElementPtr:
                        {
                            //Same as load and store, adding taint.
                            llvm::GetElementPtrInst *gepinst = llvm::dyn_cast<llvm::GetElementPtrInst>(&i);
                            StringRef operand = gepinst->getOperand(0)->getName();
                            StringRef result = gepinst->getName();
                            if (std::find(taintedVars.begin(), taintedVars.end(), operand) != taintedVars.end())
                            {
                                //The instruction is loading operand into result.
                                //So let's as result into taint list.
                                taintedVars.push_back(result);
                            }
                            break;
                        }
                        //TODO: Write code with if statements to test this module.
                        //TODO: PHI instruction handling for taint analysis, also test against vulnserver and detect all the bugs.
                        case llvm::Instruction::PHI:
                        {
                            llvm::PHINode *phi = llvm::dyn_cast<llvm::PHINode>(&i);
                            break;
                        }
                        case llvm::Instruction::Call:
                        {
                            //TODO: Take functions that reads our tainted input and pass into consideration.

                            //Classifying functions.
                            llvm::CallInst *callinst = llvm::dyn_cast<llvm::CallInst>(&i);
                            Function* calledFunction = callinst->getCalledFunction();
                            //Populating the taints vector contains caller-callee data.

                            TaintEdge taint;
                            taint.src.name = f.getName();
                            taint.dst.name = calledFunction->getName();
                            taint.src.arg = argNo;
                            //Setting the type intially to user defined function.
                            taint.src.type = API_USERFUNC;
                            taint.dst.type = API_USERFUNC;

                            //Checking if the src or the destination is defined as source, entry or sink and change the type.
                            for(ApiFunc s:apiFuncs){
                                if(f.getName() == s.funcName) {
                                    taint.src.type = s.type;
                                }
                                if(calledFunction->getName() == s.funcName) {
                                    taint.dst.type = s.type;
                                }
                            }

                            //Loop through the arguments to find tainted arguments, adding the tainted arguments to the taints vector.
                            int operandIndex = 0;
                            for(auto calledArg = callinst->arg_begin(); calledArg != callinst->arg_end(); ++calledArg) {
                                if (std::find(taintedVars.begin(), taintedVars.end(), calledArg->get()->getName()) != taintedVars.end()) {
                                    taint.dst.arg = operandIndex;
                                    taintList.push_back(taint);
                                }
                                operandIndex++;
                            }
                            break;
                        }
                        default:
                            break;
                        }
                    }
                }

            }
        }
        //Performing the analysis and printing analysis trace for each vulnerability.
        for(auto &t: taintList) {
           if(t.src.type == API_ENTRY) {
                std::vector<TaintNode> trace;
                TaintNode caller = t.src;
                while(caller.name != "") {
                    TaintNode callee = getCallee(caller);
                    trace.push_back(caller);
                    if(callee.type == API_SINK) {
                        for(auto s: apiFuncs) {
                            if(s.funcName == callee.name && s.interestingArg != callee.arg) {
                                //We found a sink but the data is not passed to the interesting argument so ignore it.
                                break;
                            }
                        }
                        //Print the stack trace with emojies to show entry, sink and normal functions.
                        errs()<<"==============================------------==============================\n";
                        errs()<<"\U0001F525 Vulnerability detected: dangerous use of '"<<callee.name<<"' \U0001F525\n";
                        errs()<<"\U0001F500 Analysis Trace (argument index is zero based):\n";
                        trace.push_back(callee);
                        for(auto k :trace) {
                            errs()<<"\t";
                            switch (k.type) {
                            case API_SINK:
                                errs()<<"\U0000274E ";
                                break;
                            case API_ENTRY:
                            case API_SOURCE:
                                errs()<<"\U0001F4E5 ";
                                break;
                            default:
                                errs()<<"\U0001F504 ";
                                break;
                            }
                            errs()<<"Function : "<<k.name<<" argument "<<k.arg<<"\n";
                        }
                        errs()<<"==============================------------==============================\n";
                        break;
                    }
                    caller=callee;
                }
            }
        }
        //We are not modifying the code, so return false.
        return false;
    }
    void getAnalysisUsage(AnalysisUsage &AU) const
    {
        AU.addRequired<CallGraphWrapperPass>();
        AU.setPreservesAll();
    }
private:
    //Helper function to get the callee of a certain node.
    TaintNode getCallee(TaintNode node) {
        for(auto t : taintList) {
            if(t.src == node) {
                return t.dst;
            }
        }
        return TaintNode();
    }
};
}

char TaintAnalyzer::ID = 0;
static RegisterPass<TaintAnalyzer> X("taintanalyzer", "Find if a value from a certain source reaches a certain sink.");
