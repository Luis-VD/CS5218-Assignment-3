/*
DISCLAIMER: Portions of code are re-used from the solution to Assignment 1 and adapted to be used for the Difference Analysis
Figured there was no reason to reinvent the wheel... right?
*/
#include <cstdio>
#include <iostream>
#include <set>
#include <map>
#include <stack>
#include <algorithm>
#include <cstdlib>
#include <sstream>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

std::set<std::string> processVars(BasicBlock*,std::set<std::string>);
std::set<std::string> union_sets(std::set<std::string>, std::set<std::string>);
std::string getSimpleNodeLabel(const BasicBlock *Node);
void printAnalysisMap(std::map<std::string,std::set<std::string>> analysisMap);
std::string getSimpleValueLabel(const Value *Val);
std::string getSimpleInstructionLabel(const Instruction *Inst);
std::set<std::string> ourVariables {}; 
std::set<std::string> allVariables {};
std::map<std::string,int> varValuesMap;
std::map<std::string,int> allVarsMap;
int loopsCounter = 0;
std::string lastFeasibleSeparation;
std::string lastSeparation;
int globalSeparation = 0;
int main(int argc, char **argv)
{
    // Read the IR file.
    LLVMContext &Context = getGlobalContext();
    SMDiagnostic Err;
    // Extract Module M from IR (assuming only one Module exists)
    Module *M = ParseIRFile(argv[1], Err, Context);
    if (M == nullptr)
    {
      fprintf(stderr, "error: failed to load LLVM IR file \"%s\"", argv[1]);
      return EXIT_FAILURE;
    }

    // 1.Extract Function main from Module M
    Function *F = M->getFunction("main");
    
    // 2.Define analysisMap as a mapping of basic block labels to empty set (of instructions):      
    std::map<std::string,std::set<std::string>> analysisMap;
    for (auto &BB: *F){
      std::set<std::string> emptySet;
    	analysisMap[getSimpleNodeLabel(&BB)] = emptySet;
    }       

    // 3. Traversing the CFG in Depth First Order
    std::stack<std::pair<BasicBlock*,std::set<std::string> > > traversalStack;
    BasicBlock* entryBB = &F->getEntryBlock();
    std::set<std::string> emptySet;
    std::pair<BasicBlock*,std::set<std::string> > analysisNode = std::make_pair(entryBB,emptySet);
    traversalStack.push(analysisNode);
       
    // 4. while the stack is not empty we pop the top analysisNode
    // An updated analysis (list of ourVariables vars) is generated by running the processVars on the analysisNode
    // The updated list of ourVariables vars is unioned with the current list of ourVariables vars for the basic block in the 
    // analysis Map 
    while(!traversalStack.empty()){
        // Pop the top analysis node from stack
        std::pair<BasicBlock*,std::set<std::string> > analysisNode = traversalStack.top();
       	traversalStack.pop();
       	
	    // Extract the basic block and the set of ourVariables ourVariables from  analysisNode
	    BasicBlock* BB = analysisNode.first;
      	std::set<std::string> blockVars = analysisNode.second;     

        // Extract updatedVars (The list of ourVariables ourVariables 
	    // after BB) from BB and blockVars
        std::set<std::string> updatedVars = processVars(BB,blockVars);
        
        // Update the analysis of node BB in the MAP to the union of currently stored blockVars 
        // and the generated updatedVars
        std::set<std::string> unionVars = union_sets(analysisMap[getSimpleNodeLabel(BB)],updatedVars); 
       	analysisMap[getSimpleNodeLabel(BB)] = unionVars;
        
        
        // Extract the last instruction in the stack (Terminator Instruction)
        const TerminatorInst *TInst = BB->getTerminator();
        
	    // Extract the number of successors the terminator instructor has
	    int NSucc = TInst->getNumSuccessors();
	
	    for (int i = 0;  i < NSucc; ++i) {

            BasicBlock *Succ = TInst->getSuccessor(i);    
            std::set<std::string> succDiffVars = analysisMap[getSimpleNodeLabel(Succ)];
	        if (succDiffVars != unionVars){
	            std::pair<BasicBlock*,std::set<std::string> > succAnalysisNode = std::make_pair(Succ,updatedVars);
	           traversalStack.push(succAnalysisNode);
            }     
    	}	
    
    }
    errs() << lastFeasibleSeparation <<"\n";
    errs() << lastSeparation <<"\n";

    return 0;
}


std::set<std::string> processVars(BasicBlock* BB,
				    std::set<std::string> blockVars)
{
  std::set<std::string> updatedVars(blockVars);
  int largestSeparation = 0;
  
  // Loop through instructions in BB
  for (auto &I: *BB)
  {
    
    //Check if an Instruction is of the type Alloca Instruction
    if (isa<AllocaInst>(I)){   
      Value* left = I.getOperand(0);
      //If the instruction deals with a known ourVariables element (alloca of source) include the instruction as Tainted var
      if (getSimpleInstructionLabel(&I) == "N"){
        allVariables.insert(getSimpleInstructionLabel(&I));
        allVarsMap[getSimpleInstructionLabel(&I)] = 99;
      }else
      if (getSimpleInstructionLabel(&I)!= "%1"){
        ourVariables.insert(getSimpleInstructionLabel(&I));
        allVariables.insert(getSimpleInstructionLabel(&I));
        varValuesMap[getSimpleInstructionLabel(&I)] = 0; //We assume all declared ourVariables are initialized with 0
        allVarsMap[getSimpleInstructionLabel(&I)] = 0;
      }
    }

    // Check if an Instruction is of the type Store Instruction
    if (isa<StoreInst>(I)){

      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)];
      } else{
        int valLeft;
        std::istringstream iss (getSimpleValueLabel(left));
        iss >> valLeft;
        intLeft = valLeft;
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)];
      } else{
        int valRight;
        std::istringstream iss (getSimpleValueLabel(right));
        iss >> valRight;
        intRight = valRight;
      }
      allVarsMap[getSimpleValueLabel(right)] = intLeft;
      //allVariables.insert(getSimpleValueLabel(right));
    }

    //Check if an Instruction is of the type Load Instruction
    if (isa<LoadInst>(I)){
      Value* left = I.getOperand(0);

      allVarsMap[getSimpleInstructionLabel(&I)] = allVarsMap[getSimpleValueLabel(left)];
      allVariables.insert(getSimpleInstructionLabel(&I));
    }


    if (isa<BranchInst>(I)){ //Check for Branch instructions to perform iterative actions in loops.
	    BranchInst* br = dyn_cast<BranchInst>(&I);
	    if(!br->isConditional())
		    continue;
	    llvm::CmpInst *cmp = dyn_cast<llvm::CmpInst>(br->getCondition());

	    Value* left = I.getOperand(0);
        Value* right = I.getOperand(1);
        int intLeft = 0;
        int intRight = 0;
        if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
            intLeft = allVarsMap[getSimpleValueLabel(left)];
        } else{
            int valLeft;
            std::istringstream iss (getSimpleValueLabel(left));
            iss >> valLeft;
            intLeft = valLeft;
        }
        if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
            intRight = allVarsMap[getSimpleValueLabel(right)];
        } else{
            int valRight;
            std::istringstream iss (getSimpleValueLabel(right));
            iss >> valRight;
            intRight = valRight;
        }
        if(loopsCounter <= 20){
	        switch (cmp->getPredicate()) {
	          case llvm::CmpInst::ICMP_EQ:{
		          if(intLeft == intRight){
                        ;
                    }else{
                        updatedVars.insert("Condition not met, counter: "+std::to_string(loopsCounter));
                    }
		          break;
	          }
	          case llvm::CmpInst::ICMP_NE:{
		          if(intLeft != intRight){
                        ;
                    }else{
                        updatedVars.insert("Condition not met, counter: "+std::to_string(loopsCounter));
                    }
		          break;
	          }
	          case llvm::CmpInst::ICMP_SGT:{
		          if(intLeft > intRight){
                        ;
                    }else{
                        updatedVars.insert("Condition not met, counter: "+std::to_string(loopsCounter));
                    }
		          break;
	          }
	          case llvm::CmpInst::ICMP_SGE:{
		          if(intLeft >= intRight){
                        ;
                    }else{
                        updatedVars.insert("Condition not met, counter: "+std::to_string(loopsCounter));
                    }
		          break;
	          }
	          case llvm::CmpInst::ICMP_SLE:{
		          if(intLeft <= intRight){
                        ;
                    }else{
                        updatedVars.insert("Condition not met, counter: "+std::to_string(loopsCounter));
                    }
		          break;
	          }
	          case llvm::CmpInst::ICMP_SLT:{
		          if(intLeft < intRight){
                        ;
                    }else{
                        updatedVars.insert("Condition not met, counter: "+std::to_string(loopsCounter));
                    }
		          break;
	          }
            }
	      }
        loopsCounter++;
       }

    //Example: %13 = add nsw i32 %7, %12
    if (I.getOpcode() == BinaryOperator::Add){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)];
      } else{
        int valLeft;
        std::istringstream iss (getSimpleValueLabel(left));
        iss >> valLeft;
        intLeft = valLeft;
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)];
      } else{
        int valRight;
        std::istringstream iss (getSimpleValueLabel(right));
        iss >> valRight;
        intRight = valRight;
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft+intRight;
      allVariables.insert(getSimpleInstructionLabel(&I));
    }

    if (I.getOpcode() == BinaryOperator::Sub){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)];
      } else{
        int valLeft;
        std::istringstream iss (getSimpleValueLabel(left));
        iss >> valLeft;
        intLeft = valLeft;
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)];
      } else{
        int valRight;
        std::istringstream iss (getSimpleValueLabel(right));
        iss >> valRight;
        intRight = valRight;
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft-intRight;
      allVariables.insert(getSimpleInstructionLabel(&I));
    }

    if (I.getOpcode() == BinaryOperator::SDiv){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)];
      } else{
        int valLeft;
        std::istringstream iss (getSimpleValueLabel(left));
        iss >> valLeft;
        intLeft = valLeft;
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)];
      } else{
        int valRight;
        std::istringstream iss (getSimpleValueLabel(right));
        iss >> valRight;
        intRight = valRight;
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft/intRight;
      allVariables.insert(getSimpleInstructionLabel(&I));
    }

    if (I.getOpcode() == BinaryOperator::Mul){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)];
      } else{
        int valLeft;
        std::istringstream iss (getSimpleValueLabel(left));
        iss >> valLeft;
        intLeft = valLeft;
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)];
      } else{
        int valRight;
        std::istringstream iss (getSimpleValueLabel(right));
        iss >> valRight;
        intRight = valRight;
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft*intRight;
      allVariables.insert(getSimpleInstructionLabel(&I));
    }

    if (I.getOpcode() == BinaryOperator::SRem){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)];
      } else{
        int valLeft;
        std::istringstream iss (getSimpleValueLabel(left));
        iss >> valLeft;
        intLeft = valLeft;
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)];
      } else{
        int valRight;
        std::istringstream iss (getSimpleValueLabel(right));
        iss >> valRight;
        intRight = valRight;
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft%intRight;
      allVariables.insert(getSimpleInstructionLabel(&I));
    }


  }
  std::string updatedDifference="";
  for (auto firstVariable: ourVariables){
    for(auto secondVariable: ourVariables){
      int difference = allVarsMap[firstVariable] - allVarsMap[secondVariable];
      if(difference > largestSeparation){
        largestSeparation = difference;
        if(loopsCounter <= 20){
            updatedDifference = "Largest Difference: " + firstVariable + " --> " + secondVariable + " : " + std::to_string(largestSeparation);
            if(difference>globalSeparation){
                globalSeparation = difference;
                lastFeasibleSeparation = updatedDifference;
            }
        }else{
            updatedDifference = "Finite bound not found on largest Difference: " + firstVariable + " --> " + secondVariable + " : INFINITE";
            lastSeparation = updatedDifference;
        }
      }
    }
  }
  updatedVars.insert(updatedDifference);


  return updatedVars;
}

// Performs set union
std::set<std::string> union_sets(std::set<std::string>A, std::set<std::string> B)
{
     A.insert(B.cbegin(), B.cend());
     return A;
}


// Printing Basic Block Label 
std::string getSimpleNodeLabel(const BasicBlock *Node) {
    if (!Node->getName().empty())
        return Node->getName().str();
    std::string Str;
    raw_string_ostream OS(Str);
    Node->printAsOperand(OS, false);
    return OS.str();
}
//Printing Value Label
std::string getSimpleValueLabel(const Value *Val) {
    if (!Val->getName().empty())
        return Val->getName().str();
    std::string Str;
    raw_string_ostream OS(Str);
    Val->printAsOperand(OS, false);
    return OS.str();
}
//Printing Instruction Label
std::string getSimpleInstructionLabel(const Instruction *Inst) {
    if (!Inst->getName().empty())
        return Inst->getName().str();
    std::string Str;
    raw_string_ostream OS(Str);
    Inst->printAsOperand(OS, false);
    return OS.str();
}

