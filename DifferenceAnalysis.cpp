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

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

std::set<std::string> processVars(BasicBlock*,std::set<Instruction*>);
std::set<Instruction*> union_sets(std::set<Instruction*>, std::set<Instruction*>);
std::string getSimpleNodeLabel(const BasicBlock *Node);
void printAnalysisMap(std::map<std::string,std::set<Instruction*>> analysisMap);
std::string getSimpleValueLabel(const Value *Val);
std::string getSimpleInstructionLabel(const Instruction *Inst);
std::set<std::string> ourVariables {}; //Initializing the set of ourVariables elements with the one we know. Source
std::set<std::string> allVariables {};
std::map<std::string,int> varValuesMap;
std::map<std::string,int> allVarsMap;
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
    std::map<std::string,std::set<Instruction*>> analysisMap;
    for (auto &BB: *F){
      std::set<Instruction*> emptySet;
    	analysisMap[getSimpleNodeLabel(&BB)] = emptySet;
    }       

    // 3. Traversing the CFG in Depth First Order
    std::stack<std::pair<BasicBlock*,std::set<Instruction*> > > traversalStack;
    BasicBlock* entryBB = &F->getEntryBlock();
    std::set<Instruction*> emptySet;
    std::pair<BasicBlock*,std::set<Instruction*> > analysisNode = std::make_pair(entryBB,emptySet);
    traversalStack.push(analysisNode);
       
    // 4. while the stack is not empty we pop the top analysisNode
    // An updated analysis (list of ourVariables vars) is generated by running the processVars on the analysisNode
    // The updated list of ourVariables vars is unioned with the current list of ourVariables vars for the basic block in the 
    // analysis Map
    // Finally, the successor nodes of the current basic block with the updated list of ourVariables vars is added to the stack
    // Extract updatedVars (The list of ourVariables ourVariables after BB) from BB and blockVars
    // from it, and then we add all its successors to it    
    while(!traversalStack.empty()){
        // Pop the top analysis node from stack
        std::pair<BasicBlock*,std::set<Instruction*> > analysisNode = traversalStack.top();
       	traversalStack.pop();
       	
	    // Extract the basic block and the set of ourVariables ourVariables from  analysisNode
	    BasicBlock* BB = analysisNode.first;
      	std::set<Instruction*> blockVars = analysisNode.second;     

        // Extract updatedVars (The list of ourVariables ourVariables 
	    // after BB) from BB and blockVars
        std::set<Instruction*> updatedVars = processVars(BB,blockVars);
        
        // Update the analysis of node BB in the MAP to the union of currently stored blockVars 
        // and the generated updatedVars
        std::set<Instruction*> unionVars = union_sets(analysisMap[getSimpleNodeLabel(BB)],updatedVars); 
       	analysisMap[getSimpleNodeLabel(BB)] = unionVars;
        
        
        // Extract the last instruction in the stack (Terminator Instruction)
        const TerminatorInst *TInst = BB->getTerminator();
        
	    // Extract the number of successors the terminator instructor has
	    int NSucc = TInst->getNumSuccessors();
	
	    for (int i = 0;  i < NSucc; ++i) {
            // for all successor basic blocks, add them plus the updatedVars to the stack 
            // if fixpoint condition is not met.
            // Fixpoint Condition:
            // We only add successor nodes to the stack if the union of the new list of initialzied ourVariables for 
            // the successor node is different from the currently stored list of initialzied ourVariables
            // for the successor node.
            
            // Load the current stored analysis for a successor node
            BasicBlock *Succ = TInst->getSuccessor(i);    
            std::set<Instruction*> succTaintedVars = analysisMap[getSimpleNodeLabel(Succ)];
	        if (succTaintedVars != unionVars){
	            std::pair<BasicBlock*,std::set<Instruction*> > succAnalysisNode = std::make_pair(Succ,updatedVars);
	           traversalStack.push(succAnalysisNode);
            }     
    	}	
    
    }
    printAnalysisMap(analysisMap);
    return 0;
}

// Input Arguments:
// BB: current Basic Block  
// blockVars: The list of ourVariables vars before BB
// 
// Output:
// updatedVars: The list of ourVariables ourVariables after BB
//
// This function receives a list of ourVariables ourVariables before a basic block
// and returns an updated list of ourVariables ourVariables after the basic block
std::set<std::string> processVars(BasicBlock* BB,
				    std::set<Instruction*> blockVars)
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
      if (getSimpleInstructionLabel(&I)!= "%1"){
        ourVariables.insert(getSimpleInstructionLabel(&I));
        allVariables.insert(getSimpleInstructionLabel(&I));
        varValuesMap[getSimpleInstructionLabel(&I)] = 0; //We assume all declared ourVariables are initialized with 0
        allVarsMap[getSimpleInstructionLabel(&I)] = 0;
        //updatedVars.insert(&I);
      }
    }

    // Check if an Instruction is of the type Store Instruction
    if (isa<StoreInst>(I)){

      Value* left = I.getOperand(0);
      Value* v = I.getOperand(1);
      //If the Storer is a ourVariables element, take action, otherwise ignore
      if (ourVariables.find(getSimpleValueLabel(v))!= ourVariables.end()){
        //Instruction* var = dyn_cast<Instruction>(v);
        //updatedVars.insert(var);
        //ourVariables.insert(getSimpleValueLabel(v));
        varValuesMap[getSimpleValueLabel(v)] = dyn_cast<int>(getSimpleValueLabel(left));
      }
      allVarsMap[getSimpleValueLabel(v)] = dyn_cast<int>(getSimpleValueLabel(left));
      allVariables.insert(getSimpleValueLabel(v));
    }

    //Check if an Instruction is of the type Load Instruction
    if (isa<LoadInst>(I)){
      Value* left = I.getOperand(0);
      //If the instruction is a ourVariables element, add the loaded element to the list of ourVariables elements and the ourVariables var
      /*if (ourVariables.find(getSimpleValueLabel(left))!= ourVariables.end()){
        ourVariables.insert(getSimpleInstructionLabel(&I));
        Instruction* var = dyn_cast<Instruction>(left);
        updatedVars.insert(var);
      }*/
      allVarsMap[getSimpleInstructionLabel(&I)] = allVarsMap[getSimpleValueLabel(left)];
      allVariables.insert(getSimpleInstructionLabel(&I));
    }

    //Example: %13 = add nsw i32 %7, %12
    if (isa<AddInst>(I)){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)]
      } else{
        intLeft = dyn_cast<int>(getSimpleValueLabel(left))
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)]
      } else{
        intRight = dyn_cast<int>(getSimpleValueLabel(right))
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft+intRight;
    }

    if (isa<SubInst>(I)){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      //If the instruction deals with a known ourVariables element (alloca of source) include the instruction as Tainted var
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)]
      } else{
        intLeft = dyn_cast<int>(getSimpleValueLabel(left))
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)]
      } else{
        intRight = dyn_cast<int>(getSimpleValueLabel(right))
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft-intRight;
    }

    if (isa<UdivInst>(I)){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      //If the instruction deals with a known ourVariables element (alloca of source) include the instruction as Tainted var
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)]
      } else{
        intLeft = dyn_cast<int>(getSimpleValueLabel(left))
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)]
      } else{
        intRight = dyn_cast<int>(getSimpleValueLabel(right))
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft/intRight;
    }

    if (isa<SdivInst>(I)){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      //If the instruction deals with a known ourVariables element (alloca of source) include the instruction as Tainted var
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)]
      } else{
        intLeft = dyn_cast<int>(getSimpleValueLabel(left))
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)]
      } else{
        intRight = dyn_cast<int>(getSimpleValueLabel(right))
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft/intRight;
    }

    if (isa<MulInst>(I)){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      //If the instruction deals with a known ourVariables element (alloca of source) include the instruction as Tainted var
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)]
      } else{
        intLeft = dyn_cast<int>(getSimpleValueLabel(left))
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)]
      } else{
        intRight = dyn_cast<int>(getSimpleValueLabel(right))
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft*intRight;
    }

    if (isa<SremInst>(I)){   
      Value* left = I.getOperand(0);
      Value* right = I.getOperand(1);
      //If the instruction deals with a known ourVariables element (alloca of source) include the instruction as Tainted var
      int intLeft = 0;
      int intRight = 0;
      if (allVariables.find(getSimpleValueLabel(left))!= allVariables.end()){
        intLeft = allVarsMap[getSimpleValueLabel(left)]
      } else{
        intLeft = dyn_cast<int>(getSimpleValueLabel(left))
      }
      if (allVariables.find(getSimpleValueLabel(right))!= allVariables.end()){
        intRight = allVarsMap[getSimpleValueLabel(right)]
      } else{
        intRight = dyn_cast<int>(getSimpleValueLabel(right))
      }
      allVarsMap[getSimpleInstructionLabel(&I)] = intLeft%intRight;
    }


  }

  for (auto firstVariable: ourVariables){
    for(auto secondVariable: ourVariables){
      int difference = allVarsMap[firstVariable] - allVarsMap[secondVariable];
      if(difference > largestSeparation){
        largestSeparation = difference;
        std::string updatedDifference = "Largest Separation in Block: " + firstVariable + " --> " + secondVariable + " : " + std::to_string(largestSeparation);
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

// Printing Analysis Map  
// When we exit the loop the analysis have finished and the analysis map will point to the set of 
// ourVariables instructions at each basic block.
void printAnalysisMap(std::map<std::string,std::set<std::string>> analysisMap) {
    for (auto& row : analysisMap){
    	std::set<std::string> blockVars = row.second;
    	std::string BBLabel = row.first;
    	errs() << BBLabel << ":\n";
    	for (std::string var : blockVars){
    		errs() << "\t";
    		var->dump();
    	}
    	errs() << "\n";
    } 
}
