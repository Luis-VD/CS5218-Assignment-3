#include <iostream>
#include <cstdio>
#include <set>
#include <map>
#include <stack>
#include <string>
#include <cmath>
#include <sstream>
#include <iostream>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

const static int POS_LIMIT = 1000;
const static int NEG_LIMIT = -1000;

class interval {
    private:
        int min;
        int max;
    public:
        interval() {
            ;
        }

        interval(int lower, int upper) {
            if (lower > upper) {
                this->min = POS_LIMIT;
                this->max = NEG_LIMIT;
            }
            if (lower <= NEG_LIMIT)
                this->min = NEG_LIMIT;
            else if (lower >= POS_LIMIT)
                this->min = POS_LIMIT;
            else
                this->min = lower;

            if (upper >= POS_LIMIT)
                this->max = POS_LIMIT;
            else if (upper <= NEG_LIMIT)
                this->max = NEG_LIMIT;
            else
                this->max = upper;
        }

        int getMaxVal() {
            return this->max;
        }

        int getMinVal() {
            return this->min;
        }

        void setMinVal(int min) {
            if (min <= NEG_LIMIT){
                this->min = NEG_LIMIT;
            }else if (min >= POS_LIMIT){
                this->min = POS_LIMIT;
            }else{
                this->min = min;
            }
        }

        void setMaxVal(int max) {
            if (max >= POS_LIMIT){
                this->max = POS_LIMIT;
            }else if (max <= NEG_LIMIT){
                this->max = NEG_LIMIT;
            }else{
                this->max = max;
            }
        }

        bool isEmptyInterval() {
            return this->getMinVal() == POS_LIMIT && this->getMaxVal() == NEG_LIMIT;
        }

        std::string toString() {
            if (this->isEmptyInterval()){
                return "[ , ]";
            }
            return "[ " + (this->getMinVal() == NEG_LIMIT ? "NEG_INFINITY" : std::to_string(this->getMinVal())) + " , " +
                   (this->getMaxVal() == POS_LIMIT ? "POS_INFINITY" : std::to_string(this->getMaxVal())) + " ]";
        }
};

std::map<BasicBlock *, std::vector<std::map<Instruction *, interval>>> constraint;

interval addOp(interval var1, interval var2) {
    if (var1.isEmptyInterval()) {
        return var1;
    }
    if (var2.isEmptyInterval()) {
        return var2;
    }
    int min = NEG_LIMIT;
    int max = POS_LIMIT;
    if (var1.getMinVal() != NEG_LIMIT && var2.getMinVal() != NEG_LIMIT) {
        min = var1.getMinVal() + var2.getMinVal();;
    } 
    if (var1.getMaxVal() != POS_LIMIT && var2.getMaxVal() != POS_LIMIT) {
        max = var1.getMaxVal() + var2.getMaxVal();
    }
    return interval(min, max);
}


interval subOp(interval var1, interval var2) {
    if (var1.isEmptyInterval()) {
        return var1;
    }
    if ( var2.isEmptyInterval()) {
        return var2;
    }
    int min = NEG_LIMIT;
    int max = POS_LIMIT;
    if (var1.getMinVal() != NEG_LIMIT && var2.getMaxVal() != POS_LIMIT) {
        min = var1.getMinVal() - var2.getMaxVal();
    }
    if (var1.getMaxVal() != POS_LIMIT && var2.getMinVal() != NEG_LIMIT) {
        max = var1.getMaxVal() - var2.getMinVal();
    }
    return interval(min, max);
}


interval mulOp(interval var1, interval var2) {
    if (var1.isEmptyInterval()) {
        return var1;
    }
    if (var2.isEmptyInterval()) {
        return var2;
    }
    std::vector<int> cmpList;
    cmpList.push_back(var1.getMinVal() * var2.getMinVal());
    cmpList.push_back(var1.getMinVal() * var2.getMaxVal());
    cmpList.push_back(var1.getMaxVal() * var2.getMinVal());
    cmpList.push_back(var1.getMaxVal() * var2.getMaxVal());
    return interval(*(std::min_element(cmpList.begin(), cmpList.end())), *(std::max_element(cmpList.begin(), cmpList.end())));
}

interval divOp(interval var1, interval var2) {
    if(var1.isEmptyInterval() || var2.isEmptyInterval() || (var2.getMinVal() == 0 && var2.getMaxVal() == 0)) {
        return interval(NEG_LIMIT, POS_LIMIT);
    }
    std::vector<int> cmpList;
    if(var2.getMinVal() == 0) {
        cmpList.push_back(var1.getMinVal());
        cmpList.push_back(var1.getMaxVal());
        cmpList.push_back(var1.getMinVal()/var2.getMaxVal());
        cmpList.push_back(var1.getMaxVal()/var2.getMaxVal());
    }else if(var2.getMaxVal() == 0) {
        cmpList.push_back(var1.getMinVal() * -1);
        cmpList.push_back(var1.getMaxVal() * -1);
        cmpList.push_back(var1.getMinVal() / var2.getMinVal());
        cmpList.push_back(var1.getMaxVal() / var2.getMinVal());
    }else if(var2.getMinVal() < 0 && var2.getMaxVal() > 0) {
        cmpList.push_back(var1.getMinVal());
        cmpList.push_back(var1.getMinVal() * -1);
        cmpList.push_back(var1.getMaxVal());
        cmpList.push_back(var1.getMaxVal() * -1);
        cmpList.push_back(var1.getMinVal()/var2.getMinVal());
        cmpList.push_back(var1.getMaxVal()/var2.getMinVal());
        cmpList.push_back(var1.getMinVal()/var2.getMaxVal());
        cmpList.push_back(var1.getMaxVal()/var2.getMaxVal());
    } else {
        cmpList.push_back(var1.getMinVal()/var2.getMinVal());
        cmpList.push_back(var1.getMaxVal()/var2.getMinVal());
        cmpList.push_back(var1.getMinVal()/var2.getMaxVal());
        cmpList.push_back(var1.getMaxVal()/var2.getMaxVal());
    }
    return interval(*(std::min_element(cmpList.begin(), cmpList.end())), *(std::max_element(cmpList.begin(), cmpList.end())));
}

interval sremOp(interval var1, interval var2) {
    if (var1.isEmptyInterval()) {
        return var1;
    }
    if ( var2.isEmptyInterval()) {
        return var2;
    }
    if (var1.getMaxVal() == POS_LIMIT && var2.getMaxVal() == POS_LIMIT) {
        return interval(0, POS_LIMIT);
    } else if (var1.getMaxVal() == POS_LIMIT) {
        return interval(0, var2.getMaxVal() - 1);
    } else if (var2.getMaxVal() == POS_LIMIT) {
        return interval(var1.getMaxVal() < var2.getMaxVal() ? var1.getMaxVal() : 0, std::max(std::abs(var1.getMaxVal()), std::abs(var1.getMaxVal())));
    } else if (var1.getMaxVal() < var2.getMaxVal()) {
        return var1;
    } else {
        return interval(0, std::min(var1.getMaxVal(), var2.getMaxVal()-1));
    }
}


interval intersection(interval v1, interval v2) {
    if (v1.getMinVal() == POS_LIMIT || v2.getMinVal() == POS_LIMIT) {
        return interval(POS_LIMIT, NEG_LIMIT);
    } else if (v1.getMinVal() > v2.getMaxVal() || v2.getMinVal() > v1.getMaxVal()) {
        return interval(POS_LIMIT, NEG_LIMIT);
    } else {
        return interval(std::max(v1.getMinVal(), v2.getMinVal()), std::min(v1.getMaxVal(), v2.getMaxVal()));
    }
}

void updateInterval(interval &value1, interval &value2, interval &originalRange) {
    interval updatedRange = addOp(value2, originalRange);
    value1.setMinVal(std::max(updatedRange.getMinVal(), value1.getMinVal()));
    value1.setMaxVal(std::min(updatedRange.getMaxVal(), value1.getMaxVal()));
    if (value1.getMinVal() > value1.getMaxVal()) {
        value1.setMinVal(POS_LIMIT);
        value1.setMaxVal(NEG_LIMIT);
    }
    updatedRange = addOp(originalRange, value1);
    value2.setMinVal(std::max(updatedRange.getMaxVal() * -1, value2.getMinVal()));
    value2.setMaxVal(std::min(updatedRange.getMinVal() * -1, value2.getMaxVal()));
    if (value2.getMinVal() > value2.getMaxVal()) {
        value2.setMinVal(POS_LIMIT);
        value2.setMaxVal(NEG_LIMIT);
    }
}

std::string getInstructionString(Instruction &I) {
    std::string instructionStr;
    llvm::raw_string_ostream rso(instructionStr);
    I.print(rso);
    return instructionStr;
}

void storeOperation(Instruction &I, std::map<Instruction *, interval> &instrRangeMap, std::map<std::string, Instruction *> &instrMap);

void branchOperation(BasicBlock *BB, Instruction &I, std::map<Instruction *, interval> &instrRangeMap,
               std::map<std::string, Instruction *> &instrMap,
               std::map<BasicBlock *, std::map<Instruction *, interval>> &result);

std::map<Instruction *, interval> updateConstraint(BasicBlock *bb, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> instrRangeMap);

bool blockAnalysis(BasicBlock *BB, std::map<Instruction *, interval> &intervalMap, std::map<std::string, Instruction *> &instrMap, std::map<BasicBlock *, std::map<Instruction *, interval>> &analysisMap,
                  std::map<BasicBlock *, std::map<Instruction *, interval>> &updatedMap);

bool intervalBlockAnalysis(BasicBlock *BB, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &constraintIntervalMap,
                             std::map<std::string, Instruction *> &instrMap, std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &intervalAnalysisMap,
                             std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &updatedMap);

std::vector<interval> getOperandIntervals(Value *operand1, Value *operand2, std::map<Instruction *, interval> &variables, std::map<std::string, Instruction *> &instrMap) {
    interval interval_op1;
    interval interval_op2;
    if (isa<llvm::ConstantInt>(operand2)) {
        interval_op1 = variables[instrMap[getInstructionString(*dyn_cast<Instruction>(operand1))]];
        interval_op2 = interval(dyn_cast<llvm::ConstantInt>(operand2)->getZExtValue(), dyn_cast<llvm::ConstantInt>(operand2)->getZExtValue());
    } else if (isa<llvm::ConstantInt>(operand1)) {
        interval_op1 = interval(dyn_cast<llvm::ConstantInt>(operand1)->getZExtValue(), dyn_cast<llvm::ConstantInt>(operand1)->getZExtValue());
        interval_op2 = variables[instrMap[getInstructionString(*dyn_cast<Instruction>(operand2))]];
    } else {
        interval_op1 = variables[instrMap[getInstructionString(*dyn_cast<Instruction>(operand1))]];
        interval_op2 = variables[instrMap[getInstructionString(*dyn_cast<Instruction>(operand1))]];
    }
    std::vector<interval> results;
    results.push_back(interval_op1);
    results.push_back(interval_op2);
    return results;
}

void branchUpdate(Value *operand1, Value *operand2, interval &originalRange, std::map<Instruction *, interval> &updatedMap, std::map<std::string, Instruction *> &instrMap) {
    if (isa<llvm::ConstantInt>(operand1)) {
        interval range = interval(dyn_cast<llvm::ConstantInt>(operand1)->getZExtValue(), dyn_cast<llvm::ConstantInt>(operand1)->getZExtValue());
        updateInterval(range, updatedMap[instrMap[getInstructionString(*dyn_cast<Instruction>(operand2))]], originalRange);
    } else if (isa<llvm::ConstantInt>(operand2)) {
        interval range = interval(dyn_cast<llvm::ConstantInt>(operand2)->getZExtValue(), dyn_cast<llvm::ConstantInt>(operand2)->getZExtValue());
        updateInterval(updatedMap[instrMap[getInstructionString(*dyn_cast<Instruction>(operand1))]], range, originalRange);
    } else {
        updateInterval(updatedMap[instrMap[getInstructionString(*dyn_cast<Instruction>(operand1))]], updatedMap[instrMap[getInstructionString(*dyn_cast<Instruction>(operand2))]], originalRange);
    }
}

std::map<Instruction *, interval> updateConstraint(BasicBlock *bb, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> instrRangeMap) {
    std::map<Instruction *, interval> updatedSet;
    if (instrRangeMap.size() == 0) {
        return updatedSet;
    }
    std::vector<Instruction *> intersetInstructionSet;
    for (auto iter = instrRangeMap.begin(); iter != instrRangeMap.end(); iter++) {
        if (iter == instrRangeMap.begin()) {
            for (auto instructionMap : iter->second) {
                intersetInstructionSet.push_back(instructionMap.first);
            }
        } else {
            std::vector<Instruction *> tempSet;
            
            for (auto instructionMap : iter->second) {
                tempSet.push_back(instructionMap.first);
            }

            std::vector<Instruction*> tempVector;

            sort(intersetInstructionSet.begin(), intersetInstructionSet.end());
            sort(tempSet.begin(), tempSet.end());

            set_intersection(intersetInstructionSet.begin(),intersetInstructionSet.end(),tempSet.begin(),tempSet.end(),back_inserter(tempVector));
            
            intersetInstructionSet = tempVector;
        }
    }
    for (auto iter = instrRangeMap.begin(); iter != instrRangeMap.end(); iter++) {
        if (iter == instrRangeMap.begin()) {
            for (auto &element : intersetInstructionSet) {
                    updatedSet.insert(std::make_pair(element, iter->second[element]));
            }
        } else {
            for (auto &element : intersetInstructionSet) {
                    updatedSet[element] = interval(std::min(updatedSet[element].getMinVal(), iter->second[element].getMinVal()), std::max(updatedSet[element].getMaxVal(), iter->second[element].getMaxVal()));
            }
        }
    }
    for(auto iter = updatedSet.begin(); iter != updatedSet.end();){
        if(iter->first->getName().size() == 0 && !iter->first->isUsedInBasicBlock(bb)){
            iter = updatedSet.erase(iter);
        }else{
            iter++;
        }
    }
    return updatedSet;
}

int main(int argc, char **argv) {

    LLVMContext &Context = getGlobalContext();
    SMDiagnostic Err;
    Module *M = ParseIRFile(argv[1], Err, Context);
    if (M == nullptr) {
        fprintf(stderr, "error: failed to load LLVM IR file \"%s\"", argv[1]);
        return EXIT_FAILURE;
    }
    Function *F = M->getFunction("main");
    BasicBlock *entryBB = &F->getEntryBlock();

    std::map<BasicBlock *, std::map<Instruction *, interval>> analysisMap;
    std::map<std::string, Instruction *> instrMap;
    std::stack<std::pair<BasicBlock *, std::map<Instruction *, interval>>> traversalStack;
    std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> intervalAnalysisMap;
    std::vector<std::map<Instruction *, interval>> globalConstraintMap;
    std::stack<std::pair<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>>> intervalTraversalStack;
    std::map<Instruction *, interval> emptySet;
    traversalStack.push(std::make_pair(entryBB, emptySet));

    while (!traversalStack.empty()) {
        std::map<BasicBlock *, std::map<Instruction *, interval>> updatedMap;
        auto top = traversalStack.top();
        traversalStack.pop();

        auto changed = blockAnalysis(top.first, top.second, instrMap, analysisMap, updatedMap);
        if (changed) {
            for (auto &p : updatedMap) {
                traversalStack.push(p);
            }
        }
    }

    // generate constraints of the program
    for (auto &instructionMap : analysisMap) {
        for (auto &intervalMap : instructionMap.second) {
            intervalMap.second = interval(NEG_LIMIT, POS_LIMIT);
        }

        BasicBlock *BB = instructionMap.first;
        std::map<Instruction *, interval> intervalMap = instructionMap.second;
        std::map<BasicBlock *, std::map<Instruction *, interval>> result;

        for (auto &I: *BB) {
            if (I.getOpcode() == Instruction::Br) {

                branchOperation(BB, I, intervalMap, instrMap, result);
  
                if (result.size() > 1) {
                    for (auto &constraintMap : result) {
                        constraint[BB].push_back(constraintMap.second);
                    }
                    for (auto iter = constraint[BB][0].begin(); iter != constraint[BB][0].end();) {
                        bool erase = false;
                        for (auto iter1 = constraint[BB][1].begin(); iter1 != constraint[BB][1].end(); iter1++) {
                            if (iter->second.toString() == iter1->second.toString()) {
                                iter = constraint[BB][0].erase(iter);
                                iter1 = constraint[BB][1].erase(iter1);
                                erase = true;
                                break;
                            }
                        }
                        if (!erase) iter++;
                    }
                    for(auto iter = constraint[BB][0].begin(); iter != constraint[BB][0].end();){
                        if(iter->first->getName().size() == 0){
                            iter = constraint[BB][0].erase(iter);
                        }else{
                            iter++;
                        }
                    }
                    for(auto iter = constraint[BB][1].begin(); iter != constraint[BB][1].end();){
                        if(iter->first->getName().size() == 0){
                            iter = constraint[BB][1].erase(iter);
                        }else{
                            iter++;
                        }
                    }
                }
            }
        }
    }

    for (auto constraintMap : constraint) {
        if (constraintMap.second.size() != 0 && constraintMap.second[0].size() != 0) {
            if (globalConstraintMap.size() == 0) {
                globalConstraintMap = constraintMap.second;
            } else {
                std::vector<std::map<Instruction *, interval>> backup = globalConstraintMap;
                globalConstraintMap.clear();

                for (auto constraintVector : constraintMap.second) {
                    for (auto temp_map : backup) {
                        for (auto iter = constraintVector.begin(); iter != constraintVector.end(); iter++) {
                            if (temp_map.find(iter->first) != temp_map.end()) {
                                temp_map.insert(std::make_pair(iter->first, intersection(temp_map.find(iter->first)->second, iter->second)));
                            } else {
                                temp_map.insert(*iter);
                            }
                        }
                        globalConstraintMap.push_back(temp_map);
                    }
                }
            }
        }
    }

    std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> emptyConstraintIntervalMap;
    for (auto &instructionInterval : globalConstraintMap) {
        emptyConstraintIntervalMap.insert(std::make_pair(&instructionInterval, instructionInterval));
    }
    intervalTraversalStack.push(std::make_pair(entryBB, emptyConstraintIntervalMap));

    while (!intervalTraversalStack.empty()) {
        std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> updatedMap;
        auto pair = intervalTraversalStack.top();
        intervalTraversalStack.pop();

        auto changed = intervalBlockAnalysis(pair.first, pair.second, instrMap, intervalAnalysisMap, updatedMap);

        if (changed) {
            for (auto &p : updatedMap) {
                intervalTraversalStack.push(p);
            }
        }
    }

    for (auto &constraintInterval : intervalAnalysisMap) {
        constraintInterval.first->printAsOperand(errs(), false);
        errs() << "\n";
        std::map<Instruction *, interval> result = updateConstraint(constraintInterval.first, constraintInterval.second);

        bool isEmpty = false;
        for (auto &element : result) {
            if (element.second.isEmptyInterval())
                isEmpty = true;
        }
        if (!isEmpty) {
            for (auto &element : result) {
                if(element.first->getName().size()!=0)
                    std::cout << getInstructionString(*element.first) << "  ----> interval range:   " << element.second.toString()
                          << std::endl;
            }
        }
    }
}

bool checkUpdates(std::map<Instruction *, interval> &instrRangeMap, std::map<Instruction *, interval> &analysisMap) {
    bool changed = false;
    for (auto &element : instrRangeMap) {
        if (analysisMap.find(element.first) == analysisMap.end()) {
            analysisMap[element.first] = element.second;
            changed = true;
        } else if (analysisMap[element.first].isEmptyInterval()) {
            if (!element.second.isEmptyInterval()) {
                analysisMap[element.first] = element.second;
                changed = true;
            }
        } else {
            bool subset; 
            if (element.second.getMinVal() == POS_LIMIT && element.second.getMaxVal() == NEG_LIMIT) {
                subset = true;
            }
            else if (analysisMap[element.first].getMinVal() == POS_LIMIT && analysisMap[element.first].getMaxVal() == NEG_LIMIT) {
                subset = false;
            }
            else 
                subset = element.second.getMinVal() >= analysisMap[element.first].getMinVal() && element.second.getMaxVal() <= analysisMap[element.first].getMaxVal();

            if (!subset) {
                analysisMap[element.first].setMinVal(std::min(element.second.getMinVal(), analysisMap[element.first].getMinVal()));
                analysisMap[element.first].setMaxVal(std::max(element.second.getMaxVal(), analysisMap[element.first].getMaxVal()));
                changed = true;
            }
        }
    }
    return changed;
}

void mathOperation(Instruction &I, std::map<Instruction *, interval> &instrRangeMap, std::map<std::string, Instruction *> &instrMap) {
    std::string instructionName = getInstructionString(I);
    interval varRange1, varRange2;
    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1))) {
        varRange1 = instrRangeMap[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)))]];
        varRange2 = instrRangeMap[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)))]];
    } else {
        if(isa<llvm::ConstantInt>(I.getOperand(0))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            std::string varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
            interval range = instrRangeMap[instrMap[varName]];
            varRange1 = interval(value, value);
            varRange2 = range;
        } else if (isa<llvm::ConstantInt>(I.getOperand(1))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            std::string varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
            interval range = instrRangeMap[instrMap[varName]];
            varRange1 = range;
            varRange2 = interval(value, value);
        }
    }
    switch(I.getOpcode()){
        case Instruction::Add: {
            instrRangeMap[instrMap[instructionName]] = addOp(varRange1, varRange2);
            break;
        }
        case Instruction::Sub: {
            instrRangeMap[instrMap[instructionName]] = subOp(varRange1, varRange2);
            break;
        }
        case Instruction::Mul: {
            instrRangeMap[instrMap[instructionName]] = mulOp(varRange1, varRange2);
            break;
        }
        case Instruction::SRem: {
            instrRangeMap[instrMap[instructionName]] = sremOp(varRange1, varRange2);
            break;
        }
    }   
}

void backwardAddOperation(Instruction &I, std::map<Instruction *, interval> &instrRangeMap, std::map<std::string, Instruction *> &instrMap) {
    interval originalRange = instrRangeMap[instrMap[getInstructionString(I)]];
    interval varRange1, varRange2;

    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1))) {
        std::string varName1 = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
        varRange1 = instrRangeMap[instrMap[varName1]];
        std::string varName2 = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
        varRange2 = instrRangeMap[instrMap[varName2]];
        instrRangeMap[instrMap[varName1]] = interval(std::max(varRange1.getMinVal(), originalRange.getMinVal() - varRange2.getMaxVal()), std::min(varRange1.getMaxVal(), originalRange.getMaxVal() - varRange2.getMinVal()));
        instrRangeMap[instrMap[varName2]] = interval(std::max(varRange2.getMinVal(), originalRange.getMinVal() - varRange1.getMaxVal()), std::min(varRange2.getMaxVal(), originalRange.getMaxVal() - varRange1.getMinVal()));
    } else {
        std::string varName;
        if(isa<llvm::ConstantInt>(I.getOperand(0))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
            varRange2 = interval(value, value);
        } else if (isa<llvm::ConstantInt>(I.getOperand(1))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
            varRange2 = interval(value, value);
        }
        instrRangeMap[instrMap[varName]] = subOp(originalRange, varRange2);
    }    
}

void backwardSubOperation(Instruction &I, std::map<Instruction *, interval> &instrRangeMap, std::map<std::string, Instruction *> &instrMap) {
    interval originalRange = instrRangeMap[instrMap[getInstructionString(I)]];
    interval varRange1, varRange2;

    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1))) {
        std::string varName1 = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
        varRange1 = instrRangeMap[instrMap[varName1]];
        std::string varName2 = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
        varRange2 = instrRangeMap[instrMap[varName2]];
        instrRangeMap[instrMap[varName1]] = interval(std::max(varRange1.getMinVal(), subOp(originalRange, varRange2).getMinVal()), std::min(varRange1.getMaxVal(), subOp(originalRange, varRange2).getMaxVal()));
        instrRangeMap[instrMap[varName2]] = interval(std::max(varRange2.getMinVal(), subOp(originalRange, varRange1).getMinVal()), std::min(varRange2.getMaxVal(), subOp(originalRange, varRange1).getMaxVal()));
    } else {
        std::string varName;
        if(isa<llvm::ConstantInt>(I.getOperand(0))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
            varRange2 = interval(value, value);
            instrRangeMap[instrMap[varName]] = subOp(varRange2, originalRange);
        } else if (isa<llvm::ConstantInt>(I.getOperand(1))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
            varRange2 = interval(value, value);
            instrRangeMap[instrMap[varName]] = addOp(originalRange, varRange2);
        }
    }
}

void backwardMulOperation(Instruction &I, std::map<Instruction *, interval> &instrRangeMap, std::map<std::string, Instruction *> &instrMap) {
    interval originalRange = instrRangeMap[instrMap[getInstructionString(I)]];
    interval varRange1, varRange2;

    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1))) {
        std::string varName1 = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
        varRange1 = instrRangeMap[instrMap[varName1]];
        std::string varName2 = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
        varRange2 = instrRangeMap[instrMap[varName2]];
        interval divRange1 = divOp(originalRange, varRange2);
        interval divRange2 = divOp(originalRange, varRange1);
        instrRangeMap[instrMap[varName1]] = interval(std::max(varRange1.getMinVal(), divRange1.getMinVal()), std::min(varRange2.getMaxVal(), divRange1.getMaxVal()));
        instrRangeMap[instrMap[varName2]] = interval(std::max(varRange2.getMinVal(), divRange2.getMinVal()), std::min(varRange2.getMaxVal(), divRange2.getMaxVal()));
    } else {
        std::string varName;
        if(isa<llvm::ConstantInt>(I.getOperand(0))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
            varRange2 = interval(value, value);
        } else if (isa<llvm::ConstantInt>(I.getOperand(1))){
            int value = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            varName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
            varRange2 = interval(value, value);
        }
        instrRangeMap[instrMap[varName]] = divOp(originalRange, varRange2);
    }
}

void backwardLoadOperation(Instruction &I, std::map<Instruction *, interval> &instrRangeMap, std::map<std::string, Instruction *> &instrMap) {
    
    std::string instructionName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));

    if (!instrRangeMap[instrMap[instructionName]].isEmptyInterval()) {
        if (instrRangeMap[instrMap[getInstructionString(I)]].isEmptyInterval()) {
            instrRangeMap[instrMap[instructionName]].setMinVal(POS_LIMIT);
            instrRangeMap[instrMap[instructionName]].setMaxVal(NEG_LIMIT);
        } else {
            instrRangeMap[instrMap[instructionName]].setMinVal(std::max(instrRangeMap[instrMap[instructionName]].getMinVal(), instrRangeMap[instrMap[getInstructionString(I)]].getMinVal()));
            instrRangeMap[instrMap[instructionName]].setMaxVal(std::min(instrRangeMap[instrMap[instructionName]].getMaxVal(), instrRangeMap[instrMap[getInstructionString(I)]].getMaxVal()));
        }
    }
}

void branchOperation(BasicBlock *BB, Instruction &I, std::map<Instruction *, interval> &instrRangeMap, std::map<std::string, Instruction *> &instrMap,
               std::map<BasicBlock *, std::map<Instruction *, interval>> &result) {
    auto *currentInstr = dyn_cast<BranchInst>(&I);
    auto *successor1 = currentInstr->getSuccessor(0);

    if(currentInstr->isConditional()) {
        auto *operand1 = dyn_cast<ICmpInst>(I.getOperand(0))->getOperand(0);
        auto *operand2 = dyn_cast<ICmpInst>(I.getOperand(0))->getOperand(1);
        std::map<Instruction *, interval> branch1 = instrRangeMap;
        std::map<Instruction *, interval> branch2 = instrRangeMap;

        switch (dyn_cast<ICmpInst>(I.getOperand(0))->getSignedPredicate()) {
            case CmpInst::Predicate::ICMP_EQ : {
                interval varRange_branch1(0, 0);
                interval varRange_branch2(NEG_LIMIT, POS_LIMIT);
                branchUpdate(operand1, operand2, varRange_branch1, branch1, instrMap);
                branchUpdate(operand1, operand2, varRange_branch2, branch2, instrMap);
                break;
            }
            case CmpInst::Predicate::ICMP_NE : {
                interval varRange_branch1(NEG_LIMIT, POS_LIMIT);
                interval varRange_branch2(0, 0);
                branchUpdate(operand1, operand2, varRange_branch1, branch1, instrMap);
                branchUpdate(operand1, operand2, varRange_branch2, branch2, instrMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SGT : {
                interval varRange_branch1(1, POS_LIMIT);
                interval varRange_branch2(NEG_LIMIT, 0);
                branchUpdate(operand1, operand2, varRange_branch1, branch1, instrMap);
                branchUpdate(operand1, operand2, varRange_branch2, branch2, instrMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SLT : {
                interval varRange_branch1(NEG_LIMIT, -1);
                interval varRange_branch2(0, POS_LIMIT);
                branchUpdate(operand1, operand2, varRange_branch1, branch1, instrMap);
                branchUpdate(operand1, operand2, varRange_branch2, branch2, instrMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SGE : {
                interval varRange_branch1(0, POS_LIMIT);
                interval varRange_branch2(NEG_LIMIT, -1);
                branchUpdate(operand1, operand2, varRange_branch1, branch1, instrMap);
                branchUpdate(operand1, operand2, varRange_branch2, branch2, instrMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SLE : {
                interval varRange_branch1(NEG_LIMIT, 0);
                interval varRange_branch2(1, POS_LIMIT);
                branchUpdate(operand1, operand2, varRange_branch1, branch1, instrMap);
                branchUpdate(operand1, operand2, varRange_branch2, branch2, instrMap);
                break;
            }
            default: {
                break;
            }
        }

        auto iter = BB->rend();
        bool terminate = false;
        while (iter != BB->rbegin()) {
            iter--;
            switch (iter->getOpcode()) {
                case Instruction::Add: {
                    backwardAddOperation(*iter, branch1, instrMap);
                    backwardAddOperation(*iter, branch2, instrMap);
                }
                case Instruction::Sub: {
                    backwardSubOperation(*iter, branch1, instrMap);
                    backwardSubOperation(*iter, branch2, instrMap);
                    break;
                }
                case Instruction::Mul: {
                    backwardMulOperation(*iter, branch1, instrMap);
                    backwardMulOperation(*iter, branch2, instrMap);
                    break;
                }
                case Instruction::Load: {
                    backwardLoadOperation(*iter, branch1, instrMap);
                    backwardLoadOperation(*iter, branch2, instrMap);
                    break;
                }
                case Instruction::Store: {
                    Value *operand1 = iter->getOperand(0);
                    Value *operand2 = iter->getOperand(1);
                    if (!isa<llvm::ConstantInt>(operand1)) {
                        branch1[instrMap[getInstructionString(*dyn_cast<Instruction>(operand1))]] = branch1[instrMap[getInstructionString(*dyn_cast<Instruction>(operand2))]];
                        branch2[instrMap[getInstructionString(*dyn_cast<Instruction>(operand1))]] = branch2[instrMap[getInstructionString(*dyn_cast<Instruction>(operand2))]];
                    }
                    break;
                }
                default: {
                    break;
                }
            }
        }
        result[successor1] = branch1;
        auto *successor2 = dyn_cast<BasicBlock>(currentInstr->getSuccessor(1));
        result[successor2] = branch2;
    } else {
        result[successor1] = instrRangeMap;
    }
}

bool blockAnalysis(BasicBlock *BB, std::map<Instruction *, interval> &intervalMap, std::map<std::string, Instruction *> &instrMap, 
                  std::map<BasicBlock *, std::map<Instruction *, interval>> &analysisMap, std::map<BasicBlock *, std::map<Instruction *, interval>> &updatedMap) {
    for (auto &I: *BB) {
        std::string instructionStr = getInstructionString(I);
        instrMap[instructionStr] = &I;
        switch (I.getOpcode()) {
            case Instruction::Add: {
                mathOperation(I, intervalMap, instrMap);
                break;
            }
            case Instruction::Sub: {
                mathOperation(I, intervalMap, instrMap);
                break;
            }
            case Instruction::Mul: {
                mathOperation(I, intervalMap, instrMap);
                break;
            }
            case Instruction::SRem: {
                mathOperation(I, intervalMap, instrMap);
                break;
            }
            case Instruction::Alloca: {
                intervalMap[instrMap[getInstructionString(I)]] = interval(NEG_LIMIT, POS_LIMIT);
                break;
            }
            case Instruction::Store: {
                if (isa<llvm::ConstantInt>(I.getOperand(0))) {
                    auto value = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
                    std::string instructionName = getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)));
                    intervalMap[instrMap[instructionName]] = interval(value, value);
                } else {
                    intervalMap[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)))]] = intervalMap[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)))]];
                }
                break;
            }
            case Instruction::Load: {
                std::string str = getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)));
                intervalMap[instrMap[getInstructionString(I)]] = intervalMap[instrMap[str]];
                break;
            }
            case Instruction::Br: {
                branchOperation(BB, I, intervalMap, instrMap, updatedMap);
                return checkUpdates(intervalMap, analysisMap[BB]);
            }
            case Instruction::Ret: {
                return checkUpdates(intervalMap, analysisMap[BB]);
            }
            default: {
                break;
            }
        }
    }
    return false;
}

void intervalMathOperation(BasicBlock *bb, Instruction &I, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &instrRangeMap,
                         std::map<std::string, Instruction *> &instrMap, std::string op) {
    if (instrRangeMap.begin()->first->find(&I) != instrRangeMap.begin()->first->end()) {
        std::map<Instruction *, interval> updatedMap = updateConstraint(bb, instrRangeMap);
        for (auto &element :instrRangeMap) {
            std::map<Instruction *, interval> context = *element.first;
            std::vector<interval> intervalVector = getOperandIntervals(I.getOperand(0), I.getOperand(1), updatedMap, instrMap);
            interval temp = interval(POS_LIMIT, NEG_LIMIT);
            if(op == "add") {
                temp = addOp(intervalVector[0], intervalVector[1]);
            } else if (op == "sub") {
                temp = subOp(intervalVector[0], intervalVector[1]);
            } else if (op == "mul") {
                temp = mulOp(intervalVector[0], intervalVector[1]);
            } else if (op == "srem") {
                temp = sremOp(intervalVector[0], intervalVector[1]);
            }
            if (intersection(temp, context[&I]).isEmptyInterval())
                for (auto &var : element.second)
                    var.second = interval(POS_LIMIT, NEG_LIMIT);
            else {
                element.second = updatedMap;
                element.second[&I] = intersection(temp, context[&I]);
            }
        }
    } else {
        for (auto &element : instrRangeMap) {
            std::map<Instruction *, interval> context = *element.first;
            std::vector<interval> intervalVector = getOperandIntervals(I.getOperand(0), I.getOperand(1), element.second, instrMap);
            interval temp = interval(POS_LIMIT, NEG_LIMIT);
            if(op == "add") {
                temp = addOp(intervalVector[0], intervalVector[1]);
            } else if (op == "sub") {
                temp = subOp(intervalVector[0], intervalVector[1]);
            } else if (op == "mul") {
                temp = mulOp(intervalVector[0], intervalVector[1]);
            } else if (op == "srem") {
                temp = sremOp(intervalVector[0], intervalVector[1]);
            }
            element.second[&I] = temp;
        }
    }
    for (auto &element : instrRangeMap) {
        bool isEmpty = false;
        for (auto &constraint : *element.first) {
            element.second[constraint.first] = intersection(constraint.second, element.second[constraint.first]);
        }
        for (auto &instructionInterval : element.second) {
            if (instructionInterval.second.isEmptyInterval()) {
                isEmpty = true;
                break;
            }
        }
        if (isEmpty) {
            for (auto &instructionInterval : element.second) {
                instructionInterval.second = interval(POS_LIMIT, NEG_LIMIT);
            }
        }
    }
}

void intervalStoreOperation(BasicBlock *bb, Instruction &I, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &instrRangeMap,
                             std::map<std::string, Instruction *> &instrMap) {
    auto operand2Instr = instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(1)))];
    interval varInterval;
    if (instrRangeMap.begin()->first->find(operand2Instr) == instrRangeMap.begin()->first->end()) {
        for (auto &constraintInterval : instrRangeMap) {
            if (isa<llvm::ConstantInt>(I.getOperand(0))) {
                varInterval = interval(dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue(), dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue());
            } else {
                varInterval = constraintInterval.second[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)))]];
            }
            constraintInterval.second[operand2Instr] = varInterval;
        }
    } else {
        std::map<Instruction *, interval> updatedConstraintMap = updateConstraint(bb, instrRangeMap);
        if (isa<llvm::ConstantInt>(I.getOperand(0))) {
            varInterval = interval(dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue(), dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue());
        } else {
            varInterval = updatedConstraintMap[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)))]];
        }
        for (auto &element :instrRangeMap) {
            std::map<Instruction *, interval> constraint = *element.first;
            if (intersection(varInterval, constraint[operand2Instr]).isEmptyInterval()) {
                for (auto &var : element.second){
                    var.second = interval(POS_LIMIT, NEG_LIMIT);
                }
            } else {
                element.second = updatedConstraintMap;
                element.second[operand2Instr] = intersection(varInterval, constraint[operand2Instr]);
            }
        }
    }
    for (auto &element : instrRangeMap) {
        bool isEmpty = false;
        for (auto &constraint : *element.first) {
            element.second[constraint.first] = intersection(constraint.second, element.second[constraint.first]);
        }
        for (auto &instructionInterval : element.second) {
            if (instructionInterval.second.isEmptyInterval()) {
                isEmpty = true;
                break;
            }
        }
        if (isEmpty) {
            for (auto &instructionInterval : element.second) {
                instructionInterval.second = interval(POS_LIMIT, NEG_LIMIT);
            }
        }
    }
}

void intervalLoadOperation(BasicBlock *bb, Instruction &I, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &instrRangeMap, std::map<std::string, Instruction *> &instrMap) {
    if (instrRangeMap.begin()->first->find(&I) == instrRangeMap.begin()->first->end()) {
        for (auto &pair : instrRangeMap) {
            pair.second[&I] = pair.second[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)))]];
        }
    } else {
        std::map<Instruction *, interval> updatedConstraintMap = updateConstraint(bb, instrRangeMap);
        for (auto &element :instrRangeMap) {
            std::map<Instruction *, interval> constraint = *element.first;
            interval varInterval = element.second[instrMap[getInstructionString(*dyn_cast<Instruction>(I.getOperand(0)))]];
            if (intersection(varInterval, constraint[&I]).isEmptyInterval()) {
                for (auto &var : element.second)
                    var.second = interval(POS_LIMIT, NEG_LIMIT);
            } else {
                element.second = updatedConstraintMap;
                element.second[&I] = intersection(varInterval, constraint[&I]);
            }
        }
    }
    for (auto &element : instrRangeMap) {
        bool isEmpty = false;
        for (auto &constraint : *element.first) {
            element.second[constraint.first] = intersection(constraint.second, element.second[constraint.first]);
        }
        for (auto &instructionInterval : element.second) {
            if (instructionInterval.second.isEmptyInterval()) {
                isEmpty = true;
                break;
            }
        }
        if (isEmpty) {
            for (auto &instructionInterval : element.second) {
                instructionInterval.second = interval(POS_LIMIT, NEG_LIMIT);
            }
        }
    }
}

void intervalBranchOperation(BasicBlock *BB, Instruction &I,std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &instrRangeMap,
                          std::map<std::string, Instruction *> &instrMap, std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &updatedBlockIntervalMap) {
    auto *block1 = dyn_cast<BranchInst>(&I)->getSuccessor(0);
    if(dyn_cast<BranchInst>(&I)->isConditional()) {
        auto branch1Constraint = constraint[BB][0];
        auto branch2Constraint = constraint[BB][1];
        std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> branch1 = instrRangeMap;
        std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> branch2 = instrRangeMap;
        for (auto &element : branch1) {
            bool emptyBranch1 = false;
            for (auto &constraintElement : *element.first) {
                if (branch1Constraint.find(constraintElement.first) != branch1Constraint.end() &&
                    intersection(branch1Constraint[constraintElement.first], constraintElement.second).isEmptyInterval()) {
                    emptyBranch1 = true;
                    break;
                }
            }
            if(emptyBranch1){
                for(auto &variable_pair : element.second){
                    variable_pair.second = interval(POS_LIMIT, NEG_LIMIT);
                }
            }
        }
        for (auto &element : branch2) {
            bool emptyBranch2 = false;
            for (auto &constraintElement : *element.first) {
                if (branch2Constraint.find(constraintElement.first) != branch2Constraint.end() &&
                    intersection(branch2Constraint[constraintElement.first], constraintElement.second).isEmptyInterval()) {
                    emptyBranch2 = true;
                    break;
                }
            }
            if(emptyBranch2){
                for(auto &variable_pair : element.second){
                    variable_pair.second = interval(POS_LIMIT, NEG_LIMIT);
                }
            }
        }
        updatedBlockIntervalMap[block1] = branch1;
        auto *block2 = dyn_cast<BasicBlock>(dyn_cast<BranchInst>(&I)->getSuccessor(1));
        updatedBlockIntervalMap[block2] = branch2;
    } else {
        updatedBlockIntervalMap[block1] = instrRangeMap;
    }
    
}

bool intervalCheckUpdates(std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &constraintIntervalMap,
        std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &analysisMap) {
    bool changed = false;
    for (auto &constraintInterval : constraintIntervalMap) {
        std::map<Instruction *, interval> intervalMap = constraintInterval.second;
        std::map<Instruction *, interval> analysisIntervalMap = analysisMap[constraintInterval.first];
        for (auto &element : intervalMap) {
            if (analysisIntervalMap.find(element.first) == analysisIntervalMap.end()) {
                analysisMap[constraintInterval.first][element.first] = element.second;
                changed = true;
            } else if (analysisIntervalMap[element.first].isEmptyInterval()) {
                if (!element.second.isEmptyInterval()) {
                    analysisMap[constraintInterval.first][element.first] = element.second;
                    changed = true;
                }
            } else {
                bool subset; 
                if (element.second.getMinVal() == POS_LIMIT && element.second.getMaxVal() == NEG_LIMIT) {
                    subset = true;
                }
                else if (analysisIntervalMap[element.first].getMinVal() == POS_LIMIT && analysisIntervalMap[element.first].getMaxVal() == NEG_LIMIT) {
                    subset = false;
                }
                else 
                    subset = element.second.getMinVal() >= analysisIntervalMap[element.first].getMinVal() && element.second.getMaxVal() <= analysisIntervalMap[element.first].getMaxVal();

                if (!subset) {
                    analysisMap[constraintInterval.first][element.first].setMinVal(std::min(element.second.getMinVal(), analysisIntervalMap[element.first].getMinVal()));
                    analysisMap[constraintInterval.first][element.first].setMaxVal(std::max(element.second.getMaxVal(), analysisIntervalMap[element.first].getMaxVal()));
                    changed = true;
                }

            } 
        }
    }
    return changed;
}

bool intervalBlockAnalysis(BasicBlock *BB, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &constraintIntervalMap, std::map<std::string, Instruction *> &instrMap,
                             std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &intervalAnalysisMap,
                             std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &updatedMap) {
    for (auto &I: *BB) {
        switch (I.getOpcode()) {
            case Instruction::Add: {
                intervalMathOperation(BB, I, constraintIntervalMap, instrMap, "add");
                break;
            }
            case Instruction::Sub: {
                intervalMathOperation(BB, I, constraintIntervalMap, instrMap, "sub");
                break;
            }
            case Instruction::Mul: {
                intervalMathOperation(BB, I, constraintIntervalMap, instrMap, "mul");
                break;
            }
            case Instruction::SRem: {
                intervalMathOperation(BB, I, constraintIntervalMap, instrMap, "srem");
                break;
            }
            case Instruction::Br: {
                intervalBranchOperation(BB, I, constraintIntervalMap, instrMap, updatedMap);
                return intervalCheckUpdates(constraintIntervalMap, intervalAnalysisMap[BB]);
            }
            case Instruction::Alloca: {
                if (constraintIntervalMap.begin()->first->find(&I) != constraintIntervalMap.begin()->first->end()) {
                    for (auto &element :constraintIntervalMap)
                        element.second = updateConstraint(BB, constraintIntervalMap);
                } else {
                    for (auto &element : constraintIntervalMap)
                        element.second[&I] = interval(NEG_LIMIT, POS_LIMIT);
                }
                for (auto &element : constraintIntervalMap) {
                    bool isEmpty = false;
                    for (auto &constraint : *element.first) {
                        element.second[constraint.first] = intersection(constraint.second, element.second[constraint.first]);
                    }
                    for (auto &instructionInterval : element.second) {
                        if (instructionInterval.second.isEmptyInterval()) {
                            isEmpty = true;
                            break;
                        }
                    }
                    if (isEmpty) {
                        for (auto &instructionInterval : element.second) {
                            instructionInterval.second = interval(POS_LIMIT, NEG_LIMIT);
                        }
                    }
                }
                break;
            }
            case Instruction::Load: {
                intervalLoadOperation(BB, I, constraintIntervalMap, instrMap);
                break;
            }
            case Instruction::Store: {
                intervalStoreOperation(BB, I, constraintIntervalMap, instrMap);
                break;
            }
            case Instruction::Ret: {
                return intervalCheckUpdates(constraintIntervalMap, intervalAnalysisMap[BB]);
            }
            default: {
                break;
            }
        }
    }
    return false;
}
