#include <cstdio>
#include <iostream>
#include <set>
#include <map>
#include <stack>
#include <string>
#include <cstdlib>
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

class interval {
private:
    int lowBound;
    int highBound;
public:
    interval() {
        ;
    }
    interval(int lower, int upper) {
        if (lower > upper) {
            this->lowBound = posThreshold;
            this->highBound = negThreshold;
        }
        if (lower <= negThreshold)
            this->lowBound = negThreshold;
        else if (lower >= posThreshold)
            this->lowBound = posThreshold;
        else
            this->lowBound = lower;

        if (upper >= posThreshold)
            this->highBound = posThreshold;
        else if (upper <= negThreshold)
            this->highBound = negThreshold;
        else
            this->highBound = upper;
    }
    void setHighBound(int highBound) {
        if (highBound >= posThreshold){
            this->highBound = posThreshold;
        }else if (highBound <= negThreshold){
            this->highBound = negThreshold;
        }else{
            this->highBound = highBound;
        }
    }
    void setLowBound(int lowBound) {
        if (lowBound <= negThreshold){
            this->lowBound = negThreshold;
        }else if (lowBound >= posThreshold){
            this->lowBound = posThreshold;
        }else{
            this->lowBound = lowBound;
        }
    }
    int getHighBound() {
        return this->highBound;
    }
    int getLowBound() {
        return this->lowBound;
    }
    bool hasNoRange() {
        return this->getLowBound() == posThreshold && this->getHighBound() == negThreshold;
    }
    std::string toString() {
        if (this->hasNoRange()){
            return "[ , ]";
        }
        return "[ " + (this->getLowBound() == negThreshold ? "-INF" : std::to_string(this->getLowBound())) + " , " +
               (this->getHighBound() == posThreshold ? "+INF" : std::to_string(this->getHighBound())) + " ]";
    }
};
const static int posThreshold = 9999;
const static int negThreshold = -9999;
void storeOper(Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap);
void isBranchOper(BasicBlock *BB, Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap,
                  std::map<std::string, Instruction *> &varValuesMap,
                  std::map<BasicBlock *, std::map<Instruction *, interval>> &result);
std::map<Instruction *, interval> constraintUpdate(BasicBlock *bb, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> allInstrRangesMap);
bool analyseBB(BasicBlock *BB, std::map<Instruction *, interval> &rangesMap, std::map<std::string, Instruction *> &varValuesMap, std::map<BasicBlock *, std::map<Instruction *, interval>> &analysisMap, std::map<BasicBlock *, std::map<Instruction *, interval>> &updatedMap);
bool checkBasicBlockRange(BasicBlock *BB, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &constIntervalMap,std::map<std::string, Instruction *> &varValuesMap, std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &intervalAnalysisMap,std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &updatedMap);

std::map<BasicBlock *, std::vector<std::map<Instruction *, interval>>> constraint;

interval intersect(interval v1, interval v2) {
    if (v1.getLowBound() == posThreshold || v2.getLowBound() == posThreshold)
    {
        return interval(posThreshold, negThreshold);
    }
    else if (v1.getLowBound() > v2.getHighBound() || v2.getLowBound() > v1.getHighBound())
    {
        return interval(posThreshold, negThreshold);
    }
    else
    {
        return interval(std::max(v1.getLowBound(), v2.getLowBound()), std::min(v1.getHighBound(), v2.getHighBound()));
    }
}

void updateRange(interval &value1, interval &value2, interval &originalRange) {
    interval updated = sumOper(value2, originalRange);
    value1.setLowBound(std::max(updated.getLowBound(), value1.getLowBound()));
    value1.setHighBound(std::min(updated.getHighBound(), value1.getHighBound()));
    if (value1.getLowBound() > value1.getHighBound()) {
        value1.setLowBound(posThreshold);
        value1.setHighBound(negThreshold);
    }
    updated = sumOper(originalRange, value1);
    value2.setLowBound(std::max(updated.getHighBound() * -1, value2.getLowBound()));
    value2.setHighBound(std::min(updated.getLowBound() * -1, value2.getHighBound()));
    if (value2.getLowBound() > value2.getHighBound()) {
        value2.setLowBound(posThreshold);
        value2.setHighBound(negThreshold);
    }
}

std::vector<interval> getOperRanges(Value *firstOp, Value *secondOp, std::map<Instruction *, interval> &variables, std::map<std::string, Instruction *> &varValuesMap) {
    interval rangeLeft;
    interval rangeRight;
    if (isa<llvm::ConstantInt>(secondOp))
    {
        rangeLeft = variables[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(firstOp))]];
        rangeRight = interval(dyn_cast<llvm::ConstantInt>(secondOp)->getZExtValue(), dyn_cast<llvm::ConstantInt>(secondOp)->getZExtValue());
    }
    else if (isa<llvm::ConstantInt>(firstOp))
    {
        rangeLeft = interval(dyn_cast<llvm::ConstantInt>(firstOp)->getZExtValue(), dyn_cast<llvm::ConstantInt>(firstOp)->getZExtValue());
        rangeRight = variables[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(secondOp))]];
    }
    else
    {
        rangeLeft = variables[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(firstOp))]];
        rangeRight = variables[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(firstOp))]];
    }
    std::vector<interval> outputRange;
    outputRange.push_back(rangeLeft);
    outputRange.push_back(rangeRight);
    return outputRange;
}

void branchUpdate(Value *firstOp, Value *secondOp, interval &originalRange, std::map<Instruction *, interval> &updatedMap, std::map<std::string, Instruction *> &varValuesMap) {
    if (isa<llvm::ConstantInt>(firstOp)) {
        interval range = interval(dyn_cast<llvm::ConstantInt>(firstOp)->getZExtValue(), dyn_cast<llvm::ConstantInt>(firstOp)->getZExtValue());
        updateRange(range, updatedMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(secondOp))]], originalRange);
    } else if (isa<llvm::ConstantInt>(secondOp)) {
        interval range = interval(dyn_cast<llvm::ConstantInt>(secondOp)->getZExtValue(), dyn_cast<llvm::ConstantInt>(secondOp)->getZExtValue());
        updateRange(updatedMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(firstOp))]], range, originalRange);
    } else {
        updateRange(updatedMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(firstOp))]], updatedMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(secondOp))]], originalRange);
    }
}

std::map<Instruction *, interval> constraintUpdate(BasicBlock *bb, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> allInstrRangesMap){
    std::map<Instruction *, interval> rangesToUpdate;
    std::vector<Instruction *> instrIntersect;
    if (allInstrRangesMap.size() == 0)
    {
        return rangesToUpdate;
    }
    for (auto it = allInstrRangesMap.begin(); it != allInstrRangesMap.end(); it++)
    {
        if (it == allInstrRangesMap.begin())
        {
            for (auto instrMap : it->second)
            {
                instrIntersect.push_back(instrMap.first);
            }
        }
        else
        {
            std::vector<Instruction *> disposableSet;

            for (auto instrMap : it->second)
            {
                disposableSet.push_back(instrMap.first);
            }

            std::vector<Instruction*> disposableVector;

            sort(instrIntersect.begin(), instrIntersect.end());
            sort(disposableSet.begin(), disposableSet.end());

            set_intersection(instrIntersect.begin(),instrIntersect.end(),disposableSet.begin(),disposableSet.end(),back_inserter(disposableVector));

            instrIntersect = disposableVector;
        }
    }
    for (auto it = allInstrRangesMap.begin(); it != allInstrRangesMap.end(); it++) {
        if (it == allInstrRangesMap.begin())
        {
            for (auto &element : instrIntersect)
            {
                    rangesToUpdate.insert(std::make_pair(element, it->second[element]));
            }
        }
        else
        {
            for (auto &element : instrIntersect)
            {
                    rangesToUpdate[element] = interval(std::min(rangesToUpdate[element].getLowBound(), it->second[element].getLowBound()), std::max(rangesToUpdate[element].getHighBound(), it->second[element].getHighBound()));
            }
        }
    }
    for(auto it = rangesToUpdate.begin(); it != rangesToUpdate.end();){
        if(it->first->getName().size() == 0 && !it->first->isUsedInBasicBlock(bb)){
            it = rangesToUpdate.erase(it);
        }else{
            it++;
        }
    }
    return rangesToUpdate;
}


bool getIntervalChanges(std::map<Instruction *, interval> &allInstrRangesMap, std::map<Instruction *, interval> &analysisMap) {
    bool isDifferent = false;
    for (auto &element : allInstrRangesMap) {
        if (analysisMap.find(element.first) == analysisMap.end()) {
            analysisMap[element.first] = element.second;
            isDifferent = true;
        } else if (analysisMap[element.first].hasNoRange()) {
            if (!element.second.hasNoRange()) {
                analysisMap[element.first] = element.second;
                isDifferent = true;
            }
        } else {
            bool hasInnerSet;
            if (element.second.getLowBound() == posThreshold && element.second.getHighBound() == negThreshold) {
                hasInnerSet = true;
            }
            else if (analysisMap[element.first].getLowBound() == posThreshold && analysisMap[element.first].getHighBound() == negThreshold) {
                hasInnerSet = false;
            }
            else
                hasInnerSet = element.second.getLowBound() >= analysisMap[element.first].getLowBound() && element.second.getHighBound() <= analysisMap[element.first].getHighBound();

            if (!hasInnerSet) {
                analysisMap[element.first].setLowBound(std::min(element.second.getLowBound(), analysisMap[element.first].getLowBound()));
                analysisMap[element.first].setHighBound(std::max(element.second.getHighBound(), analysisMap[element.first].getHighBound()));
                isDifferent = true;
            }
        }
    }
    return isDifferent;
}

void isNumOperation(Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap) {
    std::string instructionLabel = getSimpleLabel(I);
    interval varRangeLeft, varRangeRight;
    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1))) {
        varRangeLeft = allInstrRangesMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)))]];
        varRangeRight = allInstrRangesMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)))]];
    }
    else
    {
        if(isa<llvm::ConstantInt>(I.getOperand(0)))
        {
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            std::string varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
            interval range = allInstrRangesMap[varValuesMap[varLabel]];
            varRangeLeft = interval(numValue, numValue);
            varRangeRight = range;
        }
        else if (isa<llvm::ConstantInt>(I.getOperand(1)))
        {
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            std::string varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
            interval range = allInstrRangesMap[varValuesMap[varLabel]];
            varRangeLeft = range;
            varRangeRight = interval(numValue, numValue);
        }
    }
    switch(I.getOpcode()){
        case Instruction::Add: {
            allInstrRangesMap[varValuesMap[instructionLabel]] = sumOper(varRangeLeft, varRangeRight);
            break;
        }
        case Instruction::Sub: {
            allInstrRangesMap[varValuesMap[instructionLabel]] = subsOper(varRangeLeft, varRangeRight);
            break;
        }
        case Instruction::Mul: {
            allInstrRangesMap[varValuesMap[instructionLabel]] = multOper(varRangeLeft, varRangeRight);
            break;
        }
        case Instruction::SRem: {
            allInstrRangesMap[varValuesMap[instructionLabel]] = sRemOper(varRangeLeft, varRangeRight);
            break;
        }
    }
}

interval sumOper(interval left, interval right) {
    if (left.hasNoRange()) {
        return left;
    }
    if (right.hasNoRange()) {
        return right;
    }
    int lowBound = negThreshold;
    int highBound = posThreshold;
    if (left.getLowBound() != negThreshold && right.getLowBound() != negThreshold) {
        lowBound = left.getLowBound() + right.getLowBound();;
    }
    if (left.getHighBound() != posThreshold && right.getHighBound() != posThreshold) {
        highBound = left.getHighBound() + right.getHighBound();
    }
    return interval(lowBound, highBound);
}

interval subsOper(interval left, interval right) {
    if (left.hasNoRange()) {
        return left;
    }
    if ( right.hasNoRange()) {
        return right;
    }
    int lowBound = negThreshold;
    int highBound = posThreshold;
    if (left.getLowBound() != negThreshold && right.getHighBound() != posThreshold) {
        lowBound = left.getLowBound() - right.getHighBound();
    }
    if (left.getHighBound() != posThreshold && right.getLowBound() != negThreshold) {
        highBound = left.getHighBound() - right.getLowBound();
    }
    return interval(lowBound, highBound);
}


interval multOper(interval left, interval right) {
    if (left.hasNoRange()) {
        return left;
    }
    if (right.hasNoRange()) {
        return right;
    }
    std::vector<int> cmpList;
    cmpList.push_back(left.getLowBound() * right.getLowBound());
    cmpList.push_back(left.getLowBound() * right.getHighBound());
    cmpList.push_back(left.getHighBound() * right.getLowBound());
    cmpList.push_back(left.getHighBound() * right.getHighBound());
    return interval(*(std::min_element(cmpList.begin(), cmpList.end())), *(std::max_element(cmpList.begin(), cmpList.end())));
}

interval divOper(interval left, interval right) {
    if(left.hasNoRange() || right.hasNoRange() || (right.getLowBound() == 0 && right.getHighBound() == 0)) {
        return interval(negThreshold, posThreshold);
    }
    std::vector<int> cmpList;
    if(right.getLowBound() == 0)
    {
        cmpList.push_back(left.getLowBound());
        cmpList.push_back(left.getHighBound());
        cmpList.push_back(left.getLowBound()/right.getHighBound());
        cmpList.push_back(left.getHighBound()/right.getHighBound());
    }
    else if(right.getHighBound() == 0)
    {
        cmpList.push_back(left.getLowBound() * -1);
        cmpList.push_back(left.getHighBound() * -1);
        cmpList.push_back(left.getLowBound() / right.getLowBound());
        cmpList.push_back(left.getHighBound() / right.getLowBound());
    }
    else if(right.getLowBound() < 0 && right.getHighBound() > 0)
    {
        cmpList.push_back(left.getLowBound());
        cmpList.push_back(left.getLowBound() * -1);
        cmpList.push_back(left.getHighBound());
        cmpList.push_back(left.getHighBound() * -1);
        cmpList.push_back(left.getLowBound()/right.getLowBound());
        cmpList.push_back(left.getHighBound()/right.getLowBound());
        cmpList.push_back(left.getLowBound()/right.getHighBound());
        cmpList.push_back(left.getHighBound()/right.getHighBound());
    }
    else
    {
        cmpList.push_back(left.getLowBound()/right.getLowBound());
        cmpList.push_back(left.getHighBound()/right.getLowBound());
        cmpList.push_back(left.getLowBound()/right.getHighBound());
        cmpList.push_back(left.getHighBound()/right.getHighBound());
    }
    return interval(*(std::min_element(cmpList.begin(), cmpList.end())), *(std::max_element(cmpList.begin(), cmpList.end())));
}

interval sRemOper(interval left, interval right) {
    if (left.hasNoRange()) {
        return left;
    }
    if ( right.hasNoRange()) {
        return right;
    }
    if (left.getHighBound() == posThreshold && right.getHighBound() == posThreshold) {
        return interval(0, posThreshold);
    } else if (left.getHighBound() == posThreshold) {
        return interval(0, right.getHighBound() - 1);
    } else if (right.getHighBound() == posThreshold) {
        return interval(left.getHighBound() < right.getHighBound() ? left.getHighBound() : 0, std::max(std::abs(left.getHighBound()), std::abs(left.getHighBound())));
    } else if (left.getHighBound() < right.getHighBound()) {
        return left;
    } else {
        return interval(0, std::min(left.getHighBound(), right.getHighBound()-1));
    }
}

void reverseSumOper(Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap) {
    interval originalRange = allInstrRangesMap[varValuesMap[getSimpleLabel(I)]];
    interval varRangeLeft, varRangeRight;
    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1)))
    {
        std::string varName1 = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
        varRangeLeft = allInstrRangesMap[varValuesMap[varName1]];
        std::string varName2 = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
        varRangeRight = allInstrRangesMap[varValuesMap[varName2]];
        allInstrRangesMap[varValuesMap[varName1]] = interval(std::max(varRangeLeft.getLowBound(), originalRange.getLowBound() - varRangeRight.getHighBound()), std::min(varRangeLeft.getHighBound(), originalRange.getHighBound() - varRangeRight.getLowBound()));
        allInstrRangesMap[varValuesMap[varName2]] = interval(std::max(varRangeRight.getLowBound(), originalRange.getLowBound() - varRangeLeft.getHighBound()), std::min(varRangeRight.getHighBound(), originalRange.getHighBound() - varRangeLeft.getLowBound()));
    }
    else
    {
        std::string varLabel;
        if(isa<llvm::ConstantInt>(I.getOperand(0)))
        {
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
            varRangeRight = interval(numValue, numValue);
        }
        else if (isa<llvm::ConstantInt>(I.getOperand(1)))
        {
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
            varRangeRight = interval(numValue, numValue);
        }
        allInstrRangesMap[varValuesMap[varLabel]] = subsOper(originalRange, varRangeRight);
    }
}

void reverseSubstractOper(Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap) {
    interval originalRange = allInstrRangesMap[varValuesMap[getSimpleLabel(I)]];
    interval varRangeLeft, varRangeRight;

    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1))) {
        std::string varName1 = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
        varRangeLeft = allInstrRangesMap[varValuesMap[varName1]];
        std::string varName2 = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
        varRangeRight = allInstrRangesMap[varValuesMap[varName2]];
        allInstrRangesMap[varValuesMap[varName1]] = interval(std::max(varRangeLeft.getLowBound(), subsOper(originalRange, varRangeRight).getLowBound()), std::min(varRangeLeft.getHighBound(), subsOper(originalRange, varRangeRight).getHighBound()));
        allInstrRangesMap[varValuesMap[varName2]] = interval(std::max(varRangeRight.getLowBound(), subsOper(originalRange, varRangeLeft).getLowBound()), std::min(varRangeRight.getHighBound(), subsOper(originalRange, varRangeLeft).getHighBound()));
    }
    else
    {
        std::string varLabel;
        if(isa<llvm::ConstantInt>(I.getOperand(0)))
        {
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
            varRangeRight = interval(numValue, numValue);
            allInstrRangesMap[varValuesMap[varLabel]] = subsOper(varRangeRight, originalRange);
        }
        else if (isa<llvm::ConstantInt>(I.getOperand(1)))
        {
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
            varRangeRight = interval(numValue, numValue);
            allInstrRangesMap[varValuesMap[varLabel]] = sumOper(originalRange, varRangeRight);
        }
    }
}

void reverseMultOper(Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap) {
    interval originalRange = allInstrRangesMap[varValuesMap[getSimpleLabel(I)]];
    interval varRangeLeft, varRangeRight;

    if(!isa<llvm::ConstantInt>(I.getOperand(0)) && !isa<llvm::ConstantInt>(I.getOperand(1))) {
        std::string varName1 = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
        varRangeLeft = allInstrRangesMap[varValuesMap[varName1]];
        std::string varName2 = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
        varRangeRight = allInstrRangesMap[varValuesMap[varName2]];
        interval divRange1 = divOper(originalRange, varRangeRight);
        interval divRange2 = divOper(originalRange, varRangeLeft);
        allInstrRangesMap[varValuesMap[varName1]] = interval(std::max(varRangeLeft.getLowBound(), divRange1.getLowBound()), std::min(varRangeRight.getHighBound(), divRange1.getHighBound()));
        allInstrRangesMap[varValuesMap[varName2]] = interval(std::max(varRangeRight.getLowBound(), divRange2.getLowBound()), std::min(varRangeRight.getHighBound(), divRange2.getHighBound()));
    }
    else
    {
        std::string varLabel;
        if(isa<llvm::ConstantInt>(I.getOperand(0))){
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
            varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
            varRangeRight = interval(numValue, numValue);
        }
        else if (isa<llvm::ConstantInt>(I.getOperand(1)))
        {
            int numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(1))->getZExtValue();
            varLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
            varRangeRight = interval(numValue, numValue);
        }
        allInstrRangesMap[varValuesMap[varLabel]] = divOper(originalRange, varRangeRight);
    }
}

void reverseLoadOper(Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap) {

    std::string instructionLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));

    if (!allInstrRangesMap[varValuesMap[instructionLabel]].hasNoRange()) {
        if (allInstrRangesMap[varValuesMap[getSimpleLabel(I)]].hasNoRange()) {
            allInstrRangesMap[varValuesMap[instructionLabel]].setLowBound(posThreshold);
            allInstrRangesMap[varValuesMap[instructionLabel]].setHighBound(negThreshold);
        }
        else
        {
            allInstrRangesMap[varValuesMap[instructionLabel]].setLowBound(std::max(allInstrRangesMap[varValuesMap[instructionLabel]].getLowBound(), allInstrRangesMap[varValuesMap[getSimpleLabel(I)]].getLowBound()));
            allInstrRangesMap[varValuesMap[instructionLabel]].setHighBound(std::min(allInstrRangesMap[varValuesMap[instructionLabel]].getHighBound(), allInstrRangesMap[varValuesMap[getSimpleLabel(I)]].getHighBound()));
        }
    }
}

void isBranchOper(BasicBlock *BB, Instruction &I, std::map<Instruction *, interval> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap, std::map<BasicBlock *, std::map<Instruction *, interval>> &result){
    auto *currInstr = dyn_cast<BranchInst>(&I);
    auto *nextOneInstr = currInstr->getSuccessor(0);
    if(currInstr->isConditional())
    {
        auto *firstOp = dyn_cast<ICmpInst>(I.getOperand(0))->getOperand(0);
        auto *secondOp = dyn_cast<ICmpInst>(I.getOperand(0))->getOperand(1);
        std::map<Instruction *, interval> leftBranch = allInstrRangesMap;
        std::map<Instruction *, interval> rightBranch = allInstrRangesMap;

        switch (dyn_cast<ICmpInst>(I.getOperand(0))->getSignedPredicate()) {
            case CmpInst::Predicate::ICMP_EQ : {
                interval varRangeLeftBranch(0, 0);
                interval varRangeRightBranch(negThreshold, posThreshold);
                branchUpdate(firstOp, secondOp, varRangeLeftBranch, leftBranch, varValuesMap);
                branchUpdate(firstOp, secondOp, varRangeRightBranch, rightBranch, varValuesMap);
                break;
            }
            case CmpInst::Predicate::ICMP_NE : {
                interval varRangeLeftBranch(negThreshold, posThreshold);
                interval varRangeRightBranch(0, 0);
                branchUpdate(firstOp, secondOp, varRangeLeftBranch, leftBranch, varValuesMap);
                branchUpdate(firstOp, secondOp, varRangeRightBranch, rightBranch, varValuesMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SGT : {
                interval varRangeLeftBranch(1, posThreshold);
                interval varRangeRightBranch(negThreshold, 0);
                branchUpdate(firstOp, secondOp, varRangeLeftBranch, leftBranch, varValuesMap);
                branchUpdate(firstOp, secondOp, varRangeRightBranch, rightBranch, varValuesMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SLT : {
                interval varRangeLeftBranch(negThreshold, -1);
                interval varRangeRightBranch(0, posThreshold);
                branchUpdate(firstOp, secondOp, varRangeLeftBranch, leftBranch, varValuesMap);
                branchUpdate(firstOp, secondOp, varRangeRightBranch, rightBranch, varValuesMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SGE : {
                interval varRangeLeftBranch(0, posThreshold);
                interval varRangeRightBranch(negThreshold, -1);
                branchUpdate(firstOp, secondOp, varRangeLeftBranch, leftBranch, varValuesMap);
                branchUpdate(firstOp, secondOp, varRangeRightBranch, rightBranch, varValuesMap);
                break;
            }
            case CmpInst::Predicate::ICMP_SLE : {
                interval varRangeLeftBranch(negThreshold, 0);
                interval varRangeRightBranch(1, posThreshold);
                branchUpdate(firstOp, secondOp, varRangeLeftBranch, leftBranch, varValuesMap);
                branchUpdate(firstOp, secondOp, varRangeRightBranch, rightBranch, varValuesMap);
                break;
            }
            default: {
                break;
            }
        }

        auto it = BB->rend();
        bool terminate = false;
        while (it != BB->rbegin()) {
            it--;
            switch (it->getOpcode()) {
                case Instruction::Add: {
                    reverseSumOper(*it, leftBranch, varValuesMap);
                    reverseSumOper(*it, rightBranch, varValuesMap);
                }
                case Instruction::Sub: {
                    reverseSubstractOper(*it, leftBranch, varValuesMap);
                    reverseSubstractOper(*it, rightBranch, varValuesMap);
                    break;
                }
                case Instruction::Mul: {
                    reverseMultOper(*it, leftBranch, varValuesMap);
                    reverseMultOper(*it, rightBranch, varValuesMap);
                    break;
                }
                case Instruction::Load: {
                    reverseLoadOper(*it, leftBranch, varValuesMap);
                    reverseLoadOper(*it, rightBranch, varValuesMap);
                    break;
                }
                case Instruction::Store: {
                    Value *firstOp = it->getOperand(0);
                    Value *secondOp = it->getOperand(1);
                    if (!isa<llvm::ConstantInt>(firstOp)) {
                        leftBranch[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(firstOp))]] = leftBranch[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(secondOp))]];
                        rightBranch[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(firstOp))]] = rightBranch[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(secondOp))]];
                    }
                    break;
                }
                default: {
                    break;
                }
            }
        }
        result[nextOneInstr] = leftBranch;
        auto *successor2 = dyn_cast<BasicBlock>(currInstr->getSuccessor(1));
        result[successor2] = rightBranch;
    } else {
        result[nextOneInstr] = allInstrRangesMap;
    }
}

bool analyseBB(BasicBlock *BB, std::map<Instruction *, interval> &rangesMap, std::map<std::string, Instruction *> &varValuesMap, std::map<BasicBlock *, std::map<Instruction *, interval>> &analysisMap, std::map<BasicBlock *, std::map<Instruction *, interval>> &updatedMap)
{
    for (auto &I: *BB)
    {
        std::string instructionLabel = getSimpleLabel(I);
        varValuesMap[instructionLabel] = &I;
        switch (I.getOpcode())
        {
            case Instruction::Add:
            {
                isNumOperation(I, rangesMap, varValuesMap);
                break;
            }
            case Instruction::Sub:
            {
                isNumOperation(I, rangesMap, varValuesMap);
                break;
            }
            case Instruction::Mul:
            {
                isNumOperation(I, rangesMap, varValuesMap);
                break;
            }
            case Instruction::SRem:
            {
                isNumOperation(I, rangesMap, varValuesMap);
                break;
            }
            case Instruction::Alloca:
            {
                rangesMap[varValuesMap[getSimpleLabel(I)]] = interval(negThreshold, posThreshold);
                break;
            }
            case Instruction::Store:
            {
                if (isa<llvm::ConstantInt>(I.getOperand(0))) {
                    auto numValue = dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue();
                    std::string instructionLabel = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)));
                    rangesMap[varValuesMap[instructionLabel]] = interval(numValue, numValue);
                } else {
                    rangesMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)))]] = rangesMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)))]];
                }
                break;
            }
            case Instruction::Load:
            {
                std::string str = getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)));
                rangesMap[varValuesMap[getSimpleLabel(I)]] = rangesMap[varValuesMap[str]];
                break;
            }
            case Instruction::Br:
            {
                isBranchOper(BB, I, rangesMap, varValuesMap, updatedMap);
                return getIntervalChanges(rangesMap, analysisMap[BB]);
            }
            case Instruction::Ret:
            {
                return getIntervalChanges(rangesMap, analysisMap[BB]);
            }
            default: {
                break;
            }
        }
    }
    return false;
}

void rangeMathOper(BasicBlock *bb, Instruction &I, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap, std::string operType)
{
    if (allInstrRangesMap.begin()->first->find(&I) != allInstrRangesMap.begin()->first->end()) {
        std::map<Instruction *, interval> updatedMap = constraintUpdate(bb, allInstrRangesMap);
        for (auto &element :allInstrRangesMap) {
            std::map<Instruction *, interval> contMap = *element.first;
            std::vector<interval> intervalVector = getOperRanges(I.getOperand(0), I.getOperand(1), updatedMap, varValuesMap);
            interval temp = interval(posThreshold, negThreshold);
            if(operType == "add") {
                temp = sumOper(intervalVector[0], intervalVector[1]);
            } else if (operType == "sub") {
                temp = subsOper(intervalVector[0], intervalVector[1]);
            } else if (operType == "mul") {
                temp = multOper(intervalVector[0], intervalVector[1]);
            } else if (operType == "srem") {
                temp = sRemOper(intervalVector[0], intervalVector[1]);
            }
            if (intersect(temp, contMap[&I]).hasNoRange())
                for (auto &var : element.second)
                    var.second = interval(posThreshold, negThreshold);
            else {
                element.second = updatedMap;
                element.second[&I] = intersect(temp, contMap[&I]);
            }
        }
    } else {
        for (auto &element : allInstrRangesMap) {
            std::map<Instruction *, interval> contMap = *element.first;
            std::vector<interval> intervalVector = getOperRanges(I.getOperand(0), I.getOperand(1), element.second, varValuesMap);
            interval temp = interval(posThreshold, negThreshold);
            if(operType == "add") {
                temp = sumOper(intervalVector[0], intervalVector[1]);
            } else if (operType == "sub") {
                temp = subsOper(intervalVector[0], intervalVector[1]);
            } else if (operType == "mul") {
                temp = multOper(intervalVector[0], intervalVector[1]);
            } else if (operType == "srem") {
                temp = sRemOper(intervalVector[0], intervalVector[1]);
            }
            element.second[&I] = temp;
        }
    }
    for (auto &element : allInstrRangesMap) {
        bool hasNone = false;
        for (auto &constraint : *element.first) {
            element.second[constraint.first] = intersect(constraint.second, element.second[constraint.first]);
        }
        for (auto &instructionInterval : element.second) {
            if (instructionInterval.second.hasNoRange()) {
                hasNone = true;
                break;
            }
        }
        if (hasNone) {
            for (auto &instructionInterval : element.second) {
                instructionInterval.second = interval(posThreshold, negThreshold);
            }
        }
    }
}

void processStoreOperation(BasicBlock *bb, Instruction &I, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &allInstrRangesMap,
                             std::map<std::string, Instruction *> &varValuesMap)
{
    auto instrFromOp = varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(1)))];
    interval variablesInter;
    if (allInstrRangesMap.begin()->first->find(instrFromOp) == allInstrRangesMap.begin()->first->end()) {
        for (auto &givenInterval : allInstrRangesMap) {
            if (isa<llvm::ConstantInt>(I.getOperand(0))) {
                variablesInter = interval(dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue(), dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue());
            }
            else {
                variablesInter = givenInterval.second[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)))]];
            }
            givenInterval.second[instrFromOp] = variablesInter;
        }
    } else {
        std::map<Instruction *, interval> updatedConstraintMap = constraintUpdate(bb, allInstrRangesMap);
        if (isa<llvm::ConstantInt>(I.getOperand(0))) {
            variablesInter = interval(dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue(), dyn_cast<llvm::ConstantInt>(I.getOperand(0))->getZExtValue());
        }
        else {
            variablesInter = updatedConstraintMap[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)))]];
        }
        for (auto &element :allInstrRangesMap) {
            std::map<Instruction *, interval> constraint = *element.first;
            if (intersect(variablesInter, constraint[instrFromOp]).hasNoRange()) {
                for (auto &var : element.second){
                    var.second = interval(posThreshold, negThreshold);
                }
            }
            else {
                element.second = updatedConstraintMap;
                element.second[instrFromOp] = intersect(variablesInter, constraint[instrFromOp]);
            }
        }
    }
    for (auto &element : allInstrRangesMap) {
        bool hasNone = false;
        for (auto &constraint : *element.first) {
            element.second[constraint.first] = intersect(constraint.second, element.second[constraint.first]);
        }
        for (auto &instructionInterval : element.second)
        {
            if (instructionInterval.second.hasNoRange())
            {
                hasNone = true;
                break;
            }
        }
        if (hasNone)
        {
            for (auto &instructionInterval : element.second)
            {
                instructionInterval.second = interval(posThreshold, negThreshold);
            }
        }
    }
}

void processLoadOperation(BasicBlock *bb, Instruction &I, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap) {
    if (allInstrRangesMap.begin()->first->find(&I) == allInstrRangesMap.begin()->first->end()) {
        for (auto &pair : allInstrRangesMap) {
            pair.second[&I] = pair.second[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)))]];
        }
    } else {
        std::map<Instruction *, interval> updatedConstraintMap = constraintUpdate(bb, allInstrRangesMap);
        for (auto &element :allInstrRangesMap) {
            std::map<Instruction *, interval> constraint = *element.first;
            interval variablesInter = element.second[varValuesMap[getSimpleLabel(*dyn_cast<Instruction>(I.getOperand(0)))]];
            if (intersect(variablesInter, constraint[&I]).hasNoRange()) {
                for (auto &var : element.second) var.second = interval(posThreshold, negThreshold);
            }
        else {
                element.second = updatedConstraintMap;
                element.second[&I] = intersect(variablesInter, constraint[&I]);
            }
        }
    }
    for (auto &element : allInstrRangesMap) {
        bool hasNone = false;
        for (auto &constraint : *element.first)
        {
            element.second[constraint.first] = intersect(constraint.second, element.second[constraint.first]);
        }
        for (auto &instructionInterval : element.second)
        {
            if (instructionInterval.second.hasNoRange())
            {
                hasNone = true;
                break;
            }
        }
        if (hasNone)
        {
            for (auto &instructionInterval : element.second)
            {
                instructionInterval.second = interval(posThreshold, negThreshold);
            }
        }
    }
}

void processBranchOperation(BasicBlock *BB, Instruction &I,std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &allInstrRangesMap, std::map<std::string, Instruction *> &varValuesMap, std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &updatedBlockIntervalMap)
{
    auto *leftBlock = dyn_cast<BranchInst>(&I)->getSuccessor(0);
    if(dyn_cast<BranchInst>(&I)->isConditional()) {
        auto leftBranchConstr = constraint[BB][0];
        auto rightBranchConstr = constraint[BB][1];
        std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> leftBranch = allInstrRangesMap;
        std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> rightBranch = allInstrRangesMap;
        for (auto &element : leftBranch) {
            bool leftEmptyBranch = false;
            for (auto &constraintElement : *element.first) {
                if (leftBranchConstr.find(constraintElement.first) != leftBranchConstr.end() && intersect(leftBranchConstr[constraintElement.first], constraintElement.second).hasNoRange())
                {
                    leftEmptyBranch = true;
                    break;
                }
            }
            if(leftEmptyBranch)
            {
                for(auto &variable_pair : element.second)
                {
                    variable_pair.second = interval(posThreshold, negThreshold);
                }
            }
        }
        for (auto &element : rightBranch) {
            bool rightEmptyBranch = false;
            for (auto &constraintElement : *element.first)
            {
                if (rightBranchConstr.find(constraintElement.first) != rightBranchConstr.end() &&
                    intersect(rightBranchConstr[constraintElement.first], constraintElement.second).hasNoRange())
                {
                    rightEmptyBranch = true;
                    break;
                }
            }
            if(rightEmptyBranch)
            {
                for(auto &variable_pair : element.second)
                {
                    variable_pair.second = interval(posThreshold, negThreshold);
                }
            }
        }
        updatedBlockIntervalMap[leftBlock] = leftBranch;
        auto *rightBlock = dyn_cast<BasicBlock>(dyn_cast<BranchInst>(&I)->getSuccessor(1));
        updatedBlockIntervalMap[rightBlock] = rightBranch;
    } else
    {
        updatedBlockIntervalMap[leftBlock] = allInstrRangesMap;
    }
}

bool updateIntervalChecks(std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &constIntervalMap, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &analysisMap)
{
    bool isDifferent = false;
    for (auto &givenInterval : constIntervalMap) {
        std::map<Instruction *, interval> rangesMap = givenInterval.second;
        std::map<Instruction *, interval> intervalAnalysisMap = analysisMap[givenInterval.first];
        for (auto &element : rangesMap)
        {
            if (intervalAnalysisMap.find(element.first) == intervalAnalysisMap.end()) {
                analysisMap[givenInterval.first][element.first] = element.second;
                isDifferent = true;
            }
            else if (intervalAnalysisMap[element.first].hasNoRange())
            {
                if (!element.second.hasNoRange())
                {
                    analysisMap[givenInterval.first][element.first] = element.second;
                    isDifferent = true;
                }
            } else {
                bool hasInnerSet;
                if (element.second.getLowBound() == posThreshold && element.second.getHighBound() == negThreshold) {
                    hasInnerSet = true;
                }
                else if (intervalAnalysisMap[element.first].getLowBound() == posThreshold && intervalAnalysisMap[element.first].getHighBound() == negThreshold) {
                    hasInnerSet = false;
                }
                else hasInnerSet = element.second.getLowBound() >= intervalAnalysisMap[element.first].getLowBound() && element.second.getHighBound() <= intervalAnalysisMap[element.first].getHighBound();
                if (!hasInnerSet) {
                    analysisMap[givenInterval.first][element.first].setLowBound(std::min(element.second.getLowBound(), intervalAnalysisMap[element.first].getLowBound()));
                    analysisMap[givenInterval.first][element.first].setHighBound(std::max(element.second.getHighBound(), intervalAnalysisMap[element.first].getHighBound()));
                    isDifferent = true;
                }

            }
        }
    }
    return isDifferent;
}

bool checkBasicBlockRange(BasicBlock *BB, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> &constIntervalMap, std::map<std::string, Instruction *> &varValuesMap, std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &intervalAnalysisMap, std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> &updatedMap){
    for (auto &I: *BB){
        switch (I.getOpcode()) {
            case Instruction::Add:
            {
                rangeMathOper(BB, I, constIntervalMap, varValuesMap, "add");
                break;
            }
            case Instruction::Sub:
            {
                rangeMathOper(BB, I, constIntervalMap, varValuesMap, "sub");
                break;
            }
            case Instruction::Mul:
            {
                rangeMathOper(BB, I, constIntervalMap, varValuesMap, "mul");
                break;
            }
            case Instruction::SRem:
            {
                rangeMathOper(BB, I, constIntervalMap, varValuesMap, "srem");
                break;
            }
            case Instruction::Br:
            {
                processBranchOperation(BB, I, constIntervalMap, varValuesMap, updatedMap);
                return updateIntervalChecks(constIntervalMap, intervalAnalysisMap[BB]);
            }
            case Instruction::Alloca:
            {
                if (constIntervalMap.begin()->first->find(&I) != constIntervalMap.begin()->first->end()) {
                    for (auto &element :constIntervalMap)
                        element.second = constraintUpdate(BB, constIntervalMap);
                }
                else {
                    for (auto &element : constIntervalMap)
                        element.second[&I] = interval(negThreshold, posThreshold);
                }
                for (auto &element : constIntervalMap)
                {
                    bool hasNone = false;
                    for (auto &constraint : *element.first)
                    {
                        element.second[constraint.first] = intersect(constraint.second, element.second[constraint.first]);
                    }
                    for (auto &instructionInterval : element.second)
                    {
                        if (instructionInterval.second.hasNoRange())
                        {
                            hasNone = true;
                            break;
                        }
                    }
                    if (hasNone)
                    {
                        for (auto &instructionInterval : element.second)
                        {
                            instructionInterval.second = interval(posThreshold, negThreshold);
                        }
                    }
                }
                break;
            }
            case Instruction::Load:
            {
                processLoadOperation(BB, I, constIntervalMap, varValuesMap);
                break;
            }
            case Instruction::Store:
            {
                processStoreOperation(BB, I, constIntervalMap, varValuesMap);
                break;
            }
            case Instruction::Ret:
            {
                return updateIntervalChecks(constIntervalMap, intervalAnalysisMap[BB]);
            }
            default:
            {
                break;
            }
        }
    }
    return false;
}

std::string getSimpleLabel(Instruction &I) {
    std::string instructionLabel;
    llvm::raw_string_ostream rso(instructionLabel);
    I.print(rso);
    return instructionLabel;
}

int main(int argc, char **argv){
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
    std::map<std::string, Instruction *> varValuesMap;
    std::stack<std::pair<BasicBlock *, std::map<Instruction *, interval>>> traversalStack;
    std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> intervalAnalysisMap;
    std::vector<std::map<Instruction *, interval>> mainConstraintMap;
    std::stack<std::pair<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>>> intervalTraversalStack;
    std::map<Instruction *, interval> emptySet;
    traversalStack.push(std::make_pair(entryBB, emptySet));

    while (!traversalStack.empty()) {
        std::map<BasicBlock *, std::map<Instruction *, interval>> updatedMap;
        auto top = traversalStack.top();
        traversalStack.pop();

        auto isDifferent = analyseBB(top.first, top.second, varValuesMap, analysisMap, updatedMap);
        if (isDifferent) {
            for (auto &p : updatedMap) {
                traversalStack.push(p);
            }
        }
    }

    // generate constraints of the program
    for (auto &instrMap : analysisMap) {
        for (auto &rangesMap : instrMap.second) {
            rangesMap.second = interval(negThreshold, posThreshold);
        }

        BasicBlock *BB = instrMap.first;
        std::map<Instruction *, interval> rangesMap = instrMap.second;
        std::map<BasicBlock *, std::map<Instruction *, interval>> result;

        for (auto &I: *BB) {
            if (I.getOpcode() == Instruction::Br)
            {
                isBranchOper(BB, I, rangesMap, varValuesMap, result);
                if (result.size() > 1)
                {
                    for (auto &attributesMap : result)
                    {
                        constraint[BB].push_back(attributesMap.second);
                    }
                    for (auto it = constraint[BB][0].begin(); it != constraint[BB][0].end();)
                    {
                        bool erase = false;
                        for (auto innerIt = constraint[BB][1].begin(); innerIt != constraint[BB][1].end(); innerIt++)
                        {
                            if (it->second.toString() == innerIt->second.toString())
                            {
                                it = constraint[BB][0].erase(it);
                                innerIt = constraint[BB][1].erase(innerIt);
                                erase = true;
                                break;
                            }
                        }
                        if (!erase) it++;
                    }
                    for(auto it = constraint[BB][0].begin(); it != constraint[BB][0].end();)
                    {
                        if(it->first->getName().size() == 0)
                        {
                            it = constraint[BB][0].erase(it);
                        }
                        else
                        {
                            it++;
                        }
                    }
                    for(auto it = constraint[BB][1].begin(); it != constraint[BB][1].end();)
                    {
                        if(it->first->getName().size() == 0)
                        {
                            it = constraint[BB][1].erase(it);
                        }
                        else
                        {
                            it++;
                        }
                    }
                }
            }
        }
    }

    for (auto attributesMap : constraint)
    {
        if (attributesMap.second.size() != 0 && attributesMap.second[0].size() != 0)
        {
            if (mainConstraintMap.size() == 0)
            {
                mainConstraintMap = attributesMap.second;
            }
            else
            {
                std::vector<std::map<Instruction *, interval>> backup = mainConstraintMap;
                mainConstraintMap.clear();

                for (auto constraintVector : attributesMap.second)
                {
                    for (auto temporaryMap : backup) {
                        for (auto it = constraintVector.begin(); it != constraintVector.end(); it++)
                        {
                            if (temporaryMap.find(it->first) != temporaryMap.end())
                            {
                                temporaryMap.insert(std::make_pair(it->first, intersect(temporaryMap.find(it->first)->second, it->second)));
                            }
                            else
                            {
                                temporaryMap.insert(*it);
                            }
                        }
                        mainConstraintMap.push_back(temporaryMap);
                    }
                }
            }
        }
    }

    std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>> emptyMap;
    for (auto &instructionInterval : mainConstraintMap) {
        emptyMap.insert(std::make_pair(&instructionInterval, instructionInterval));
    }
    intervalTraversalStack.push(std::make_pair(entryBB, emptyMap));

    while (!intervalTraversalStack.empty())
    {
        std::map<BasicBlock *, std::map<std::map<Instruction *, interval> *, std::map<Instruction *, interval>>> updatedMap;
        auto pair = intervalTraversalStack.top();
        intervalTraversalStack.pop();

        auto isDifferent = checkBasicBlockRange(pair.first, pair.second, varValuesMap, intervalAnalysisMap, updatedMap);

        if (isDifferent) {
            for (auto &p : updatedMap) {
                intervalTraversalStack.push(p);
            }
        }
    }

    for (auto &givenInterval : intervalAnalysisMap) {
        givenInterval.first->printAsOperand(errs(), false);
        errs() << "\n";
        std::map<Instruction *, interval> result = constraintUpdate(givenInterval.first, givenInterval.second);

        bool hasNone = false;
        for (auto &element : result) {
            if (element.second.hasNoRange())
                hasNone = true;
        }
        if (!hasNone) {
            for (auto &element : result) {
                if(element.first->getName().size()!=0)
                    std::cout << getSimpleLabel(*element.first) << "  ----> interval range:   " << element.second.toString()
                          << std::endl;
            }
        }
    }
}
