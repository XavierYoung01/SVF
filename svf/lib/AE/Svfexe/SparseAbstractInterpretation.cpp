//===- SparseAbstractInterpretation.cpp -- Sparse Abstract Execution----//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===---------------------------------------------------------------------===//

#include "AE/Svfexe/SparseAbstractInterpretation.h"

#include "Graphs/SVFG.h"
#include "Graphs/SparseObjGraph.h"
#include "MSSA/SVFGBuilder.h"
#include "Graphs/PAG.h"
#include "Util/Options.h"

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <optional>
#include <set>

namespace SVF
{

SemiSparseAbstractInterpretation::SemiSparseAbstractInterpretation()
{
    preAnalysis->initCycleValVars();
}

const ICFGNode* SemiSparseAbstractInterpretation::getICFGNode(const ValVar* var) const
{
    if (!var->getICFGNode())
        return icfg->getGlobalICFGNode();
    if (SVFUtil::isa<CallICFGNode>(var->getICFGNode()) && SVFUtil::isa<RetValPN>(var))
        return SVFUtil::cast<CallICFGNode>(var->getICFGNode())->getRetICFGNode();
    return var->getICFGNode();
}

SVF::Interval SemiSparseAbstractInterpretation::getInterval(const ValVar* var, const ICFGNode*)
{
    return Base::getInterval(var, getICFGNode(var));
}

SVF::Interval SemiSparseAbstractInterpretation::getDefinedInterval(const ValVar* var, const ICFGNode*)
{
    return Base::getDefinedInterval(var, getICFGNode(var));
}

SVF::AddressSet SemiSparseAbstractInterpretation::getAddressSet(const ValVar* var, const ICFGNode*)
{
    return Base::getAddressSet(var, getICFGNode(var));
}

bool SemiSparseAbstractInterpretation::hasAbsValue(const ValVar* var, const ICFGNode*) const
{
    return Base::hasAbsValue(var, getICFGNode(var));
}

bool SemiSparseAbstractInterpretation::numericalValueMayBeUninitialized(const ValVar* var, const ICFGNode*) const
{
    return Base::numericalValueMayBeUninitialized(var, getICFGNode(var));
}

void SemiSparseAbstractInterpretation::updateValue(const ValVar* var,
        const SVF::Interval& interval, const SVF::AddressSet& addresses, const ICFGNode* node)
{
    Base::updateValue(var, interval, addresses, var->getICFGNode() ? var->getICFGNode() : node);
}

void SemiSparseAbstractInterpretation::addUninitializedNumericalAlternative(const ValVar* var, const ICFGNode* node)
{
    Base::addUninitializedNumericalAlternative(var, var->getICFGNode() ? var->getICFGNode() : node);
}

void SemiSparseAbstractInterpretation::forgetScalarValues(State& state) const
{
    const SVF::Variable end = adapter_.firstObjectContentVariable();
    for (SVF::Variable variable : state.initializedVariablesBefore(end))
        state.resetValue(variable);
    for (SVF::Variable variable : state.numerical().supportVariablesBefore(end))
        state.numerical().forget(variable);
    for (SVF::Variable variable : state.addresses().nonDefaultVariablesBefore(end))
        state.addresses().forget(variable);
}

SemiSparseAbstractInterpretation::State
SemiSparseAbstractInterpretation::propagatedState(const State& source) const
{
    State result = source;
    forgetScalarValues(result);
    return result;
}

void SemiSparseAbstractInterpretation::updateFlowState(const ICFGNode* node, State incoming)
{
    // SSA values remain at their definition sites when memory is replaced.
    const auto old = abstractTrace_.find(node);
    if (old != abstractTrace_.end())
    {
        const SVF::Variable end = adapter_.firstObjectContentVariable();
        std::set<SVF::Variable> scalars;
        for (SVF::Variable var : old->second.initializedVariablesBefore(end)) scalars.insert(var);
        for (SVF::Variable var : old->second.numerical().supportVariablesBefore(end)) scalars.insert(var);
        for (SVF::Variable var : old->second.addresses().nonDefaultVariablesBefore(end)) scalars.insert(var);
        for (SVF::Variable var : scalars)
            incoming.assignValueFrom(var, old->second, var);
    }
    abstractTrace_.insert_or_assign(node, std::move(incoming));
}

void SemiSparseAbstractInterpretation::copyAbstractState(const ICFGNode* source, const ICFGNode* destination)
{
    State incoming = state(source);
    forgetScalarValues(incoming);
    updateFlowState(destination, std::move(incoming));
}

bool SemiSparseAbstractInterpretation::mergeStatesFromPredecessors(const ICFGNode* node)
{
    State merged = bottomState();
    bool hasFeasiblePredecessor = false;
    for (const ICFGEdge* edge : node->getInEdges())
    {
        const ICFGNode* predecessor = edge->getSrcNode();
        if (!hasAbsState(predecessor)) continue;
        const auto* branch = SVFUtil::dyn_cast<IntraCFGEdge>(edge);
        if (!branch && !SVFUtil::isa<CallCFGEdge>(edge) && !SVFUtil::isa<RetCFGEdge>(edge)) continue;
        if (SVFUtil::isa<RetCFGEdge>(edge) && Options::HandleRecur() != TOP &&
                !hasAbsState(SVFUtil::cast<RetICFGNode>(node)->getCallICFGNode())) continue;
        State incoming = state(predecessor);
        if (branch && branch->getCondition())
        {
            if (!isBranchEdgeFeasibleAt(branch, predecessor)) continue;
            collectBranchRefinement(branch, incoming);
        }
        merged.joinWith(propagatedState(incoming));
        hasFeasiblePredecessor = true;
    }
    if (hasFeasiblePredecessor)
        updateFlowState(node, std::move(merged));
    return hasFeasiblePredecessor;
}

void SemiSparseAbstractInterpretation::collectComponentScalarInputs(
    const ICFGNode* node, State& input)
{
    const auto copyValue = [&](const SVFVar* operand)
    {
        const auto* var = SVFUtil::dyn_cast<ValVar>(operand);
        if (var && adapter_.contains(*var) && getICFGNode(var) != node &&
                hasAbsValue(var, node))
        {
            const Variable key = adapter_.variable(*var);
            input.assignValueFrom(key, state(getICFGNode(var)), key);
        }
    };
    for (const SVFStmt* statement : node->getSVFStmts())
    {
        if (const auto* branch = SVFUtil::dyn_cast<BranchStmt>(statement))
            copyValue(branch->getCondition());
        else if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(statement))
            for (u32_t index = 0; index < multi->getOpVarNum(); ++index)
                copyValue(multi->getOpVar(index));
        else
            copyValue(statement->getSrcNode());

        if (const auto* gep = SVFUtil::dyn_cast<GepStmt>(statement))
            for (const auto& offset : gep->getOffsetVarAndGepTypePairVec())
                copyValue(offset.first);
    }
}

std::unique_ptr<SVF::AbstractDomain>
SemiSparseAbstractInterpretation::cloneCycleHeadState(const ICFGCycleWTO* cycle)
{
    State snapshot = state(cycle->head()->getICFGNode());
    forgetScalarValues(snapshot);
    for (const ValVar* var : preAnalysis->getCycleValVars(cycle))
    {
        const ICFGNode* defSite = var->getICFGNode();
        if (!defSite || !hasAbsValue(var, defSite) || !adapter_.contains(*var)) continue;
        assignValue(snapshot, adapter_.variable(*var), getInterval(var, defSite), getAddressSet(var, defSite));
    }
    return std::make_unique<State>(std::move(snapshot));
}

void SemiSparseAbstractInterpretation::scatterCycleValues(const State& snapshot, const ICFGNode* node)
{
    for (SVF::Variable variable : snapshot.initializedVariablesBefore(adapter_.firstObjectContentVariable()))
        if (const ValVar* var = adapter_.value(variable))
            updateValue(var, snapshot.interval(variable), snapshot.addressSet(variable), node);
}

bool SemiSparseAbstractInterpretation::widenCycleState(const SVF::AbstractDomain& previous,
        const SVF::AbstractDomain& current, const ICFGCycleWTO* cycle)
{
    const bool fixpoint = Base::widenCycleState(previous, current, cycle);
    const ICFGNode* head = cycle->head()->getICFGNode();
    const State snapshot = state(head);
    scatterCycleValues(snapshot, head);
    return fixpoint;
}

bool SemiSparseAbstractInterpretation::narrowCycleState(const SVF::AbstractDomain& previous,
        const SVF::AbstractDomain& current, const ICFGCycleWTO* cycle)
{
    const bool fixpoint = Base::narrowCycleState(previous, current, cycle);
    if (!fixpoint)
    {
        const ICFGNode* head = cycle->head()->getICFGNode();
        const State snapshot = state(head);
        scatterCycleValues(snapshot, head);
    }
    return fixpoint;
}

FullSparseAbstractInterpretation::FullSparseAbstractInterpretation()
{
    SVFGBuilder builder(true);
    builder.buildFullSVFG(preAnalysis->getPointerAnalysis());
    objRoutes_ = std::make_unique<SparseObjGraph>(
        *builder.getSVFG(), *icfg, *preAnalysis->getPointerAnalysis(),
        *svfir);
}

FullSparseAbstractInterpretation::~FullSparseAbstractInterpretation() = default;

FullSparseAbstractInterpretation::State FullSparseAbstractInterpretation::
    propagatedState(const State& source) const
{
    if (source.isBottom())
        return bottomState();
    State result = topState();
    result.lifetimes() = source.lifetimes();
    return result;
}

void FullSparseAbstractInterpretation::storeValue(const ValVar* pointer,
                                                  const Interval& interval,
                                                  const AddressSet& addresses,
                                                  const ICFGNode* node)
{
    const AddressSet targets = Base::getAddressSet(pointer, node);
    Base::storeValue(pointer, interval, addresses, node);
    auto record = [&](Location location) {
        const ObjVar* object = objectAt(location);
        if (object && memoryVariable(*object, state(node)) ==
                          adapter_.contentVariable(*object))
            memoryDefinitionSupport_[node].insert(
                adapter_.contentVariable(*object));
    };
    if (targets.hasUnknownObject())
        for (const auto& [location, variable] : adapter_.memoryLayout().cells())
        {
            (void)variable;
            record(location);
        }
    else
        for (Location location : targets)
            record(location);
}

std::optional<FullSparseAbstractInterpretation::ComponentInput>
FullSparseAbstractInterpretation::probeComponentInput(const ICFGNode* node)
{
    const auto oldSupport = memoryDefinitionSupport_.find(node);
    std::optional<std::set<Variable>> support;
    if (oldSupport != memoryDefinitionSupport_.end())
        support = oldSupport->second;
    auto input = Base::probeComponentInput(node);
    const auto current = memoryDefinitionSupport_.find(node);
    if (input && current != memoryDefinitionSupport_.end())
        input->memorySupport = std::move(current->second);
    if (support)
        memoryDefinitionSupport_.insert_or_assign(node, std::move(*support));
    else
        memoryDefinitionSupport_.erase(node);
    return input;
}

bool FullSparseAbstractInterpretation::mergeStatesFromPredecessors(
    const ICFGNode* node)
{
    std::optional<State> previous;
    std::set<Variable> previousSupport;
    const auto& edges = objRoutes_->getInputs(node);
    for (const auto* edge : edges)
        if (edge->getSrcNode()->getICFGNode() == node && hasAbsState(node))
        {
            previous = state(node);
            previousSupport = std::move(memoryDefinitionSupport_[node]);
            break;
        }
    memoryDefinitionSupport_.erase(node);
    if (!Base::mergeStatesFromPredecessors(node))
        return false;
    State& merged = ensureState(node);
    NodeBS pulled;
    for (const auto* edge : edges)
    {
        const auto* sourceNode = edge->getSrcNode();
        const ICFGNode* source = sourceNode->getICFGNode();
        const State* input =
            source == node ? (previous ? &*previous : nullptr)
                           : (hasAbsState(source) ? &state(source) : nullptr);
        if (!input)
            continue;
        std::optional<State> refined;
        const State* values = input;
        if (sourceNode->branch)
        {
            if (!isBranchEdgeFeasibleAt(sourceNode->branch, source))
                continue;
            refined = *input;
            if (!collectBranchRefinement(sourceNode->branch, *refined))
                continue;
            values = &*refined;
        }
        const auto& support =
            source == node ? previousSupport : memoryDefinitionSupport_[source];
        for (NodeID base : edge->getBases())
        for (NodeID id : svfir->getAllFieldsObjVars(svfir->getBaseObject(base)))
        {
            const auto* object =
                SVFUtil::dyn_cast<ObjVar>(svfir->getSVFVar(id));
            if (!object)
                continue;
            const Variable content = adapter_.contentVariable(*object);
            if (!input->hasValue(content) && !support.count(content))
                continue;
            const Variable from = memoryVariable(*object, *values);
            const Variable to = memoryVariable(*object, merged);
            if (pulled.test(id))
                merged.joinValueFrom(to, *values, from);
            else
                merged.assignValueFrom(to, *values, from);
            pulled.set(id);
            memoryDefinitionSupport_[node].insert(content);
        }
    }
    return true;
}

} // namespace SVF
