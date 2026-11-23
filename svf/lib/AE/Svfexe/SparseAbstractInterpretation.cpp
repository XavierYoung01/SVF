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
#include "AE/Core/PackedRelationalDomain.h"
#include "Graphs/SparseObjGraph.h"

#include "Graphs/SVFG.h"
#include "MSSA/SVFGBuilder.h"
#include "SVFIR/SVFIR.h"
#include "Util/Options.h"
#include "Util/ExtAPI.h"

#include <algorithm>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <iterator>
#include <optional>
#include <set>

namespace SVF
{


namespace
{

std::vector<SVF::Variable> nonDefaultVariables(
    const SemiSparseAbstractInterpretation::State& state)
{
    // All domain support queries are already sorted and unique. Keep that
    // order without allocating a tree node for every initialized coordinate.
    const auto numbers = state.numerical().supportVariables();
    const auto pointers = state.addresses().nonDefaultVariables();
    std::vector<SVF::Variable> payloads;
    payloads.reserve(numbers.size() + pointers.size());
    std::set_union(numbers.begin(), numbers.end(), pointers.begin(), pointers.end(),
                   std::back_inserter(payloads));
    const auto initialized = state.initializedVariables();
    std::vector<SVF::Variable> variables;
    variables.reserve(payloads.size() + initialized.size());
    std::set_union(payloads.begin(), payloads.end(), initialized.begin(), initialized.end(),
                   std::back_inserter(variables));
    return variables;
}

std::set<SVF::Variable> definedScalarVariables(const ICFGNode* node,
        const SVFIRAdapter& adapter)
{
    std::set<SVF::Variable> result;
    const auto add = [&](const SVFVar* variable)
    {
        if (!variable)
            return;
        const auto* value = SVFUtil::dyn_cast<ValVar>(variable);
        if (value && adapter.contains(*value))
            result.insert(adapter.variable(*value));
    };
    for (const SVFStmt* statement : node->getSVFStmts())
    {
        if (const auto* address = SVFUtil::dyn_cast<AddrStmt>(statement))
            add(address->getLHSVar());
        else if (const auto* binary =
                     SVFUtil::dyn_cast<BinaryOPStmt>(statement))
            add(binary->getRes());
        else if (const auto* compare = SVFUtil::dyn_cast<CmpStmt>(statement))
            add(compare->getRes());
        else if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(statement))
            add(load->getLHSVar());
        else if (const auto* copy = SVFUtil::dyn_cast<CopyStmt>(statement))
            add(copy->getLHSVar());
        else if (const auto* gep = SVFUtil::dyn_cast<GepStmt>(statement))
            add(gep->getLHSVar());
        else if (const auto* select = SVFUtil::dyn_cast<SelectStmt>(statement))
            add(select->getRes());
        else if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(statement))
            add(phi->getRes());
        else if (const auto* call = SVFUtil::dyn_cast<CallPE>(statement))
            add(call->getRes());
        else if (const auto* ret = SVFUtil::dyn_cast<RetPE>(statement))
            add(ret->getLHSVar());
    }
    // External models bind the actual return directly in the call node's
    // post-state.  Internal calls expose their result at the RetICFGNode via
    // RetPE; importing that future definition at the call boundary would make
    // reconstruction circular.
    if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(node))
        if (call->getCalledFunction() &&
                SVFUtil::isExtCall(call->getCalledFunction()))
            add(call->getRetICFGNode()->getActualRet());
    if (const auto* returnSite = SVFUtil::dyn_cast<RetICFGNode>(node))
        add(returnSite->getActualRet());
    return result;
}

} // namespace

SemiSparseAbstractInterpretation::SemiSparseAbstractInterpretation()
{
    this->preAnalysis->initCycleValVars();
    initializeScalarAvailability();
}

void SemiSparseAbstractInterpretation::initializeScalarAvailability()
{
    scalarSymbols_.clear();
    scalarVariables_.clear();
    scalarAvailability_.clear();
    auto& symbols = scalarSymbols_;
    auto& variables = scalarVariables_;
    const auto symbol = [&](SVF::Variable variable)
    {
        const auto entry = symbols.emplace(variable, variables.size());
        if (entry.second)
            variables.push_back(variable);
        return entry.first->second;
    };
    const auto encode = [&](const std::set<SVF::Variable>& values)
    {
        NodeBS result;
        for (SVF::Variable variable : values)
            result.set(symbol(variable));
        return result;
    };
    Map<const ICFGNode*, NodeBS> available, definitions;
    std::vector<const ICFGNode*> nodes;
    for (auto iterator = this->icfg->begin(); iterator != this->icfg->end();
            ++iterator)
    {
        nodes.push_back(iterator->second);
        available.try_emplace(iterator->second);
        definitions.emplace(iterator->second, encode(
                                definedScalarVariables(iterator->second, this->adapter_)));
    }
    std::sort(nodes.begin(), nodes.end(),
              [](const ICFGNode* left, const ICFGNode* right)
    {
        return left->getId() < right->getId();
    });

    const ICFGNode* global = this->icfg->getGlobalICFGNode();
    NodeBS globalOut = definitions.at(global);
    // Use the same entry policy as execution, not all syntactic callers.
    // This is static reachability: no guard feasibility is assumed here.
    std::set<const ICFGNode*> reachable{global};
    std::set<const ICFGNode*> entryNodes;
    FIFOWorkList<const FunObjVar*> roots = this->collectProgEntryFuns();
    while (!roots.empty())
    {
        const FunEntryICFGNode* entry =
            this->icfg->getFunEntryICFGNode(roots.pop());
        reachable.insert(entry);
        entryNodes.insert(entry);
        for (const SVFVar* argument : entry->getFormalParms())
        {
            const auto* value = SVFUtil::dyn_cast<ValVar>(argument);
            if (value && this->adapter_.contains(*value))
                globalOut.set(symbol(this->adapter_.variable(*value)));
        }
    }
    available[global] = std::move(globalOut);

    bool reachChanged=true;
    while(reachChanged)
    {
        reachChanged=false;
        for(const ICFGNode* node:nodes)
        {
            if(!reachable.count(node)) continue;
            const auto* summaryCall = SVFUtil::dyn_cast<CallICFGNode>(node);
            if (summaryCall && summaryCall->getCalledFunction() &&
                    this->recursiveTopSummary(summaryCall))
                reachChanged |= reachable.insert(
                                    summaryCall->getRetICFGNode()).second;
            for(const ICFGEdge* edge:node->getOutEdges())
            {
                if(!SVFUtil::isa<IntraCFGEdge>(edge) &&
                        !SVFUtil::isa<CallCFGEdge>(edge) &&
                        !SVFUtil::isa<RetCFGEdge>(edge)) continue;
                // Reaching a shared callee through main does not execute an
                // unvisited caller's return site. Revisit on later discovery
                // of that call site; this fixed point is independent of IDs.
                if(const auto* ret=SVFUtil::dyn_cast<RetCFGEdge>(edge))
                    if(!reachable.count(ret->getCallSite())) continue;
                reachChanged|=reachable.insert(edge->getDstNode()).second;
            }
        }
    }
    for(const ICFGNode* node:nodes)
        if(!reachable.count(node)) available[node].clear();

    // Unvisited equations start at the universe, the identity for intersection.
    // Keep it implicit until a finite boundary reaches the node.
    std::set<const ICFGNode*> pending = reachable;
    pending.erase(global);
    Map<const ICFGNode*, std::vector<const ICFGNode*>> dependents;
    FIFOWorkList<const ICFGNode*> worklist;
    for (const ICFGNode* node : nodes)
    {
        if (node == global || !reachable.count(node))
            continue;
        worklist.push(node);
        for (const ICFGEdge* edge : node->getInEdges())
        {
            const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge);
            const ICFGNode* source = ret
                                     ? static_cast<const ICFGNode*>(ret->getCallSite())
                                     : edge->getSrcNode();
            dependents[source].push_back(node);
        }
        if (const auto* ret = SVFUtil::dyn_cast<RetICFGNode>(node))
            dependents[ret->getCallICFGNode()].push_back(node);
    }
    while (!worklist.empty())
    {
        const ICFGNode* node = worklist.pop();
        bool first = true;
        bool hasPendingInput = false;
        NodeBS incoming;
        const auto* returnSite = SVFUtil::dyn_cast<RetICFGNode>(node);
        const CallICFGNode* summaryCall = returnSite
                                          ? returnSite->getCallICFGNode() : nullptr;
        const bool summaryReturn = summaryCall &&
                                   summaryCall->getCalledFunction() &&
                                   this->recursiveTopSummary(summaryCall);
        // Execution also starts selected roots directly from the global
        // state (including no-main entry SCCs without an explicit edge).
        if (entryNodes.count(node))
        {
            incoming=available.at(global);
            first=false;
        }
        if (summaryReturn)
        {
            if (pending.count(summaryCall))
                hasPendingInput = true;
            else
            {
                incoming = available.at(summaryCall);
                first = false;
            }
        }
        for (const ICFGEdge* edge : node->getInEdges())
        {
            // TOP binds its own result; the unexecuted callee's formal
            // return ghost is not an input to the synthetic summary edge.
            if (summaryReturn)
                break;
            if (!SVFUtil::isa<IntraCFGEdge>(edge) &&
                    !SVFUtil::isa<CallCFGEdge>(edge) &&
                    !SVFUtil::isa<RetCFGEdge>(edge))
                continue;
            if (!reachable.count(edge->getSrcNode())) continue;
            if (const auto* ret=SVFUtil::dyn_cast<RetCFGEdge>(edge))
                if (!reachable.count(ret->getCallSite())) continue;
            const auto predecessor =
                available.find(edge->getSrcNode());
            if (predecessor == available.end())
                continue;
            const auto* returnEdge = SVFUtil::dyn_cast<RetCFGEdge>(edge);
            const ICFGNode* source = returnEdge
                                     ? static_cast<const ICFGNode*>(returnEdge->getCallSite())
                                     : edge->getSrcNode();
            if (pending.count(source))
            {
                hasPendingInput = true;
                continue;
            }
            NodeBS edgeAvailable =
                available.at(source);
            // Return transfer retains the callee's formal-return ghosts
            // needed to bind RetPE relations and restores only the caller
            // SSA frame. Other callee locals are out of scope here and
            // must not leak into the caller's global scalar carrier.
            if (returnEdge)
            {
                for (const SVFStmt* statement : node->getSVFStmts())
                {
                    const auto* binding =
                        SVFUtil::dyn_cast<RetPE>(statement);
                    const auto* formal = binding
                                         ? SVFUtil::dyn_cast<ValVar>(binding->getRHSVar())
                                         : nullptr;
                    if (formal && this->adapter_.contains(*formal))
                        edgeAvailable.set(
                            symbol(this->adapter_.variable(*formal)));
                }
            }
            if (first)
            {
                incoming = std::move(edgeAvailable);
                first = false;
            }
            else
            {
                incoming &= edgeAvailable;
            }
        }
        if (first && hasPendingInput)
            continue;
        incoming |= definitions.at(node);
        if (pending.erase(node) || incoming != available.at(node))
        {
            available[node] = std::move(incoming);
            for (const ICFGNode* dependent : dependents[node])
                worklist.push(dependent);
        }
    }
    assert(pending.empty() && "Reachable scalar availability has no finite boundary");
    scalarAvailability_ = std::move(available);
}

bool SemiSparseAbstractInterpretation::isScalarAvailable(
    const ICFGNode* node, SVF::Variable variable) const
{
    const auto state = scalarAvailability_.find(node);
    const auto symbol = scalarSymbols_.find(variable);
    return state != scalarAvailability_.end() &&
           symbol != scalarSymbols_.end() && state->second.test(symbol->second);
}

std::vector<SVF::Variable>
SemiSparseAbstractInterpretation::availableScalarVariables(
    const ICFGNode* node) const
{
    std::vector<SVF::Variable> variables;
    const auto state = scalarAvailability_.find(node);
    if (state != scalarAvailability_.end())
        for (NodeID symbol : state->second)
            variables.push_back(scalarVariables_.at(symbol));
    std::sort(variables.begin(), variables.end());
    return variables;
}

SemiSparseAbstractInterpretation::State
SemiSparseAbstractInterpretation::flowState(bool bottom) const
{
    return State(this->makeNumericalDomain(bottom),
                 this->adapter_.memoryLayout(), true);
}

SemiSparseAbstractInterpretation::State&
SemiSparseAbstractInterpretation::scalarState()
{
    if (!scalarState_)
        scalarState_.emplace(flowState());
    return *scalarState_;
}

const SemiSparseAbstractInterpretation::State*
SemiSparseAbstractInterpretation::findScalarState() const
{
    return scalarState_ ? &*scalarState_ : nullptr;
}

SemiSparseAbstractInterpretation::State&
SemiSparseAbstractInterpretation::scalarTransferState(const ICFGNode*)
{
    return scalarState();
}

SemiSparseAbstractInterpretation::State
SemiSparseAbstractInterpretation::phiAlternativeState(
    const ICFGNode* predecessor)
{
    State alternative = this->topState();
    if (predecessor)
    {
        std::vector<SVF::Variable> seeds;
        const auto available = scalarAvailability_.find(predecessor);
        if (available != scalarAvailability_.end())
            seeds = availableScalarVariables(predecessor);
        if (Options::AEDomain() == AENumericalDomain::Box)
        {
            for (SVF::Variable variable : seeds)
                alternative.assignValueFrom(variable, scalarState(), variable);
        }
        else
            materializeScalarDefinitions(alternative, seeds, predecessor);
        if (this->hasAbsState(predecessor))
            alternative.numerical().meetWith(
                           this->state(predecessor).numerical());
        // Semi-sparse branch predicates live in refinementTrace_ because
        // scalar SSA coordinates are removed from persistent ICFG states.
        // A phi alternative must include the predicate that selected its
        // predecessor; otherwise joining `x` from x<=y with `y` from x>y
        // loses the derived min/max relation and retains only unary hulls.
        const auto refinement = refinementTrace_.find(predecessor);
        // Replaying branch relations into every loop phi makes the same
        // octagonal closure participate in each widening iteration.  Cyclic
        // functions already reconstruct loop values through WTO
        // widen/scatter; keep this supplementary path-sensitive phi recovery
        // for acyclic SSA joins, where it is stable and directly useful.
        if (refinement != refinementTrace_.end() &&
                !this->preAnalysis->functionHasCycle(
                    predecessor->getFun()))
            applyScalarRefinement(alternative, refinement->second);
    }
    return alternative;
}

void SemiSparseAbstractInterpretation::assignRelationalValue(
    const ValVar* target, const SVF::LinearExpression& expression,
    const SVF::Interval& interval, const SVF::AddressSet& addresses,
    const ICFGNode* node)
{
    if (!target || !this->adapter_.contains(*target))
        return;
    const SVF::Variable variable = this->adapter_.variable(*target);
    State& scalars = scalarState();
    scalars.assignNumeric(variable, expression);
    scalars.setAddressSet(variable, addresses);
    if (Options::AEDomain() != AENumericalDomain::Box)
    {
        State summary = this->topState();
        std::vector<SVF::Variable> sources;
        for (const auto& [source, coefficient] : expression.terms())
        {
            (void)coefficient;
            sources.push_back(source);
        }
        materializeScalarDefinitions(summary, sources, node);
        summary.assignNumeric(variable, expression);
        // The interval was evaluated in the current invocation.  It is stable
        // for a root or single-call-site function, but not for a
        // context-insensitive callee shared by multiple call sites: a later
        // caller can enlarge the formal inputs after an earlier return edge
        // has already been processed.  Keep only the invocation-independent
        // affine equality in that case.  Reusing call-local unary bounds would
        // make the earlier return state fail the interprocedural Post equation.
        const bool sharedFunction =
            isSharedFunction(node ? node->getFun() : nullptr);
        const bool cyclicFunction =
            this->preAnalysis->functionHasCycle(node ? node->getFun()
                                                : nullptr);
        const SVF::Interval impliedInterval =
            summary.numerical().bound(variable);
        if (!sharedFunction && !cyclicFunction &&
                !impliedInterval.isSubsetOf(interval))
            this->constrainInterval(summary, variable, interval);
        summary.setAddressSet(variable, addresses);
        // Keep the independently proved unary result together with the affine
        // equality. Only join a saved value from an older visit to this
        // definition (for example, a loop iteration).
        const auto pending = pendingDefinitionHistory_.find(variable);
        if (pending != pendingDefinitionHistory_.end() &&
                pending->second.first == node)
        {
            summary.joinWith(pending->second.second);
            pendingDefinitionHistory_.erase(pending);
        }
        scalarDefinitions_.insert_or_assign(variable, std::move(summary));
        if (std::getenv("SVF_AE_TRACE_SCALAR_SUMMARY"))
            std::cerr << "AE scalar summary assign node=" << node->getId()
                      << " target=" << variable.id()
                      << " shared_function=" << sharedFunction
                      << " cyclic_function=" << cyclicFunction << " state="
                      << scalarDefinitions_.at(variable).numerical().toString()
                      << '\n';
    }
    for (const auto& [source, coefficient] : expression.terms())
    {
        (void)coefficient;
        recordRelationalDependency(variable, source);
    }
}

void SemiSparseAbstractInterpretation::recordRelationalDependency(
    SVF::Variable target, SVF::Variable source)
{
    if (target == source)
        return;
    const auto dependencies = scalarDependencies_.find(source);
    if (dependencies == scalarDependencies_.end() ||
            dependencies->second.empty())
        scalarDependencies_[target].insert(source);
    else
        scalarDependencies_[target].insert(dependencies->second.begin(),
                                           dependencies->second.end());
}

void SemiSparseAbstractInterpretation::recordRelationalTupleDependency(
    SVF::Variable target, SVF::Variable peer)
{
    if (target != peer)
        scalarDependencies_[target].insert(peer);
}

void SemiSparseAbstractInterpretation::recordRelationalSummary(
    SVF::Variable target, const State& sourceSummary, const ICFGNode* node)
{
    if (Options::AEDomain() == AENumericalDomain::Box)
        return;
    // Phi/select alternatives record syntactic dependencies before their
    // relational states are joined.  A join can eliminate some or all of
    // those relations, so stale branch-local sources must not remain an
    // availability prerequisite for the target's (possibly Top) definition.
    const std::vector<SVF::Variable> support =
        sourceSummary.numerical().supportVariables();
    if (std::find(support.begin(), support.end(), target) == support.end())
    {
        scalarDependencies_.erase(target);
    }
    else
    {
        auto dependencies = scalarDependencies_.find(target);
        if (dependencies != scalarDependencies_.end())
        {
            std::set<SVF::Variable> supported;
            for (SVF::Variable dependency : dependencies->second)
                if (std::find(support.begin(), support.end(), dependency) !=
                        support.end())
                    supported.insert(dependency);
            if (supported.empty())
                scalarDependencies_.erase(dependencies);
            else
                dependencies->second = std::move(supported);
        }
    }
    const std::vector<SVF::Variable> variables =
        carrierDependencyClosure({target});
    State summary = this->topState();
    for (SVF::Variable variable : variables)
        summary.assignValueFrom(variable, sourceSummary, variable);
    // The unary summary written by updateValue may own target product facets
    // that are absent from the relational source.  Restore only those missing
    // facets: copying the old numerical coordinate would reintroduce a stale
    // bound when a shared callee or loop revisits this SSA definition with a
    // wider input summary.
    const auto intervalSummary = scalarDefinitions_.find(target);
    if (intervalSummary != scalarDefinitions_.end())
    {
        summary.restoreMissingNumericalInitializationFrom(
            intervalSummary->second, target);
        summary.restoreMissingAddressFrom(intervalSummary->second, target);
    }
    State projected = sourceSummary;
    projected.numerical().project(variables);
    summary.numerical().meetWith(projected.numerical());
    const auto pending = pendingDefinitionHistory_.find(target);
    if (pending != pendingDefinitionHistory_.end() &&
            pending->second.first == node)
    {
        summary.joinWith(pending->second.second);
        pendingDefinitionHistory_.erase(pending);
    }
    scalarDefinitions_.insert_or_assign(target, std::move(summary));
    if (std::getenv("SVF_AE_TRACE_SCALAR_SUMMARY"))
        std::cerr << "AE scalar summary merge target=" << target.id()
                  << " dependencies=";
    if (std::getenv("SVF_AE_TRACE_SCALAR_SUMMARY"))
    {
        for (SVF::Variable variable : variables)
            std::cerr << variable.id() << ',';
        std::cerr << " state="
                  << scalarDefinitions_.at(target).numerical().toString()
                  << '\n';
    }
}

void SemiSparseAbstractInterpretation::recordMergedReturnSummary(
    const RetICFGNode* returnSite)
{
    if (!returnSite)
        return;
    const auto* target =
        SVFUtil::dyn_cast<ValVar>(returnSite->getActualRet());
    if (!target || !this->adapter_.contains(*target))
        return;
    const SVF::Variable targetVariable = this->adapter_.variable(*target);
    if (Options::AEDomain() == AENumericalDomain::Box)
    {
        // The edge merge computes the return value in the transient flow
        // state.  Publish its scalar facet before finalizeAbstractState drops
        // active ValVars from that state.
        scalarState().assignValueFrom(
            targetVariable, this->state(returnSite), targetVariable);
        return;
    }
    for (const ICFGEdge* edge : returnSite->getInEdges())
    {
        const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge);
        const auto* binding = ret ? ret->getRetPE() : nullptr;
        const auto* source = binding
                             ? SVFUtil::dyn_cast<ValVar>(binding->getRHSVar())
                             : nullptr;
        if (source && this->adapter_.contains(*source))
            recordRelationalDependency(
                targetVariable, this->adapter_.variable(*source));
    }
    recordRelationalSummary(targetVariable, this->state(returnSite),
                            returnSite);
}

void SemiSparseAbstractInterpretation::assignRelationalStore(
    const ValVar* source, SVF::Variable content, const ICFGNode* node)
{
    if (!source || !this->adapter_.contains(*source))
        return;
    State& local = this->ensureState(node);
    const SVF::Variable sourceVariable = this->adapter_.variable(*source);
    materializeRelations(local, {sourceVariable}, node);
    if (!scalarState().numericalMayBeUninitialized(sourceVariable))
        local.numerical().assign(content,
                                 SVF::LinearExpression(sourceVariable));
}

void SemiSparseAbstractInterpretation::assignRelationalLoad(
    const ValVar* target, SVF::Variable content, const ICFGNode* node)
{
    if (!target || !this->adapter_.contains(*target))
        return;
    State& local = this->ensureState(node);
    if (local.numericalMayBeUninitialized(content))
        return;
    const SVF::Variable targetVariable = this->adapter_.variable(*target);
    local.numerical().assign(targetVariable,
                             SVF::LinearExpression(content));

    publishRelationalLoad(target, node);
}

void SemiSparseAbstractInterpretation::publishRelationalLoad(
    const ValVar* target, const ICFGNode* node)
{
    State& local = this->ensureState(node);
    const SVF::Variable targetVariable = this->adapter_.variable(*target);
    State projection = local;
    for (SVF::Variable variable : projection.numerical().supportVariables())
        if (this->adapter_.contentObject(variable))
            projection.numerical().forget(variable);
    scalarState().numerical().meetWith(projection.numerical());
    for (SVF::Variable variable : projection.numerical().supportVariables())
    {
        if (variable != targetVariable &&
                !this->adapter_.contentObject(variable))
            recordRelationalDependency(targetVariable, variable);
    }
    recordRelationalSummary(targetVariable, projection, node);
}

const SVF::AbstractDomain* SemiSparseAbstractInterpretation::
getScalarAbstractState() const
{
    return findScalarState();
}

std::unique_ptr<SVF::AbstractDomain>
SemiSparseAbstractInterpretation::cloneScalarSummary() const
{
    if (Options::AEDomain() != AENumericalDomain::Box || !scalarState_)
        return nullptr;
    State snapshot = *scalarState_;
    for (const auto& [variable, summary] : scalarDefinitions_)
        snapshot.assignValueFrom(variable, summary, variable);
    return std::make_unique<State>(std::move(snapshot));
}

void SemiSparseAbstractInterpretation::handleGlobalNode()
{
    Base::handleGlobalNode();
    finalizeAbstractState(this->icfg->getGlobalICFGNode());
}

SVF::Interval SemiSparseAbstractInterpretation::getInterval(
    const ValVar* value, const ICFGNode* node)
{
    if (this->recheckStates_)
        return Base::getInterval(value, node);
    const SVF::Interval result = getDefinedInterval(value, node);
    if (Options::AEDomain() == AENumericalDomain::Box ||
            !value || !this->adapter_.contains(*value))
        return result;
    State materialized = this->topState();
    const SVF::Variable variable = this->adapter_.variable(*value);
    const auto definition = scalarDefinitions_.find(variable);
    if (definition != scalarDefinitions_.end())
        materialized.assignValueFrom(variable, definition->second, variable);
    else
        materialized.assignValueFrom(variable, scalarState(), variable);
    if (materialized.numericalMayBeUninitialized(variable))
    {
        if (std::getenv("SVF_AE_TRACE_UNINITIALIZED_READ"))
            std::cerr << "AE uninitialized scalar read node="
                      << (node ? node->getId() : 0)
                      << " variable=" << variable.id()
                      << " svfir=" << value->getId()
                      << " payload=" << result.toString() << '\n';
        return SVF::Interval::top();
    }
    return result;
}

SVF::Interval SemiSparseAbstractInterpretation::getDefinedInterval(
    const ValVar* value, const ICFGNode* node)
{
    if (this->recheckStates_)
        return Base::getDefinedInterval(value, node);
    if (const auto* integer = SVFUtil::dyn_cast<ConstIntValVar>(value))
        return SVF::Interval::singleton(SVF::Rational(integer->getSExtValue()));
    if (const auto* floating = SVFUtil::dyn_cast<ConstFPValVar>(value))
        return SVFIRAdapter::floatingConstant(floating->getFPValue());
    if (!value)
        return SVF::Interval::top();
    if (value->getId() == this->svfir->getBlkPtr() ||
            SVFUtil::isa<BlackHoleValVar>(value))
        return Base::getDefinedInterval(value, node);
    if (!this->adapter_.contains(*value))
        return SVF::Interval::top();

    // Synthetic copy helpers have no def-site. Original's sparse reader
    // resolves them at the global node, where their numerical value is Top,
    // rather than reading the value written at the generated load's node.
    // Keep this policy for subsequent generated stores as well as queries.
    if (SVFUtil::isa<DummyValVar>(value) && !value->getICFGNode())
        return SVF::Interval::top();

    const SVF::Variable variable = this->adapter_.variable(*value);
    const auto available = scalarAvailability_.find(node);
    if (node && (available == scalarAvailability_.end() ||
                 !isScalarAvailable(node, variable)))
        return value->isPointer() ? SVF::Interval::bottom()
               : SVF::Interval::top();
    // A forward reference in a global initializer has not executed its
    // AddrStmt yet. Match the unresolved-symbol policy of the dense reader.
    if ((SVFUtil::isa<FunValVar>(value) || SVFUtil::isa<GlobalValVar>(value)) &&
            !scalarState().hasValue(variable))
        return SVF::Interval::top();
    SVF::Interval result;
    const auto definition = scalarDefinitions_.find(variable);
    if (definition != scalarDefinitions_.end())
        result = definition->second.interval(variable);
    else
        result = scalarState().interval(variable);
    // Conditional-edge refinement is intentionally local to the ICFG state.
    // Read it in addition to the module-wide scalar carrier so transfer
    // functions observe path constraints without copying all SSA values into
    // every program point.
    if (node && this->hasAbsState(node))
    {
        const State& local = this->state(node);
        const SVF::Interval refined = local.numerical().bound(variable);
        if (!refined.isTop())
        {
            if (result.isBottom())
                result = refined;
            else
                result.meetWith(refined);
        }
    }
    if (Options::AEDomain() != AENumericalDomain::Box && node)
    {
        const auto refinement = refinementTrace_.find(node);
        if (refinement != refinementTrace_.end())
        {
            const SVF::Interval refined =
                refinement->second.numerical().bound(variable);
            if (!refined.isTop())
            {
                if (result.isBottom())
                    result = refined;
                else
                    result.meetWith(refined);
            }
        }
    }
    return result;
}

SVF::AddressSet SemiSparseAbstractInterpretation::getAddressSet(
    const ValVar* value, const ICFGNode* node)
{
    if (this->recheckStates_)
        return Base::getAddressSet(value, node);
    (void)node;
    if (!value)
        return SVF::AddressSet::top();
    if (value->getId() == IRGraph::NullPtr ||
            SVFUtil::isa<ConstNullPtrValVar>(value))
        return SVF::AddressSet::singleton(SVF::Location::null());
    if (value->getId() == this->svfir->getBlkPtr() ||
            SVFUtil::isa<BlackHoleValVar>(value))
        return this->blackHoleAddressSet();
    if (SVFUtil::isa<DummyValVar>(value) && !value->getICFGNode())
        return SVF::AddressSet::bottom();
    if (!this->adapter_.contains(*value))
        return SVF::AddressSet::bottom();
    const SVF::Variable variable = this->adapter_.variable(*value);
    const auto available = scalarAvailability_.find(node);
    if (node && (available == scalarAvailability_.end() ||
                 !isScalarAvailable(node, variable)))
        return value->isPointer() ? SVF::AddressSet::top()
               : SVF::AddressSet::bottom();
    const auto definition = scalarDefinitions_.find(variable);
    return definition != scalarDefinitions_.end()
           ? definition->second.addressSet(variable)
           : scalarState().addressSet(variable);
}

bool SemiSparseAbstractInterpretation::hasAbsValue(
    const ValVar* value, const ICFGNode* node) const
{
    if (this->recheckStates_)
        return Base::hasAbsValue(value, node);
    (void)node;
    if (SVFUtil::isa<ConstIntValVar>(value) ||
            SVFUtil::isa<ConstFPValVar>(value))
        return true;
    return value && this->adapter_.contains(*value);
}

bool SemiSparseAbstractInterpretation::numericalValueMayBeUninitialized(
    const ValVar* value, const ICFGNode* node) const
{
    if (this->recheckStates_)
        return Base::numericalValueMayBeUninitialized(value, node);
    if (!value || !this->adapter_.contains(*value))
        return true;
    const SVF::Variable variable = this->adapter_.variable(*value);
    const auto definition = scalarDefinitions_.find(variable);
    if (definition != scalarDefinitions_.end())
        return definition->second.numericalMayBeUninitialized(variable);
    return !scalarState_ ||
           scalarState_->numericalMayBeUninitialized(variable);
}

void SemiSparseAbstractInterpretation::updateValue(
    const ValVar* value, const SVF::Interval& interval,
    const SVF::AddressSet& addresses, const ICFGNode* node)
{
    if (value && this->adapter_.contains(*value))
    {
        const SVF::Variable variable = this->adapter_.variable(*value);
        this->assignValue(scalarState(), variable, interval, addresses);
        State summary = this->topState();
        this->assignValue(summary, variable, interval, addresses);
        if (Options::AEDomain() == AENumericalDomain::Box)
        {
            const auto previous = scalarDefinitions_.find(variable);
            if (previous != scalarDefinitions_.end())
                summary.joinWith(previous->second);
        }
        else
        {
            const auto previous = scalarDefinitions_.find(variable);
            if (previous != scalarDefinitions_.end())
                pendingDefinitionHistory_.insert_or_assign(
                    variable, std::make_pair(node, previous->second));
            else
                pendingDefinitionHistory_.erase(variable);
        }
        scalarDefinitions_.insert_or_assign(variable, std::move(summary));
    }
}

void SemiSparseAbstractInterpretation::addUninitializedNumericalAlternative(
    const ValVar* value, const ICFGNode* node)
{
    (void)node;
    if (value && this->adapter_.contains(*value))
    {
        const SVF::Variable variable = this->adapter_.variable(*value);
        scalarState().addUninitializedNumericalAlternative(variable);
        const auto summary = scalarDefinitions_.find(variable);
        if (summary != scalarDefinitions_.end())
            summary->second.addUninitializedNumericalAlternative(variable);
    }
}

void SemiSparseAbstractInterpretation::copyAbstractState(
    const ICFGNode* source, const ICFGNode* destination)
{
    if (source == this->icfg->getGlobalICFGNode())
    {
        // Root parameters are initialized on the global state after
        // handleGlobalNode().  Snapshot here, immediately before the root
        // entry copy, so Post reconstruction sees both global initializers
        // and the configured entry arguments, but no later carrier updates.
        globalScalarSnapshot_ = scalarState();
    }
    this->abstractTrace_.insert_or_assign(destination, this->state(source));
}

void SemiSparseAbstractInterpretation::resetAbstractState(
    const ICFGNode* node)
{
    this->abstractTrace_.insert_or_assign(node, flowState());
}

void SemiSparseAbstractInterpretation::finalizeAbstractState(
    const ICFGNode* node)
{
    State& denseState = this->ensureState(node);
    forgetActiveScalarValues(denseState);
}

SemiSparseAbstractInterpretation::State SemiSparseAbstractInterpretation::
reconstructPostState(const ICFGNode* node,
                     const std::set<SVF::Variable>& availableScalars)
{
    const std::set<SVF::Variable>& pointScalars = availableScalars;
    const State& local = this->state(node);
    State reconstructed = this->topState();

    // Copy the complete flow component onto a neutral product. A local reset
    // memory cell is semantically uninitialized, so it must be copied too;
    // treating it as absent would weaken the Post check.
    std::vector<SVF::Variable> localNumericalVariables;
    localNumericalVariables.reserve(
        this->adapter_.memoryLayout().cells().size() + pointScalars.size());
    for (const auto& [location, content] :
            this->adapter_.memoryLayout().cells())
    {
        (void)location;
        reconstructed.assignValueFrom(content, local, content);
        localNumericalVariables.push_back(content);
    }
    // Auxiliary flow coordinates, including allocation extents, have no SSA
    // scalar definition and must be reconstructed with their initialization.
    for (SVF::Variable variable : nonDefaultVariables(local))
        if (!(variable < this->adapter_.firstObjectContentVariable()) &&
                !this->adapter_.contentObject(variable))
        {
            reconstructed.assignValueFrom(variable, local, variable);
            localNumericalVariables.push_back(variable);
        }
    localNumericalVariables.insert(localNumericalVariables.end(),
                                   pointScalars.begin(), pointScalars.end());
    std::sort(localNumericalVariables.begin(), localNumericalVariables.end());
    localNumericalVariables.erase(std::unique(localNumericalVariables.begin(),
            localNumericalVariables.end()),
                                  localNumericalVariables.end());
    reconstructed.lifetimes() = local.lifetimes();

    const State* globalScalars =
        node == this->icfg->getGlobalICFGNode() && globalScalarSnapshot_
        ? &*globalScalarSnapshot_ : nullptr;
    if (globalScalars)
    {
        for (SVF::Variable variable : pointScalars)
            reconstructed.assignValueFrom(variable, *globalScalars, variable);
        State projected = *globalScalars;
        const std::vector<SVF::Variable> variables(pointScalars.begin(),
                pointScalars.end());
        projected.numerical().project(variables);
        reconstructed.numerical().meetWith(projected.numerical());
    }
    else if (Options::AEDomain() != AENumericalDomain::Box)
    {
        const std::vector<SVF::Variable> variables(pointScalars.begin(),
                pointScalars.end());
        // Post computed availability on the final reachable equation graph.
        // Use that same scope throughout reconstruction, including inside
        // materialization. Static all-CFG availability can be smaller when
        // an unreachable predecessor bypasses a definition; filtering twice
        // would silently turn an initialized coordinate into uninitialized.
        materializeScalarDefinitions(reconstructed, variables, node,
                                     &pointScalars);
    }
    else if (const State* carrier = findScalarState())
    {
        // Copy only point-available scalar facets. Whole-product meet would
        // conflate the carrier's "not stored" defaults with flow-state
        // uninitialized memory coordinates.
        for (SVF::Variable variable : pointScalars)
        {
            const auto definition = scalarDefinitions_.find(variable);
            reconstructed.assignValueFrom(
                variable,
                definition != scalarDefinitions_.end()
                ? definition->second : *carrier,
                variable);
        }
    }

    // Copying individual coordinates above intentionally discards relations.
    // Reapply the projected local component last so that scalar--memory and
    // memory--memory relations survive without meeting unrelated product
    // facets from the sparse carrier.
    State projectedLocal = local;
    projectedLocal.numerical().project(localNumericalVariables);
    reconstructed.numerical().meetWith(projectedLocal.numerical());

    const auto refinement = refinementTrace_.find(node);
    if (refinement != refinementTrace_.end())
    {
        State projected = refinement->second;
        std::vector<SVF::Variable> variables(pointScalars.begin(),
                                             pointScalars.end());
        projected.numerical().project(variables);
        applyScalarRefinement(reconstructed, projected);
    }
    return reconstructed;
}

void SemiSparseAbstractInterpretation::normalizePostReplayState(
    State& denseState, const std::set<SVF::Variable>& availableScalars) const
{
    const SVF::Variable contentBegin =
        this->adapter_.firstObjectContentVariable();
    for (SVF::Variable variable : nonDefaultVariables(denseState))
    {
        if (variable < contentBegin && availableScalars.count(variable) == 0)
            this->forgetValue(denseState, variable);
    }
    // Octagon carriers retain forgotten dimensions in their physical layout.
    // Project explicitly so relations through an out-of-scope callee scalar
    // cannot survive normalization and make replay stronger than the return
    // equation's caller-visible state.
    std::vector<SVF::Variable> retainedNumerical;
    for (SVF::Variable variable : denseState.numerical().supportVariables())
        if (!(variable < contentBegin) ||
                availableScalars.count(variable) != 0)
            retainedNumerical.push_back(variable);
    denseState.numerical().project(retainedNumerical);
}

void SemiSparseAbstractInterpretation::preparePostReplayState(
    State& denseState, const ICFGNode* target,
    const std::set<SVF::Variable>& inputScalars) const
{
    (void)inputScalars;
    if (Options::AEDomain() != AENumericalDomain::Box)
        return;
    const auto available = scalarAvailability_.find(target);
    if (available == scalarAvailability_.end())
        return;
    const auto variables = availableScalarVariables(target);
    std::set<SVF::Variable> targetInputs(variables.begin(), variables.end());
    for (SVF::Variable definition :
            definedScalarVariables(target, this->adapter_))
        targetInputs.erase(definition);
    std::vector<SVF::Variable> missingInputs;
    for (SVF::Variable variable : targetInputs)
    {
        // Preserve path-local facts already reconstructed at the source.
        // The global per-definition summary is only a fallback for an input
        // that semi-sparse transfer would materialize on demand but dense Post
        // replay cannot otherwise observe.
        if (!denseState.hasValue(variable))
            missingInputs.push_back(variable);
    }
    materializeScalarDefinitions(denseState, missingInputs, target);
}

void SemiSparseAbstractInterpretation::restorePostReplayCallerFrame(
    State& denseState, const RetICFGNode* returnSite,
    const State& callerState,
    const std::set<SVF::Variable>& callerScalars) const
{
    if (isSharedCalleeReturn(returnSite))
    {
        const bool nonReentrant = preservesCallerFrame(returnSite);
        const FunObjVar* caller = returnSite->getCallICFGNode()->getCaller();
        for (SVF::Variable variable : callerScalars)
        {
            const ValVar* value = this->adapter_.value(variable);
            if (nonReentrant && value && value->getFunction() == caller)
            {
                // Only this activation's available SSA coordinates are
                // immutable along every admitted callee path. Preserve
                // their exit relations with *current* memory, and intersect
                // with the call-site facts. Never restore call-site memory.
                this->constrainInterval(
                    denseState, variable, callerState.interval(variable));
                denseState.restoreMissingNumericalInitializationFrom(
                    callerState, variable);
                denseState.restoreMissingAddressFrom(callerState, variable);
            }
            else
            {
                // Recursion, unknown effects, or a coordinate owned by
                // another function retain the old frame replacement path.
                this->forgetValue(denseState, variable);
                denseState.assignValueFrom(variable, callerState, variable);
            }
        }
        if (!callerScalars.empty() ||
                Options::AEDomain() != AENumericalDomain::Box ||
                callerState.isBottom())
        {
            State projectedCaller = callerState;
            const std::vector<SVF::Variable> callerVariables(
                callerScalars.begin(), callerScalars.end());
            projectedCaller.numerical().project(callerVariables);
            denseState.numerical().meetWith(projectedCaller.numerical());
        }
    }
    else
    {
        for (SVF::Variable variable : callerScalars)
        {
            // The relational flow state can contain a sound relation for a
            // caller SSA coordinate while deliberately omitting that
            // coordinate's initialization carrier.  A strong coordinate
            // assignment would then erase all relations through it.  Caller
            // SSA values are unchanged by a single-call-site callee, so meet
            // their unary bounds and restore only missing product facets.
            this->constrainInterval(
                denseState, variable, callerState.interval(variable));
            denseState.restoreMissingNumericalInitializationFrom(
                callerState, variable);
            denseState.restoreMissingAddressFrom(callerState, variable);
        }
    }
    restoreCallerFrameAfterSharedCallee(denseState, returnSite, &callerState);
}

void SemiSparseAbstractInterpretation::forgetActiveScalarValues(
    State& denseState) const
{
    const SVF::Variable contentBegin =
        this->adapter_.firstObjectContentVariable();
    std::set<SVF::Variable> retainedScalars;
    if (Options::AEDomain() != AENumericalDomain::Box)
    {
        std::vector<SVF::Variable> memorySeeds;
        for (SVF::Variable variable : denseState.numerical().supportVariables())
            if (this->adapter_.contentObject(variable))
                memorySeeds.push_back(variable);
        for (SVF::Variable variable :
                denseState.numerical().relationalClosure(memorySeeds))
            if (variable < contentBegin)
                retainedScalars.insert(variable);
    }
    for (SVF::Variable variable :
            denseState.numerical().supportVariablesBefore(contentBegin))
        if (retainedScalars.count(variable) == 0)
            denseState.numerical().forget(variable);
    for (SVF::Variable variable :
            denseState.addresses().nonDefaultVariablesBefore(contentBegin))
        denseState.addresses().forget(variable);
    for (SVF::Variable variable : denseState.initializedVariablesBefore(contentBegin))
        if (retainedScalars.count(variable) == 0)
            denseState.resetValue(variable);
}

void SemiSparseAbstractInterpretation::forgetMemoryValues(
    State& denseState) const
{
    for (SVF::Variable variable : nonDefaultVariables(denseState))
    {
        if (this->adapter_.contentObject(variable))
            this->forgetValue(denseState, variable);
    }
}

void SemiSparseAbstractInterpretation::restoreCallerFrameAfterSharedCallee(
    State& denseState, const RetICFGNode* returnSite,
    const State* callerOverride) const
{
    if (!returnSite)
        return;
    const CallICFGNode* call = returnSite->getCallICFGNode();
    if (!call || (!callerOverride && !this->hasAbsState(call)))
        return;

    if (!isSharedCalleeReturn(returnSite))
        return;

    const State& caller = callerOverride ? *callerOverride : this->state(call);
    NodeBS exposedBases;
    bool exposesAllObjects = false;
    auto expose = [&](const ObjVar* object)
    {
        if (object)
            exposedBases.set(
                this->svfir->getBaseObject(object->getId())->getId());
    };
    for (const ValVar* actual : call->getActualParms())
    {
        if (!actual || !actual->isPointer())
            continue;
        for (NodeID objectId :
                this->preAnalysis->getPointerAnalysis()->getPts(actual->getId()))
        {
            expose(SVFUtil::dyn_cast<ObjVar>(
                       this->svfir->getGNode(objectId)));
        }
        if (!this->adapter_.contains(*actual))
            continue;
        const SVF::AddressSet addresses = caller.addressSet(
                                              this->adapter_.variable(*actual));
        if (addresses.hasUnknownObject())
        {
            exposesAllObjects = true;
            continue;
        }
        for (SVF::Location location : addresses)
            expose(this->objectAt(location));
    }

    auto restore = [&](SVF::Variable content)
    {
        const ObjVar* object = this->adapter_.contentObject(content);
        const BaseObjVar* base = object
                                 ? this->svfir->getBaseObject(object->getId()) : nullptr;
        if (!base)
            return;
        if (base->isStack() && !exposesAllObjects &&
                !exposedBases.test(base->getId()))
            denseState.restoreMissingMemoryFrom(caller, content);
        else
            denseState.restoreMissingAddressFrom(caller, content);
    };
    for (SVF::Variable content : nonDefaultVariables(caller))
        restore(content);
}

bool SemiSparseAbstractInterpretation::isSharedFunction(
    const FunObjVar* function) const
{
    if (!function)
        return false;
    const ICFGNode* entry = this->icfg->getFunEntryICFGNode(function);
    const std::size_t callers = std::count_if(
                                    entry->getInEdges().begin(), entry->getInEdges().end(),
                                    [](const ICFGEdge* incoming)
    {
        return SVFUtil::isa<CallCFGEdge>(incoming);
    });
    return callers > 1;
}

bool SemiSparseAbstractInterpretation::isSharedCalleeReturn(
    const RetICFGNode* returnSite) const
{
    if (!returnSite)
        return false;
    for (const ICFGEdge* edge : returnSite->getInEdges())
    {
        if (!SVFUtil::isa<RetCFGEdge>(edge) || !edge->getSrcNode()->getFun())
            continue;
        if (isSharedFunction(edge->getSrcNode()->getFun()))
            return true;
    }
    return false;
}

bool SemiSparseAbstractInterpretation::preservesCallerFrame(
    const RetICFGNode* returnSite) const
{
    return returnSite && (!isSharedCalleeReturn(returnSite) ||
                          callerFrameCannotBeReentered(returnSite));
}

bool SemiSparseAbstractInterpretation::callerFrameCannotBeReentered(
    const RetICFGNode* returnSite) const
{
    const auto cached = nonReentrantReturnCache_.find(returnSite);
    if (cached != nonReentrantReturnCache_.end())
        return cached->second;
    const CallICFGNode* call = returnSite ? returnSite->getCallICFGNode() : nullptr;
    const FunObjVar* caller = call ? call->getCaller() : nullptr;
    std::vector<const FunObjVar*> pending;
    std::set<const FunObjVar*> visited;
    // An indirect target set must consist entirely of resolved function
    // objects. An empty/black-hole/non-function target is not a proof.
    const auto appendTargets = [&](const CallICFGNode* site)
    {
        if (const FunObjVar* direct = site->getCalledFunction())
        {
            pending.push_back(direct);
            return true;
        }
        const SVFVar* pointer = site->getIndFunPtr();
        if (!pointer || !this->callGraph->hasIndCSCallees(site))
            return false;
        const auto& targets = this->preAnalysis->getPointerAnalysis()->getPts(
                                  pointer->getId());
        if (targets.empty())
            return false;
        const auto& resolved = this->callGraph->getIndCSCallees(site);
        for (NodeID target : targets)
        {
            const auto* function = SVFUtil::dyn_cast<FunObjVar>(
                                       this->svfir->getGNode(target));
            if (!function || resolved.count(function) == 0)
                return false;
        }
        // Also traverse any extra conservative call-graph target rather
        // than assuming the two representations have identical contents.
        for (const FunObjVar* function : resolved)
            pending.push_back(function);
        return !resolved.empty();
    };
    bool safe = caller && appendTargets(call);
    while (safe && !pending.empty())
    {
        const FunObjVar* function = pending.back();
        pending.pop_back();
        if (function == caller)
        {
            safe = false;
            break;
        }
        if (!visited.insert(function).second)
            continue;
        if (SVFUtil::isExtCall(function))
        {
            // The frozen regression harness defines this zero-argument
            // primitive as fresh nondeterministic input with no callbacks.
            // No libc/unknown external function is inferred callback-free
            // merely because the call graph has no outgoing edge for it.
            if (!Options::AEHarnessNondetNoCallback() ||
                    function->getName() != "nondet_i32")
                safe = false;
            continue;
        }
        for (const CallICFGNode* nested : this->svfir->getCallSiteSet())
            if (nested->getCaller() == function && !appendTargets(nested))
            {
                safe = false;
                break;
            }
    }
    nonReentrantReturnCache_.emplace(returnSite, safe);
    if (std::getenv("SVF_AE_TRACE_CALLER_FRAME"))
        std::cerr << "AE_CALLER_FRAME return="
                  << (returnSite ? returnSite->getId() : 0)
                  << " non_reentrant=" << safe << '\n';
    return safe;
}

void SemiSparseAbstractInterpretation::applyScalarRefinement(
    State& denseState, const State& checkpoint)
{
    if (Options::AEDomain() != AENumericalDomain::Box)
    {
        denseState.numerical().meetWith(checkpoint.numerical());
        return;
    }
    for (SVF::Variable variable : checkpoint.numerical().supportVariables())
    {
        const ValVar* value = this->adapter_.value(variable);
        if (!value || value->isPointer())
            continue;
        this->constrainInterval(denseState, variable,
                                checkpoint.numerical().bound(variable));
        denseState.setAddressSet(variable, SVF::AddressSet::bottom());
    }
}

void SemiSparseAbstractInterpretation::materializeValue(
    State& denseState, const ValVar* value, const ICFGNode* node)
{
    if (!value || !this->adapter_.contains(*value))
        return;
    const SVF::Variable variable = this->adapter_.variable(*value);
    if (value->isPointer())
    {
        denseState.setAddressSet(variable, getAddressSet(value, node));
        denseState.setInterval(variable, SVF::Interval::bottom());
    }
    else
    {
        this->constrainInterval(denseState, variable, getInterval(value, node));
        denseState.setAddressSet(variable, SVF::AddressSet::bottom());
    }
}

void SemiSparseAbstractInterpretation::materializeRelations(
    State& denseState, const std::vector<SVF::Variable>& variables,
    const ICFGNode* node)
{
    if (Options::AEDomain() == AENumericalDomain::Box || variables.empty())
        return;
    State projected = this->topState();
    materializeScalarDefinitions(projected, variables, node);
    denseState.numerical().meetWith(projected.numerical());
}

std::vector<SVF::Variable> SemiSparseAbstractInterpretation::
carrierDependencyClosure(const std::vector<SVF::Variable>& seeds) const
{
    std::set<SVF::Variable> closure(seeds.begin(), seeds.end());
    std::vector<SVF::Variable> worklist(seeds.begin(), seeds.end());
    while (!worklist.empty())
    {
        const SVF::Variable variable = worklist.back();
        worklist.pop_back();
        const auto dependencies = scalarDependencies_.find(variable);
        if (dependencies == scalarDependencies_.end())
            continue;
        for (SVF::Variable dependency : dependencies->second)
        {
            if (closure.insert(dependency).second)
                worklist.push_back(dependency);
        }
    }
    return std::vector<SVF::Variable>(closure.begin(), closure.end());
}

void SemiSparseAbstractInterpretation::materializeScalarDefinitions(
    State& destination, const std::vector<SVF::Variable>& seeds,
    const ICFGNode* node,
    const std::set<SVF::Variable>* availableOverride) const
{
    if (!node || seeds.empty())
        return;
    const auto available = scalarAvailability_.find(node);
    if (!availableOverride && available == scalarAvailability_.end())
        return;

    const auto isAvailable = [&](SVF::Variable variable)
    {
        return (availableOverride ? availableOverride->count(variable) != 0
                : isScalarAvailable(node, variable)) ||
               extraAvailable(node, variable);
    };
    std::set<SVF::Variable> retained;
    for (SVF::Variable seed : seeds)
    {
        if (!isAvailable(seed))
            continue;
        // Keep an available definition even when part of its transitive
        // carrier is out of scope at this point.  Projecting the saved
        // summary below existentially forgets those unavailable coordinates;
        // dropping the whole closure would also drop the seed's value and
        // initialization facet.
        retained.insert(seed);
        const std::vector<SVF::Variable> closure =
            carrierDependencyClosure({seed});
        for (SVF::Variable dependency : closure)
        {
            if (isAvailable(dependency))
                retained.insert(dependency);
        }
    }
    if (retained.empty())
        return;

    const std::vector<SVF::Variable> variables(retained.begin(), retained.end());
    for (SVF::Variable variable : variables)
    {
        const auto definition = scalarDefinitions_.find(variable);
        if (definition != scalarDefinitions_.end())
            destination.assignValueFrom(variable, definition->second, variable);
        else if (scalarState_)
            destination.assignValueFrom(variable, *scalarState_, variable);
    }
    // Coordinate copies intentionally discard relations. Reapply every
    // available definition summary only after initialization/address facets
    // are in place, and never meet whole products with incompatible sparse
    // defaults.
    for (SVF::Variable variable : variables)
    {
        const auto definition = scalarDefinitions_.find(variable);
        if (definition == scalarDefinitions_.end())
            continue;
        State projected = definition->second;
        projected.numerical().project(variables);
        destination.numerical().meetWith(projected.numerical());
    }
    if (std::getenv("SVF_AE_TRACE_SCALAR_SUMMARY"))
    {
        std::cerr << "AE scalar summary materialize node=" << node->getId()
                  << " seeds=";
        for (SVF::Variable variable : seeds)
            std::cerr << variable.id() << ',';
        std::cerr << " retained=";
        for (SVF::Variable variable : variables)
            std::cerr << variable.id() << ',';
        std::cerr << " state=" << destination.numerical().toString() << '\n';
    }
}

void SemiSparseAbstractInterpretation::loadValue(
    const ValVar* pointer, SVF::Interval& interval, SVF::AddressSet& addresses,
    bool& numericalMayBeUninitialized,
    const ICFGNode* node)
{
    Base::loadValue(pointer, interval, addresses,
                    numericalMayBeUninitialized, node);
    if (pointer && this->adapter_.contains(*pointer))
        this->forgetValue(this->ensureState(node),
                          this->adapter_.variable(*pointer));
}

void SemiSparseAbstractInterpretation::storeValue(
    const ValVar* pointer, const SVF::Interval& interval,
    const SVF::AddressSet& addresses, const ICFGNode* node)
{
    Base::storeValue(pointer, interval, addresses, node);
    if (pointer && this->adapter_.contains(*pointer))
        this->forgetValue(this->ensureState(node),
                          this->adapter_.variable(*pointer));
}

SemiSparseAbstractInterpretation::State
SemiSparseAbstractInterpretation::propagatedState(const State& state) const
{
    return state;
}

void SemiSparseAbstractInterpretation::filterPropagatedState(State& state) const
{
    (void)state;
}

bool SemiSparseAbstractInterpretation::mergeStatesFromPredecessors(
    const ICFGNode* node)
{
    const bool traceMerge = std::getenv("SVF_AE_TRACE_SPARSE_MERGE");
    if (traceMerge)
        std::cerr << "AE sparse merge target=" << node->getId() << '\n';
    State merged = flowState(true);
    std::optional<State> mergedRefinement;
    bool refinementIsTop = false;
    bool hasFeasiblePredecessor = false;

    for (const ICFGEdge* edge : node->getInEdges())
    {
        const ICFGNode* predecessor = edge->getSrcNode();
        if (!this->hasAbsState(predecessor))
            continue;

        bool shouldMerge = false;
        const auto* conditional = SVFUtil::dyn_cast<IntraCFGEdge>(edge);
        if (conditional || SVFUtil::isa<CallCFGEdge>(edge))
        {
            shouldMerge = true;
        }
        else if (SVFUtil::isa<RetCFGEdge>(edge))
        {
            const auto* returnSite = SVFUtil::dyn_cast<RetICFGNode>(node);
            shouldMerge = returnSite &&
                          this->hasAbsState(returnSite->getCallICFGNode());
        }
        if (!shouldMerge)
            continue;

        const auto refinementIterator = refinementTrace_.find(predecessor);
        const bool hasConditional = conditional && conditional->getCondition();
        const bool needsRefinement =
            hasConditional || refinementIterator != refinementTrace_.end();
        std::optional<State> refinement;
        if (needsRefinement)
        {
            refinement = refinementIterator != refinementTrace_.end()
                         ? refinementIterator->second
                         : State(this->makeNumericalDomain(false),
                                 this->adapter_.memoryLayout());
            if (hasConditional)
                this->assumeBranch(conditional, *refinement);
            if (refinement->isBottom())
            {
                if (traceMerge)
                    std::cerr << "  predecessor=" << predecessor->getId()
                              << " refinement=bottom\n";
                continue;
            }
        }

        if (traceMerge)
            std::cerr << "  predecessor=" << predecessor->getId()
                      << " refinement="
                      << (refinement ? refinement->numerical().toString()
                          : std::string("top"))
                      << '\n';

        State source = propagatedState(this->state(predecessor));
        this->applyRelationalCallBoundary(source, edge, node);
        if (const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge))
        {
            // Scalar SSA definitions live in the semi-sparse carrier rather
            // than in persistent ICFG states.  A return binding is owned by
            // one callee edge, so reconstruct that edge's formal return in
            // its source state before applying RetPE.  Doing this per edge
            // preserves join(Post_edge) for multi-target calls; materializing
            // after the join would conflate alternative formal returns.
            const RetPE* binding = ret->getRetPE();
            const auto* returned = binding
                                   ? SVFUtil::dyn_cast<ValVar>(
                                       binding->getRHSVar())
                                   : nullptr;
            if (returned && this->adapter_.contains(*returned))
            {
                materializeScalarDefinitions(
                    source, {this->adapter_.variable(*returned)},
                    predecessor);
            }
            this->applyReturnEdgeTransfer(source, ret);
        }
        filterPropagatedState(source);
        if (hasConditional)
            this->collectBranchRefinement(conditional, source);

        merged.joinWith(source);
        if (!refinement || refinement->isTop())
        {
            refinementIsTop = true;
            mergedRefinement.reset();
        }
        else if (!refinementIsTop)
        {
            forgetMemoryValues(*refinement);
            if (!mergedRefinement)
                mergedRefinement = std::move(*refinement);
            else
                mergedRefinement->joinWith(*refinement);
        }
        hasFeasiblePredecessor = true;
    }

    if (!hasFeasiblePredecessor)
    {
        if (traceMerge)
            std::cerr << "  result=unreachable\n";
        return false;
    }
    if (const auto* returnSite = SVFUtil::dyn_cast<RetICFGNode>(node))
    {
        const CallICFGNode* call = returnSite->getCallICFGNode();
        const auto callerAvailability = scalarAvailability_.find(call);
        if (call && this->hasAbsState(call) &&
                callerAvailability != scalarAvailability_.end())
        {
            if (Options::AEDomain() == AENumericalDomain::Box)
            {
                const SVF::Variable end =
                    this->adapter_.firstObjectContentVariable();
                std::set<SVF::Variable> active;
                for (const State* state :
                        {
                            &this->state(call),
                            static_cast<const State*>(&merged)
                        })
                {
                    const auto add = [&](const std::vector<SVF::Variable>& variables)
                    {
                        for (SVF::Variable variable : variables)
                            if (isScalarAvailable(call, variable))
                                active.insert(variable);
                    };
                    add(state->numerical().supportVariablesBefore(end));
                    add(state->addresses().nonDefaultVariablesBefore(end));
                    add(state->initializedVariablesBefore(end));
                }
                // Absent Box coordinates are independent uninitialized facets.
                restorePostReplayCallerFrame(
                    merged, returnSite, this->state(call), active);
            }
            else
            {
                const auto variables = availableScalarVariables(call);
                restorePostReplayCallerFrame(
                    merged, returnSite, this->state(call),
                    std::set<SVF::Variable>(variables.begin(), variables.end()));
            }
        }
    }
    if (mergedRefinement && !refinementIsTop && !mergedRefinement->isTop())
    {
        refinementTrace_.insert_or_assign(node, *mergedRefinement);
        applyScalarRefinement(merged, *mergedRefinement);
    }
    else
    {
        refinementTrace_.erase(node);
    }
    this->abstractTrace_.insert_or_assign(node, std::move(merged));
    if (traceMerge)
        std::cerr << "  result=" << this->state(node).numerical().toString()
                  << '\n';
    return true;
}

std::unique_ptr<SVF::AbstractDomain> SemiSparseAbstractInterpretation::
cloneCycleHeadState(const ICFGCycleWTO* cycle)
{
    const ICFGNode* head = cycle->head()->getICFGNode();
    State snapshot = this->state(head);
    const auto available = scalarAvailability_.find(head);
    std::vector<SVF::Variable> cycleVariables;
    for (const ValVar* value : this->preAnalysis->getCycleValVars(cycle))
    {
        if (!value || !this->adapter_.contains(*value))
            continue;
        const SVF::Variable variable = this->adapter_.variable(*value);
        if (Options::AEDomain() != AENumericalDomain::Box &&
                available != scalarAvailability_.end() &&
                !isScalarAvailable(head, variable))
            continue;
        cycleVariables.push_back(variable);
    }
    if (Options::AEDomain() == AENumericalDomain::Box)
    {
        for (SVF::Variable variable : cycleVariables)
        {
            const auto definition = scalarDefinitions_.find(variable);
            const State& source = definition == scalarDefinitions_.end()
                                  ? scalarState() : definition->second;
            if (source.hasValue(variable))
                snapshot.assignValueFrom(variable, source, variable);
        }
    }
    else
    {
        materializeScalarDefinitions(snapshot, cycleVariables, head);
    }
    const auto refinement = refinementTrace_.find(head);
    if (Options::AEDomain() != AENumericalDomain::Box &&
            refinement != refinementTrace_.end())
    {
        State projected = refinement->second;
        projected.numerical().project(cycleVariables);
        applyScalarRefinement(snapshot, projected);
    }
    if (std::getenv("SVF_AE_TRACE_SPARSE_CYCLE"))
        std::cerr << "AE sparse cycle snapshot head=" << head->getId()
                  << " state=" << snapshot.numerical().toString() << '\n';
    return std::make_unique<State>(std::move(snapshot));
}

void SemiSparseAbstractInterpretation::scatterCycleValues(
    const ICFGCycleWTO* cycle, const State& cycleState)
{
    const ICFGNode* head = cycle->head()->getICFGNode();
    const auto available = scalarAvailability_.find(head);
    for (const ValVar* value : this->preAnalysis->getCycleValVars(cycle))
    {
        if (!value || !this->adapter_.contains(*value))
            continue;
        const SVF::Variable variable = this->adapter_.variable(*value);
        if (Options::AEDomain() != AENumericalDomain::Box &&
                available != scalarAvailability_.end() &&
                !isScalarAvailable(head, variable))
            continue;
        if (Options::AEDomain() == AENumericalDomain::Box &&
                !cycleState.hasValue(variable))
            continue;
        // A widened cycle value is a complete product coordinate.  Copy its
        // initialization guards as well as its numerical/address payloads;
        // rebuilding it from the payload alone turns Top into Initialized
        // and loses the distinction between an unknown value and an
        // uninitialized facet.
        scalarState().assignValueFrom(variable, cycleState, variable);
        if (Options::AEDomain() == AENumericalDomain::Box)
        {
            State summary = this->topState();
            summary.assignValueFrom(variable, cycleState, variable);
            scalarDefinitions_.insert_or_assign(variable,
                                                std::move(summary));
        }
        else
        {
            const auto previous = scalarDefinitions_.find(variable);
            if (previous != scalarDefinitions_.end())
                pendingDefinitionHistory_.insert_or_assign(
                    variable, std::make_pair(head, previous->second));
            else
                pendingDefinitionHistory_.erase(variable);

            State summary = this->topState();
            summary.assignValueFrom(variable, cycleState, variable);
            scalarDefinitions_.insert_or_assign(variable,
                                                std::move(summary));
        }
    }
}

bool SemiSparseAbstractInterpretation::widenCycleState(
    const SVF::AbstractDomain& previous, const SVF::AbstractDomain& current,
    const ICFGCycleWTO* cycle)
{
    const bool fixpoint = Base::widenCycleState(previous, current, cycle);
    if (std::getenv("SVF_AE_TRACE_SPARSE_CYCLE"))
        std::cerr
                << "AE sparse cycle widen head="
                << cycle->head()->getICFGNode()->getId() << " fixpoint=" << fixpoint
                << " state="
                << this->state(cycle->head()->getICFGNode()).numerical().toString()
                << '\n';
    scatterCycleValues(cycle, this->state(cycle->head()->getICFGNode()));
    finalizeAbstractState(cycle->head()->getICFGNode());
    return fixpoint;
}

bool SemiSparseAbstractInterpretation::narrowCycleState(
    const SVF::AbstractDomain& previous, const SVF::AbstractDomain& current,
    const ICFGCycleWTO* cycle)
{
    const bool fixpoint = Base::narrowCycleState(previous, current, cycle);
    if (std::getenv("SVF_AE_TRACE_SPARSE_CYCLE"))
        std::cerr
                << "AE sparse cycle narrow head="
                << cycle->head()->getICFGNode()->getId() << " fixpoint=" << fixpoint
                << " state="
                << this->state(cycle->head()->getICFGNode()).numerical().toString()
                << '\n';
    if (!fixpoint)
    {
        scatterCycleValues(cycle, this->state(cycle->head()->getICFGNode()));
    }
    finalizeAbstractState(cycle->head()->getICFGNode());
    return fixpoint;
}

void AbstractInterpretation::initializeSparseObjectRoutes()
{
    objectRouteBuilder_ = std::make_unique<SVFGBuilder>(true);
    objectRouteBuilder_->buildFullSVFG(preAnalysis->getPointerAnalysis());
    objectRoutes_ = std::make_unique<SparseObjGraph>(
        *objectRouteBuilder_->getSVFG(), *icfg,
        *preAnalysis->getPointerAnalysis(), *svfir);
    if (relationalPacking_)
        for (const auto& pack : *relationalPacking_)
            if (pack.size() > 1)
                packedObjectCoordinates_.insert(pack.begin(), pack.end());
    const auto allocationOnly = [](const FunObjVar* function)
    {
        if (!function || !SVFUtil::isExtCall(function))
            return false;
        bool allocation = false;
        for (const auto& raw : ExtAPI::getExtAPI()->getExtFuncAnnotations(function))
        {
            const auto annotation = raw.substr(0, raw.find('\0'));
            if (annotation == "ALLOC_HEAP_RET")
                allocation = true;
            else if (annotation.rfind("AllocSize:", 0) != 0)
                return false;
        }
        return allocation;
    };
    const auto allocationOnlyUsers = [this, &allocationOnly](const CopyStmt* copy)
    {
        bool used = false;
        for (const auto* use : copy->getLHSVar()->getOutEdges())
        {
            const auto* binding = SVFUtil::dyn_cast<CallPE>(use);
            if (!binding || !allocationOnly(binding->getFunEntryICFGNode()->getFun()))
                return false;
            used = true;
        }
        // External actual arguments need not have explicit CallPE edges.
        for (auto it = icfg->begin(); it != icfg->end(); ++it)
            if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(it->second))
                for (const ValVar* actual : call->getActualParms())
                    if (actual == copy->getLHSVar())
                    {
                        if (!allocationOnly(call->getCalledFunction()))
                            return false;
                        used = true;
                    }
        return used;
    };
    auto* pta = preAnalysis->getPointerAnalysis();
    for (auto it = icfg->begin(); it != icfg->end(); ++it)
    {
        for (const SVFStmt* statement : it->second->getSVFStmts())
        {
            if (const auto* copy = SVFUtil::dyn_cast<CopyStmt>(statement))
                objectRouteFallbackAll_ |=
                    copy->getCopyKind() == CopyStmt::INTTOPTR &&
                    !allocationOnlyUsers(copy);
            if (const auto* store = SVFUtil::dyn_cast<StoreStmt>(statement))
            {
                const auto& targets = pta->getPts(store->getLHSVarID());
                objectRouteFallbackAll_ |=
                    targets.empty() || targets.test(svfir->getBlackHoleNode());
            }
        }
        const auto* call = SVFUtil::dyn_cast<CallICFGNode>(it->second);
        if (!call || (call->getCalledFunction() &&
                      !SVFUtil::isExtCall(call->getCalledFunction())))
            continue;
        std::vector<NodeID> pending;
        NodeBS seen;
        for (const ValVar* arg : call->getActualParms())
            if (arg->isPointer())
                pending.push_back(arg->getId());
        while (!pending.empty())
        {
            const NodeID id = pending.back();
            pending.pop_back();
            if (seen.test(id))
                continue;
            seen.set(id);
            for (NodeID target : pta->getPts(id))
            {
                if (target == svfir->getBlackHoleNode())
                {
                    objectRouteFallbackAll_ = true;
                    continue;
                }
                for (NodeID field :
                     svfir->getAllFieldsObjVars(svfir->getBaseObject(target)))
                {
                    const auto* obj =
                        SVFUtil::dyn_cast<ObjVar>(svfir->getSVFVar(field));
                    if (!obj)
                        continue;
                    objectRouteFallback_.insert(adapter_.contentVariable(*obj));
                    pending.push_back(field);
                }
            }
        }
    }
}

bool AbstractInterpretation::routesObject(SVF::Variable variable) const
{
    if (!objectRoutes_ || objectRouteFallbackAll_ ||
        objectRouteFallback_.count(variable))
        return false;
    return !packedObjectCoordinates_.count(variable);
}

AbstractInterpretation::State AbstractInterpretation::sparseObjectPredecessor(
    const State& source) const
{
    if (!objectRoutes_ || objectRouteFallbackAll_ || source.isBottom())
        return source;
    const auto& cells = adapter_.memoryLayout().cells();
    for (auto it = cells.upper_bound(lastRoutedLocation_); it != cells.end();
         ++it)
    {
        if (routesObject(it->second))
            routedObjectVariables_.insert(it->second);
        lastRoutedLocation_ = it->first;
    }
    if (source.numerical().kind() == SVF::DomainKind::Box)
        return source.withoutValues(routedObjectVariables_);
    State result = source;
    for (auto variable : routedObjectVariables_)
        result.resetValue(variable);
    return result;
}

void AbstractInterpretation::recordSparseObjectStore(
    const ICFGNode* node, const SVF::AddressSet& targets)
{
    if (targets.hasUnknownObject())
        return;
    for (auto location : targets)
        if (const auto* object = objectAt(location))
        {
            const auto content = adapter_.contentVariable(*object);
            if (memoryVariable(*object, state(node)) == content)
                objectRouteDefinitions_[node].insert(content);
        }
}

void AbstractInterpretation::pullSparseObjectRoutes(const ICFGNode* node,
                                                    const State* previous)
{
    const auto previousSupport = objectRouteDefinitions_[node];
    objectRoutePreviousDefinitions_[node] = previousSupport;
    objectRouteDefinitions_.erase(node);
    State& merged = ensureState(node);
    std::set<SVF::Variable> pulled;
    for (const auto* edge : objectRoutes_->getInputs(node))
    {
        const auto* route = edge->getSrcNode();
        const auto* sourceNode = route->getICFGNode();
        const State* input =
            sourceNode == node
                ? previous
                : (hasAbsState(sourceNode) ? &state(sourceNode) : nullptr);
        if (!input || input->isBottom())
            continue;
        std::optional<State> refined;
        const State* source = input;
        if (route->branch)
        {
            refined = *input;
            assumeBranch(route->branch, *refined);
            collectBranchRefinement(route->branch, *refined);
            if (refined->isBottom())
                continue;
            source = &*refined;
        }
        for (NodeID id :
             svfir->getAllFieldsObjVars(svfir->getBaseObject(route->base)))
        {
            const auto* object =
                SVFUtil::dyn_cast<ObjVar>(svfir->getSVFVar(id));
            if (!object)
                continue;
            const auto content = adapter_.contentVariable(*object);
            if (!routesObject(content))
                continue;
            const auto from = memoryVariable(*object, *source),
                       to = memoryVariable(*object, merged);
            if (pulled.insert(content).second)
                merged.assignValueFrom(to, *source, from);
            else
                merged.joinValueFrom(to, *source, from);
            objectRouteDefinitions_[node].insert(content);
        }
    }
}

FullSparseAbstractInterpretation::FullSparseAbstractInterpretation()
{
    initializeSparseObjectRoutes();
}
FullSparseAbstractInterpretation::~FullSparseAbstractInterpretation() = default;
FullSparseAbstractInterpretation::State
FullSparseAbstractInterpretation::reconstructPostState(
    const ICFGNode* node, const std::set<SVF::Variable>& availableScalars)
{
    State result = Base::reconstructPostState(node, availableScalars);
    if (!objectRoutes_ || objectRouteFallbackAll_ || result.isBottom())
        return result;

    std::map<NodeID, std::set<SVF::Variable>> groups;
    for (const auto& [location, content] : adapter_.memoryLayout().cells())
    {
        (void)location;
        const auto* object = adapter_.contentObject(content);
        if (object && routesObject(content))
            groups[svfir->getBaseObject(object->getId())->getId()].insert(content);
    }
    std::map<const ICFGNode*, State> observations;
    observations.emplace(node, result);
    const auto observe = [&](const ICFGNode* point) -> const State&
    {
        const auto cached = observations.find(point);
        if (cached != observations.end())
            return cached->second;
        const auto variables = availableScalarVariables(point);
        return observations.emplace(point,
                   Base::reconstructPostState(point,
                       std::set<SVF::Variable>(variables.begin(), variables.end()))).first->second;
    };
    for (const auto& group : groups)
    {
        const auto base = group.first;
        const auto& contents = group.second;
        const auto represented = [&](const ICFGNode* point)
        {
            if (point == icfg->getGlobalICFGNode() || point->getInEdges().empty())
                return true;
            for (const auto* edge : objectRoutes_->getInputs(point))
                if (edge->getDstNode()->base == base)
                    return true;
            const auto support = objectRouteDefinitions_.find(point);
            for (auto content : contents)
                if (state(point).hasValue(content) ||
                        (support != objectRouteDefinitions_.end() &&
                         support->second.count(content)))
                    return true;
            for (const auto* statement : point->getSVFStmts())
                if (const auto* address = SVFUtil::dyn_cast<AddrStmt>(statement))
                    if (svfir->getBaseObject(address->getRHSVarID())->getId() == base)
                        return true;
            return false;
        };
        if (represented(node))
            continue;

        // Recorded object events remain authoritative, including explicitly
        // uninitialized cells. Only omitted observations inherit route values.
        State values = topState();
        bool found = false;
        std::set<const ICFGNode*> visited;
        std::deque<std::pair<const ICFGNode*, const IntraCFGEdge*>> pending;
        pending.emplace_back(node, nullptr);
        while (!pending.empty())
        {
            const auto [point, branch] = pending.front();
            pending.pop_front();
            if (!hasAbsState(point) || state(point).isBottom())
                continue;
            if (represented(point))
            {
                State source = observe(point);
                if (branch)
                {
                    assumeBranch(branch, source);
                    collectBranchRefinement(branch, source);
                }
                if (source.isBottom()) continue;
                for (auto content : contents)
                    if (!found) values.assignValueFrom(content, source, content);
                    else values.joinValueFrom(content, source, content);
                found = true;
                continue;
            }
            if (!visited.insert(point).second)
                continue;
            for (const auto* incoming : point->getInEdges())
            {
                const auto* predecessor = incoming->getSrcNode();
                if (!hasAbsState(predecessor) || state(predecessor).isBottom())
                    continue;
                const auto* edge = SVFUtil::dyn_cast<IntraCFGEdge>(incoming);
                const bool conditional = edge && edge->getCondition();
                if (conditional)
                {
                    State feasible = observe(predecessor);
                    assumeBranch(edge, feasible);
                    if (feasible.isBottom()) continue;
                }
                pending.emplace_back(predecessor, conditional ? edge : nullptr);
            }
        }
        if (found)
            for (auto content : contents)
                result.assignValueFrom(content, values, content);
    }
    return result;
}
void FullSparseAbstractInterpretation::restorePostReplayCallerFrame(
    State& replayed, const RetICFGNode* returnSite, const State& caller,
    const std::set<SVF::Variable>& callerScalars) const
{
    Base::restorePostReplayCallerFrame(replayed, returnSite, caller,
                                       callerScalars);
    if (!objectRoutes_ || objectRouteFallbackAll_)
        return;

    std::map<NodeID, bool> preserved;
    for (const auto* edge : objectRoutes_->getInputs(returnSite))
    {
        const auto base = edge->getDstNode()->base;
        const auto* source = edge->getSrcNode();
        const bool bypass = !source->branch &&
                            source->getICFGNode() ==
                            returnSite->getCallICFGNode();
        const auto inserted = preserved.emplace(base, bypass);
        if (!inserted.second)
            inserted.first->second &= bypass;
    }
    // A caller-only route carries an object unchanged across the call.
    // A callee output, including a mixed-target output, remains authoritative.
    for (const auto& [location, content] : adapter_.memoryLayout().cells())
    {
        (void)location;
        const auto* object = adapter_.contentObject(content);
        if (!object || !routesObject(content))
            continue;
        const auto found = preserved.find(
                               svfir->getBaseObject(object->getId())->getId());
        if (found != preserved.end() && found->second)
            replayed.assignValueFrom(content, caller, content);
    }
}
FullSparseAbstractInterpretation::State FullSparseAbstractInterpretation::
    propagatedState(const State& source) const
{
    return sparseObjectPredecessor(source);
}
bool FullSparseAbstractInterpretation::mergeStatesFromPredecessors(
    const ICFGNode* node)
{
    std::optional<State> previous;
    if (hasAbsState(node))
        previous = state(node);
    if (!SemiSparseAbstractInterpretation::mergeStatesFromPredecessors(node))
        return false;
    if (SVFUtil::isa<RetICFGNode>(node))
        ensureState(node) = sparseObjectPredecessor(state(node));
    pullSparseObjectRoutes(node, previous ? &*previous : nullptr);
    return true;
}

bool FullSparseAbstractInterpretation::widenCycleState(
    const SVF::AbstractDomain& previous, const SVF::AbstractDomain& current,
    const ICFGCycleWTO* cycle)
{
    const ICFGNode* head = cycle->head()->getICFGNode();
    const auto old = objectRoutePreviousDefinitions_.find(head);
    const std::set<SVF::Variable> empty;
    const std::set<SVF::Variable>& oldSupport =
        old == objectRoutePreviousDefinitions_.end() ? empty : old->second;
    auto& support = objectRouteDefinitions_[head];
    support.insert(oldSupport.begin(), oldSupport.end());
    const bool supportFixpoint = support == oldSupport;
    if (support.empty())
        objectRouteDefinitions_.erase(head);
    return Base::widenCycleState(previous, current, cycle) &&
           supportFixpoint;
}

bool FullSparseAbstractInterpretation::narrowCycleState(
    const SVF::AbstractDomain& previous, const SVF::AbstractDomain& current,
    const ICFGCycleWTO* cycle)
{
    const ICFGNode* head = cycle->head()->getICFGNode();
    const auto old = objectRoutePreviousDefinitions_.find(head);
    const auto next = objectRouteDefinitions_.find(head);
    const bool oldEmpty = old == objectRoutePreviousDefinitions_.end() ||
                          old->second.empty();
    const bool nextEmpty = next == objectRouteDefinitions_.end() ||
                           next->second.empty();
    const bool supportFixpoint =
        (oldEmpty && nextEmpty) ||
        (!oldEmpty && !nextEmpty && old->second == next->second);
    return Base::narrowCycleState(previous, current, cycle) &&
           supportFixpoint;
}


} // namespace SVF
