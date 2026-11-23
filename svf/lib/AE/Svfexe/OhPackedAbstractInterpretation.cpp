//===- OhPackedAbstractInterpretation.cpp -- Oh Packed Abstract Interpretation --------===//
//
//                     SVF: Static Value-Flow Analysis
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

// SPDX-License-Identifier: AGPL-3.0-or-later
#include "AE/Svfexe/OhPackedAbstractInterpretation.h"
#include "Util/Options.h"
#include <chrono>
#include <functional>
#include <fstream>
#include <stdexcept>

using namespace SVF;

void OhPackedAbstractInterpretation::initializeExecutionPolicy()
{
    const auto start = std::chrono::steady_clock::now();
    Defs all;
    bool mutated = false;
    const SVF::PackedRelationalDomain schema(relationalPacking_);
    for (auto p : schema.relationalPackIndices()) all.insert(p);
    PackSSA::NodeDefinitions writes;
    PackSSA::EdgeDefinitions edgeWrites;
    std::map<SVF::Variable, Defs> variableOwners;
    for (auto pack : all)
        for (auto variable : relationalPacking_->at(pack))
            variableOwners[variable].insert(pack);
    const auto owners = [&](const std::set<SVF::Variable>& variables)
    {
        Defs packs;
        for (const auto variable : variables)
        {
            const auto direct = variableOwners.find(variable);
            if (direct != variableOwners.end())
                packs.insert(direct->second.begin(), direct->second.end());
            if (const auto* object = adapter_.contentObject(variable))
            {
                const auto* base = svfir->getBaseObject(object->getId());
                const auto found = objectPacks_.find(base);
                if (found != objectPacks_.end() && all.count(found->second))
                    packs.insert(found->second);
            }
        }
        return packs;
    };
    std::map<const SVFBasicBlock*, Defs> phiWrites;
    for (auto it = icfg->begin(); it != icfg->end(); ++it)
        for (const SVFStmt* stmt : it->second->getSVFStmts())
            if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(stmt))
                if (phiEdgeBlock(it->second->getBB()))
                {
                    const auto* target = SVFUtil::cast<ValVar>(phi->getRes());
                    const auto packs = owners({adapter_.variable(*target)});
                    auto& blockWrites = phiWrites[it->second->getBB()];
                    blockWrites.insert(packs.begin(), packs.end());
                }
    for (auto it = icfg->begin(); it != icfg->end(); ++it)
    {
        const auto* node = it->second;
        // Calls and unsupported transfers can change globally carried
        // coordinates, including the caller relations restored at return.
        bool completeWrite = !SVFUtil::isa<IntraICFGNode>(node);
        Defs defs;
        for (const SVFStmt* stmt : node->getSVFStmts())
        {
            const ValVar* target = nullptr;
            if (const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt)) target = binary->getRes();
            else if (const auto* cmp = SVFUtil::dyn_cast<CmpStmt>(stmt)) target = cmp->getRes();
            else if (const auto* copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
                target = SVFUtil::dyn_cast<ValVar>(copy->getLHSVar());
            else if (SVFUtil::isa<BranchStmt>(stmt) ||
                     (SVFUtil::isa<PhiStmt>(stmt) && phiEdgeBlock(node->getBB()))) continue;
            else
            {
                completeWrite = true;
                continue;
            }
            if (!target || !adapter_.contains(*target))
            {
                completeWrite = true;
                continue;
            }
            const auto packs = owners({adapter_.variable(*target)});
            defs.insert(packs.begin(), packs.end());
        }
        if (!completeWrite && !defs.empty() && !mutated &&
                std::getenv("SVF_AE_OH_DROP_DEFINITION"))
        {
            defs.clear();
            mutated = true;
        }
        writes[node] = completeWrite ? all : std::move(defs);
        const SVFBasicBlock* block = node->getBB();
        const bool phiEntry = block && phiWrites.count(block) &&
                              !block->getICFGNodeList().empty() &&
                              block->getICFGNodeList().front() == node;
        for (const ICFGEdge* incoming : node->getInEdges())
            if (const auto* edge = SVFUtil::dyn_cast<IntraCFGEdge>(incoming))
            {
                Defs edgeDefs = owners(branchWrites(edge));
                if (phiEntry)
                    edgeDefs.insert(phiWrites.at(block).begin(), phiWrites.at(block).end());
                if (std::getenv("SVF_AE_OH_ALL_EDGE_DEFINITIONS") &&
                        (edge->getCondition() || phiEntry))
                    edgeDefs = all;
                edgeWrites[edge] = std::move(edgeDefs);
            }
    }
    packSSA_ = std::make_unique<PackSSA>(*icfg, all, writes, edgeWrites);
    // Edge and input values consumed immediately by a local transfer remain
    // transient. Persist only versions referenced by saved node observations.
    for (auto it = icfg->begin(); it != icfg->end(); ++it)
        for (const auto& [pack, version] : packSSA_->after(it->second))
        {
            (void)pack;
            retainedVersions_.insert(version);
        }
    if (const char* path = std::getenv("SVF_AE_PACK_SSA_DUMP"))
    {
        std::ofstream output(path);
        if (!output) throw std::runtime_error("Cannot open pack SSA graph dump");
        packSSA_->dump(output);
    }
    graphSeconds_=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    SVFUtil::outs() << "AE_OH_GRAPH packs=" << all.size()
                   << " versions=" << packSSA_->versions().size()
                   << " interfaces=" << packSSA_->connections().size()
                   << " dense_slots=" << icfg->getTotalNodeNum() * all.size()
                   << " uses=ssa auxiliary=dense graph_s=" << graphSeconds_ << '\n';
}

const OhPackedAbstractInterpretation::Pack& OhPackedAbstractInterpretation::definition(
    PackSSA::VersionID version) const
{
    const auto& def = packSSA_->versions().at(version);
    if (def.node)
    {
        const auto raw = abstractTrace_.find(def.node);
        const auto& after = packSSA_->after(def.node);
        const auto route = after.find(def.pack);
        const auto& output = packSSA_->outputDefinitions(def.node);
        if (raw != abstractTrace_.end() && route != after.end() && route->second == version &&
                output.count(def.pack) && output.at(def.pack) == version &&
                raw->second.numerical().isDomain<SVF::PackedRelationalDomain>())
            return static_cast<const SVF::PackedRelationalDomain&>(raw->second.numerical()).packState(def.pack);
    }
    const auto stored = storedPacks_.find(version);
    if (stored == storedPacks_.end())
        throw std::runtime_error("Oh missing pack SSA version " + std::to_string(version));
    return stored->second;
}

void OhPackedAbstractInterpretation::saveDefinitions(
    const PackSSA::Routes& definitions, const State& state)
{
    const auto& numerical = static_cast<const SVF::PackedRelationalDomain&>(state.numerical());
    for (const auto& [pack, version] : definitions)
        if (retainedVersions_.count(version))
            storedPacks_.insert_or_assign(version, numerical.packState(pack));
}

void OhPackedAbstractInterpretation::recordIncomingAbstractState(
    const ICFGEdge* incoming, const State& source)
{
    if (recheckStates_) return;
    if (const auto* edge = SVFUtil::dyn_cast<IntraCFGEdge>(incoming))
    {
        const auto& definitions = packSSA_->edgeDefinitions(edge);
        if (std::getenv("SVF_AE_VERIFY_PACK_EDGES") && !source.isBottom())
        {
            const auto& before = static_cast<const SVF::PackedRelationalDomain&>(
                                     state(edge->getSrcNode()).numerical());
            const auto& after = static_cast<const SVF::PackedRelationalDomain&>(source.numerical());
            for (auto pack : after.relationalPackIndices())
                if (!definitions.count(pack))
                {
                    ++edgeChecks_;
                    if (before.packState(pack).isEquivalentTo(after.packState(pack)) != SVF::CheckResult::True)
                        throw std::runtime_error("Oh undeclared edge pack write " +
                            std::to_string(edge->getSrcID()) + " -> " + std::to_string(edge->getDstID()) +
                            " pack " + std::to_string(pack));
                }
        }
        saveDefinitions(definitions, source);
        invalidateReadCache();
    }
}

AbstractInterpretation::State OhPackedAbstractInterpretation::reconstruct(const ICFGNode* node) const
{
    State result=abstractTrace_.at(node);
    if (result.numerical().isDomain<SVF::PackedRelationalDomain>()) return result;
    if (!result.numerical().isDomain<SVF::BoxDomain>()) throw std::logic_error("Oh storage kind");
    auto domain=std::make_unique<SVF::PackedRelationalDomain>(relationalPacking_);
    std::vector<Pack> packs;
    const auto& route=packSSA_->after(node);
    for (const auto& [p,source]:route) packs.push_back(definition(source));
    domain->restoreRelationalComponents(static_cast<const SVF::BoxDomain&>(result.numerical()),std::move(packs));
    result.replaceNumericalStorage(std::move(domain));
    return result;
}

const AbstractInterpretation::State& OhPackedAbstractInterpretation::state(const ICFGNode* node) const
{
    if (recheckStates_) return AbstractInterpretation::state(node);
    const State& raw=abstractTrace_.at(node);
    if (raw.numerical().isDomain<SVF::PackedRelationalDomain>()) return raw;
    // No cache reuse across writes. References are consumed within one shared
    // transfer; owned clones are used across recursive calls and loop steps.
    auto hit=readCache_.find(node);
    if (hit==readCache_.end()) hit=readCache_.emplace(node,std::make_unique<State>(reconstruct(node))).first;
    peakReadCacheNodes_=std::max(peakReadCacheNodes_,readCache_.size()+retiredReadCache_.size());
    return *hit->second;
}

void OhPackedAbstractInterpretation::invalidateReadCache()
{
    for (auto& item:readCache_) retiredReadCache_.push_back(std::move(item.second));
    readCache_.clear();
}

AbstractInterpretation::State& OhPackedAbstractInterpretation::ensureState(const ICFGNode* node)
{
    if (recheckStates_ && recheckStates_->count(node)) return AbstractInterpretation::ensureState(node);
    invalidateReadCache();
    auto hit=abstractTrace_.find(node);
    if (hit==abstractTrace_.end())
    {
        hit=abstractTrace_.emplace(node,topState()).first;
        saveDefinitions(packSSA_->inputDefinitions(node), hit->second);
    }
    else if (!hit->second.numerical().isDomain<SVF::PackedRelationalDomain>())
    {
        State full=reconstruct(node);
        hit->second=std::move(full);
        ++restored_;
    }
    expanded_.insert(node);
    return hit->second;
}

void OhPackedAbstractInterpretation::compact(const ICFGNode* node)
{
    auto it=abstractTrace_.find(node);
    if (it==abstractTrace_.end() || !it->second.numerical().isDomain<SVF::PackedRelationalDomain>()) return;
    auto& numerical=static_cast<SVF::PackedRelationalDomain&>(it->second.numerical());
    const auto& output = packSSA_->outputDefinitions(node);
    const auto& routes = packSSA_->after(node);
    for (auto p : numerical.relationalPackIndices())
    {
        const auto version = routes.at(p);
        if (output.count(p))
            storedPacks_.insert_or_assign(version, numerical.packState(p));
        else
        {
            ++omittedChecks_;
            if (numerical.packState(p).isEquivalentTo(definition(version)) != SVF::CheckResult::True)
                throw std::runtime_error("Oh undeclared pack write at node " + std::to_string(node->getId()) +
                                         " pack " + std::to_string(p));
        }
    }
    auto fallback=std::make_unique<SVF::BoxDomain>(numerical.fallbackState());
    it->second.replaceNumericalStorage(std::move(fallback));
    expanded_.erase(node);
    readCache_.clear();
    retiredReadCache_.clear();
}

void OhPackedAbstractInterpretation::compactBorrowed()
{
    const auto pending=expanded_;
    for (const auto* node:pending) if (!active_.count(node)) compact(node);
}
void OhPackedAbstractInterpretation::beginAbstractState(const ICFGNode* node)
{
    ++active_[node];
    State& incoming = ensureState(node);
    saveDefinitions(packSSA_->inputDefinitions(node), incoming);
}
void OhPackedAbstractInterpretation::finalizeAbstractState(const ICFGNode* node)
{
    auto it=active_.find(node);
    if (it!=active_.end() && --it->second==0) active_.erase(it);
    if (!active_.count(node)) compact(node);
    compactBorrowed();
}
bool OhPackedAbstractInterpretation::mergeStatesFromPredecessors(const ICFGNode* node)
{
    compactBorrowed();
    readCache_.clear();
    retiredReadCache_.clear();
    const bool merged=AbstractInterpretation::mergeStatesFromPredecessors(node);
    if (merged)
    {
        // A cycle head can be merged again before its statements execute.
        saveDefinitions(packSSA_->inputDefinitions(node), abstractTrace_.at(node));
        expanded_.insert(node);
    }
    return merged;
}
void OhPackedAbstractInterpretation::resetAbstractState(const ICFGNode* node)
{
    readCache_.clear();
    AbstractInterpretation::resetAbstractState(node);
    saveDefinitions(packSSA_->inputDefinitions(node), abstractTrace_.at(node));
    expanded_.insert(node);
}
void OhPackedAbstractInterpretation::copyAbstractState(const ICFGNode* source,const ICFGNode* destination)
{
    State copy=state(source);
    readCache_.clear();
    abstractTrace_.insert_or_assign(destination,std::move(copy));
    saveDefinitions(packSSA_->inputDefinitions(destination), abstractTrace_.at(destination));
    expanded_.insert(destination);
}
void OhPackedAbstractInterpretation::handleGlobalNode()
{
    AbstractInterpretation::handleGlobalNode();
    compact(icfg->getGlobalICFGNode());
}
bool OhPackedAbstractInterpretation::widenCycleState(const SVF::AbstractDomain& a,
        const SVF::AbstractDomain& b,const ICFGCycleWTO* cycle)
{
    const bool result=AbstractInterpretation::widenCycleState(a,b,cycle);
    const ICFGNode* head = cycle->head()->getICFGNode();
    const auto& input = packSSA_->inputDefinitions(head);
    PackSSA::Routes widened;
    for (const auto& [pack, version] : input)
        if (packSSA_->after(head).at(pack) == version) widened.emplace(pack, version);
    saveDefinitions(widened, state(head));
    compact(head);
    return result;
}
bool OhPackedAbstractInterpretation::narrowCycleState(const SVF::AbstractDomain& a,
        const SVF::AbstractDomain& b,const ICFGCycleWTO* cycle)
{
    const bool result=AbstractInterpretation::narrowCycleState(a,b,cycle);
    const ICFGNode* head = cycle->head()->getICFGNode();
    const auto& input = packSSA_->inputDefinitions(head);
    PackSSA::Routes widened;
    for (const auto& [pack, version] : input)
        if (packSSA_->after(head).at(pack) == version) widened.emplace(pack, version);
    saveDefinitions(widened, state(head));
    compact(head);
    return result;
}
void OhPackedAbstractInterpretation::runOnModule()
{
    AbstractInterpretation::runOnModule();
    if (!relationalPacking_)
        return;
    compactBorrowed();
    if (std::getenv("SVF_AE_OH_CACHE_CHECK")) checkCacheInvalidation();
    if (const char* path = std::getenv("SVF_AE_PACK_STATE_DUMP"))
    {
        std::ofstream output(path);
        if (!output) throw std::runtime_error("Cannot open pack state dump");
        for (const auto& [node, stored] : abstractTrace_)
        {
            (void)stored;
            const auto& numerical = static_cast<const SVF::PackedRelationalDomain&>(state(node).numerical());
            for (auto pack : numerical.relationalPackIndices())
                output << node->getId() << '\t' << pack << '\t' << numerical.packState(pack).toString() << '\n';
            readCache_.clear();
        }
    }
    const std::size_t slots = storedPacks_.size();
    SVFUtil::outs()<<"AE_OH_STORAGE pack_slots="<<slots<<" flow_states="<<abstractTrace_.size()
                   <<" restored="<<restored_<<" identity_checks="<<omittedChecks_
                   <<" edge_identity_checks="<<edgeChecks_
                   <<" peak_read_cache_nodes="<<peakReadCacheNodes_
                   <<" peak_read_cache_pack_slots="<<peakReadCacheNodes_*std::count_if(relationalPacking_->begin(),relationalPacking_->end(),
                           [](const auto& pack)
    {
        return pack.size()>1;
    })
            <<" post_replay=dense"<<'\n';
    readCache_.clear();
    retiredReadCache_.clear();
}

void OhPackedAbstractInterpretation::checkCacheInvalidation()
{
    // A focused accessor-contract regression, after analysis and Post. Save
    // and restore the source exactly; no detector result is produced here.
    for (const auto& item:abstractTrace_)
    {
        const auto* node=item.first;
        if (!abstractTrace_.count(node)) continue;
        for (const auto& [p, version] : packSSA_->after(node))
        {
            const auto* source = packSSA_->versions().at(version).node;
            if (!source || source == node || !abstractTrace_.count(source) ||
                    packSSA_->after(source).at(p) != version) continue;
            compact(node);
            compact(source);
            State original=state(source);
            const State& oldRead=state(node);
            auto replacement=std::make_unique<SVF::PackedRelationalDomain>(relationalPacking_);
            replacement->assign(relationalPacking_->at(p).front(),SVF::LinearExpression(SVF::Rational(42)));
            const Pack expected=replacement->packState(p);
            ensureState(source).replaceNumericalStorage(std::move(replacement));
            const auto& observed=static_cast<const SVF::PackedRelationalDomain&>(state(node).numerical());
            // A bottom fallback may normalize the whole product; select a
            // reachable sample for which the old Box state is non-bottom.
            const bool good=observed.packState(p).isEquivalentTo(expected)==SVF::CheckResult::True;
            (void)oldRead.numerical().isBottom(); // old reference remains valid
            abstractTrace_.insert_or_assign(source,std::move(original));
            invalidateReadCache();
            compact(source);
            if (!good) throw std::runtime_error("Oh cache invalidation regression");
            SVFUtil::outs()<<"AE_OH_CACHE_CHECK Pass\n";
            return;
        }
    }
    // With no relational locations there is no reaching-pack route. Exercise
    // the actual dense Box reconstruction cache at the same node instead.
    const SVF::PackedRelationalDomain schema(relationalPacking_);
    if(schema.materializedPackCount()==0)
        for(const auto& entry:abstractTrace_)
        {
            const auto* node=entry.first;
            State original=state(node);
            if(original.numerical().isBottom()) continue;
            const State& oldRead=state(node);
            auto replacement=std::make_unique<SVF::PackedRelationalDomain>(relationalPacking_);
            if(relationalPacking_->empty()) break;
            const auto variable=relationalPacking_->front().front();
            replacement->assign(variable,SVF::LinearExpression(SVF::Rational(42)));
            ensureState(node).replaceNumericalStorage(std::move(replacement));
            const bool good=state(node).numerical().bound(variable)==SVF::Interval::singleton(SVF::Rational(42));
            (void)oldRead.numerical().isBottom();
            abstractTrace_.insert_or_assign(node,std::move(original));
            invalidateReadCache();
            compact(node);
            if(!good) throw std::runtime_error("Oh singleton Box cache invalidation regression");
            SVFUtil::outs()<<"AE_OH_CACHE_CHECK Pass singleton-box-dense\n";
            return;
        }
    throw std::runtime_error("Oh cache regression found no nontrivial route");
}
