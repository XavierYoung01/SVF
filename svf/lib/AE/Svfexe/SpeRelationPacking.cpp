//===- SpeRelationPacking.cpp -- SPE-derived witness packs --------===//
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
#include "AE/Svfexe/StatementRelationPacking.h"
#include "AE/Svfexe/AllocationSize.h"
#include "AE/Svfexe/SVFIRAdapter.h"
#include "MemoryModel/PointerAnalysis.h"
#include "SVFIR/SVFIR.h"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <iterator>
#include <map>
#include <optional>
#include <set>
#include <vector>

namespace SVF
{
namespace
{
// An edge (i,j) denotes a finite upper bound on j - i. Coherence also
// requires (-j,-i). Diagonal entries are implicit.
using Signed = std::pair<Variable, bool>;
using Edge = std::pair<Signed, Signed>;
using Members = std::vector<Variable>;
using Witnesses = std::set<Members>;
using Facts = std::map<Edge, Witnesses>;
using Requirements = std::set<Edge>;
using Clock = std::chrono::steady_clock;

Signed opposite(Signed coordinate)
{
    coordinate.second = !coordinate.second;
    return coordinate;
}

Edge coherent(Edge edge)
{
    return {opposite(edge.second), opposite(edge.first)};
}

Edge canonical(Edge edge)
{
    return std::min(edge, coherent(edge));
}

Members mergeMembers(const Members& left, const Members& right)
{
    Members result;
    std::set_union(left.begin(), left.end(), right.begin(), right.end(),
                   std::back_inserter(result));
    return result;
}

Members endpoints(Edge edge)
{
    if (edge.first.first == edge.second.first)
        return {edge.first.first};
    return {std::min(edge.first.first, edge.second.first),
            std::max(edge.first.first, edge.second.first)};
}

struct LimitReached {};

struct Budget
{
    // Count work deterministically, including closure and witness products.
    std::size_t remaining;
    void use(std::size_t amount = 1)
    {
        if (amount > remaining)
            throw LimitReached{};
        remaining -= amount;
    }
};

void addCoherent(Facts& facts, Edge edge, const Members& witness)
{
    if (edge.first == edge.second)
        return;
    facts[edge].insert(witness);
    facts[coherent(edge)].insert(witness);
}

// Saturate newly finite edges. Coherence and unary bounds can add
// edges in either orientation. Keep witness alternatives already joined
// from separate predecessors.
void addFinite(Facts& facts, Edge edge, Budget& budget)
{
    if (edge.first == edge.second || facts.count(edge))
        return;
    std::deque<Edge> pending;
    const auto enqueue = [&](Edge added, Witnesses paths)
    {
        const auto insert = [&](Edge bound)
        {
            if (facts.emplace(bound, paths).second)
                pending.push_back(bound);
        };
        insert(added);
        insert(coherent(added));
    };
    enqueue(edge, {endpoints(edge)});
    while (!pending.empty())
    {
        const Edge added = pending.front();
        pending.pop_front();
        std::vector<Edge> before, after, unary;
        budget.use(facts.size());
        for (const auto& [bound, _] : facts)
        {
            if (bound.second == added.first)
                before.push_back(bound);
            if (bound.first == added.second)
                after.push_back(bound);
            if (opposite(added.first) == added.second &&
                    opposite(bound.first) == bound.second)
                unary.push_back(bound);
        }
        const auto compose = [&](Edge left, Edge right)
        {
            const Edge result{left.first, right.second};
            if (result.first == result.second || facts.count(result))
                return;
            Witnesses witnesses;
            for (const auto& a : facts.at(left))
                for (const auto& b : facts.at(right))
                {
                    budget.use();
                    witnesses.insert(mergeMembers(a, b));
                }
            enqueue(result, std::move(witnesses));
        };
        for (const auto& left : before)
            compose(left, added);
        for (const auto& right : after)
            compose(added, right);
        for (const auto& other : unary)
        {
            compose(added, other);
            compose(other, added);
        }
    }
}

struct Term
{
    enum Kind { Unknown, Constant, VariableOffset } kind = Unknown;
    std::optional<Signed> source;
    int shift = 0;  // Sign of the offset, used by Fig. 3 for self updates.
};

using Parallel = std::map<Variable, Term>;
struct Effect
{
    std::vector<Edge> guards;
    Parallel simultaneous;
    const std::set<Variable>* scopeExit = nullptr;
    const std::set<Variable>* clobberedContents = nullptr;
};

std::vector<Signed> images(Signed before, const Parallel& assignments,
                           const std::map<Signed, std::vector<Signed>>& from)
{
    std::vector<Signed> result;
    if (!assignments.count(before.first))
        result.push_back(before);
    if (const auto it = from.find(before); it != from.end())
        result.insert(result.end(), it->second.begin(), it->second.end());
    return result;
}

void assign(Facts& facts, const Parallel& assignments, Budget& budget)
{
    if (assignments.empty())
        return;
    Facts next;
    std::map<Signed, std::vector<Signed>> from;
    for (const auto& [target, term] : assignments)
        if (term.source)
        {
            from[*term.source].emplace_back(target, false);
            from[opposite(*term.source)].emplace_back(target, true);
        }
    const auto growingSide = [&](Signed end, bool upper)
    {
        if (const auto it = assignments.find(end.first); it != assignments.end())
        {
            const auto& term = it->second;
            if (term.source == Signed{end.first, false})
                return term.shift * (end.second ? -1 : 1) * (upper ? 1 : -1) > 0;
        }
        return false;
    };
    budget.use(facts.size());
    for (const auto& [bound, family] : facts)
        for (const auto& i : images(bound.first, assignments, from))
            for (const auto& j : images(bound.second, assignments, from))
            {
                if (growingSide(i, false) || growingSide(j, true))
                    continue;
                for (const auto& witness : family)
                {
                    budget.use();
                    addCoherent(next, {i, j}, mergeMembers(witness, endpoints({i, j})));
                }
            }
    for (const auto& [source, _] : from)
    {
        const auto copies = images(source, assignments, from);
        for (const auto& i : copies)
            for (const auto& j : copies)
                addFinite(next, {i, j}, budget);
    }
    for (const auto& [target, term] : assignments)
        if (term.kind == Term::Constant)
        {
            const Signed positive{target, false};
            addFinite(next, {positive, opposite(positive)}, budget);
            addFinite(next, {opposite(positive), positive}, budget);
        }
    facts = std::move(next);
}

void apply(Facts& facts, const Effect& effect, Budget& budget)
{
    if (effect.clobberedContents)
    {
        for (auto it = facts.begin(); it != facts.end();)
            if (effect.clobberedContents->count(it->first.first.first) ||
                    effect.clobberedContents->count(it->first.second.first))
                it = facts.erase(it);
            else
                ++it;
    }
    for (const auto edge : effect.guards)
        addFinite(facts, edge, budget);
    assign(facts, effect.simultaneous, budget);
    // A return kills facts about callee coordinates. Surviving facts can
    // still depend on those coordinates along their source-to-query paths.
    if (effect.scopeExit)
        for (auto it = facts.begin(); it != facts.end();)
        {
            const auto edge = it->first;
            if (effect.scopeExit->count(edge.first.first) || effect.scopeExit->count(edge.second.first))
                it = facts.erase(it);
            else
                ++it;
        }
}

bool join(std::optional<Facts>& old, Facts incoming, Budget& budget)
{
    if (!old)
    {
        old = std::move(incoming);
        return true;
    }
    bool changed = false;
    budget.use(old->size());
    for (auto it = old->begin(); it != old->end();)
        if (const auto found = incoming.find(it->first); found == incoming.end())
        {
            it = old->erase(it);
            changed = true;
        }
        else
        {
            budget.use(found->second.size());
            for (const auto& path : found->second)
                changed |= it->second.insert(path).second;
            ++it;
        }
    return changed;
}

struct Demand
{
    Requirements finite;
    bool impossible = false;
};

Demand backward(Demand after, const Effect& effect, Budget& budget)
{
    if (after.impossible)
        return after;
    Demand result;
    for (const auto required : after.finite)
    {
        budget.use();
        Edge need = required;
        bool known[2] = {false, false};
        Signed* ends[2] = {&need.first, &need.second};
        for (unsigned side = 0; side != 2; ++side)
        {
            auto& end = *ends[side];
            if (const auto found = effect.simultaneous.find(end.first);
                    found != effect.simultaneous.end())
            {
                const auto& term = found->second;
                if (term.source)
                    end = end.second ? opposite(*term.source) : *term.source;
                else if (term.kind == Term::Constant)
                    known[side] = true;
                else
                    return {{}, true};
            }
        }
        if (effect.clobberedContents &&
                (effect.clobberedContents->count(need.first.first) ||
                 effect.clobberedContents->count(need.second.first)))
            return {{}, true};
        if (known[0] && known[1])
            continue;
        if (known[0])
            need.first = opposite(need.second);
        if (known[1])
            need.second = opposite(need.first);
        if (need.first == need.second)
            continue;
        // The reversed assignment is followed by reversing the guard.
        for (Edge guard : effect.guards)
        {
            if (guard.second == need.second)
                need.second = guard.first;
            else if (guard.first == need.first)
                need.first = guard.second;
            else if (coherent(guard).second == need.second)
                need.second = coherent(guard).first;
            else if (coherent(guard).first == need.first)
                need.first = coherent(guard).second;
        }
        if (need.first != need.second)
            result.finite.insert(canonical(need));
    }
    return result;
}

const SVFStmt* definition(const SVFVar* value)
{
    if (!value)
        return nullptr;
    const SVFStmt* definition = nullptr;
    for (const auto* edge : value->getInEdges())
    {
        if (SVFUtil::isa<StoreStmt>(edge))
            continue;
        if (definition)
            return nullptr;
        definition = edge;
    }
    return definition;
}

template<class T>
const T* definedBy(const SVFVar* value)
{
    const auto* stmt = definition(value);
    return stmt ? SVFUtil::dyn_cast<T>(stmt) : nullptr;
}

struct Obligation
{
    const ICFGNode* point;
    Requirements required;
    bool extension;
    const char* reason = "unsupported-obligation";
    std::optional<Rational> indexLimit;
};

class SpePacking
{
public:
    SpePacking(SVFIR& ir, const SVFIRAdapter& adapter, PointerAnalysis& pointsTo,
               const AllocationSizeModel& sizes, const std::vector<Variable>& vocabulary)
        : ir_(ir), adapter_(adapter), pointsTo_(pointsTo), sizes_(sizes),
          permitted_(vocabulary.begin(), vocabulary.end()) {}

    RelationPacking construct(const std::vector<const ICFGNode*>& entries,
                              const std::vector<StatementPackingQuery>& queries);
private:
    std::optional<Variable> numeric(const SVFVar* value) const;
    std::optional<Variable> content(const ObjVar* object) const;
    Term operand(const SVFVar* value) const;
    Term expression(const BinaryOPStmt& stmt) const;
    std::set<const ObjVar*> pointees(const ValVar* pointer) const;
    std::optional<Requirements> comparison(const SVFVar* condition, bool taken) const;
    Obligation mapQuery(const StatementPackingQuery& query) const;
    Effect nodeEffect(const ICFGNode* node) const;
    void compilePhis();
    Effect edgeEffect(const ICFGEdge* edge) const;
    bool knownNoContentEffect(const CallICFGNode* call) const;

    SVFIR& ir_;
    const SVFIRAdapter& adapter_;
    PointerAnalysis& pointsTo_;
    const AllocationSizeModel& sizes_;
    std::set<Variable> permitted_;
    std::set<Variable> memory_;
    std::map<const FunObjVar*, std::set<Variable>> locals_;
    std::set<Variable> shared_;
    std::map<const ICFGNode*, Effect> nodes_;
    std::map<const ICFGEdge*, Effect> edges_;
    std::map<std::pair<const ICFGNode*, const ICFGNode*>, Parallel> phis_;
    std::map<const ICFGNode*, Parallel> phiFallbacks_;
};

std::optional<Variable> SpePacking::numeric(const SVFVar* value) const
{
    const auto* var = value ? SVFUtil::dyn_cast<ValVar>(value) : nullptr;
    if (!var || var->isPointer() || SVFUtil::isa<ConstDataValVar>(var) ||
            !adapter_.contains(*var))
        return std::nullopt;
    const auto mapped = adapter_.variable(*var);
    return permitted_.count(mapped) ? std::optional<Variable>(mapped) : std::nullopt;
}

std::optional<Variable> SpePacking::content(const ObjVar* object) const
{
    if (!object || object->isPointer())
        return std::nullopt;
    const auto mapped = adapter_.contentVariable(*object);
    return permitted_.count(mapped) ? std::optional<Variable>(mapped) : std::nullopt;
}

Term SpePacking::operand(const SVFVar* value) const
{
    if (value && SVFUtil::isa<ConstIntValVar>(value))
        return {Term::Constant, std::nullopt, 0};
    if (const auto var = numeric(value))
        return {Term::VariableOffset, Signed{*var, false}, 0};
    return {};
}

Term SpePacking::expression(const BinaryOPStmt& stmt) const
{
    const auto* lhs = stmt.getOpVar(0);
    const auto* rhs = stmt.getOpVar(1);
    const auto* left = SVFUtil::dyn_cast<ConstIntValVar>(lhs);
    const auto* right = SVFUtil::dyn_cast<ConstIntValVar>(rhs);
    if (left && right)
        return {Term::Constant, std::nullopt, 0};
    if (stmt.getOpcode() == BinaryOPStmt::Add || stmt.getOpcode() == BinaryOPStmt::Sub)
    {
        if (const auto* literal = left ? left : right)
        {
            Term term = operand(left ? rhs : lhs);
            if (!term.source)
                return {};
            term.shift = (literal->getSExtValue() > 0) - (literal->getSExtValue() < 0);
            if (stmt.getOpcode() == BinaryOPStmt::Sub && right)
                term.shift = -term.shift;
            if (stmt.getOpcode() == BinaryOPStmt::Sub && left)
                term.source = opposite(*term.source);
            return term;
        }
    }
    return {};
}

std::set<const ObjVar*> SpePacking::pointees(const ValVar* pointer) const
{
    std::set<const ObjVar*> objects;
    const auto& targets = pointsTo_.getPts(pointer->getId());
    if (targets.empty() || targets.test(IRGraph::BlackHole))
        return objects;
    for (NodeID id : targets)
        if (const auto* object = SVFUtil::dyn_cast<ObjVar>(ir_.getGNode(id)))
            objects.insert(object);
        else
            return {};
    return objects;
}

std::optional<Requirements> SpePacking::comparison(const SVFVar* condition, bool taken) const
{
    const auto* value = condition ? SVFUtil::dyn_cast<ValVar>(condition) : nullptr;
    const auto* cmp = value ? definedBy<CmpStmt>(SVFIRAdapter::booleanCondition(value, taken)) : nullptr;
    if (!cmp)
        return std::nullopt;
    const auto lhs = operand(cmp->getOpVar(0)), rhs = operand(cmp->getOpVar(1));
    if (lhs.kind == Term::Unknown || rhs.kind == Term::Unknown)
        return std::nullopt;
    bool reverse = false, equality = false;
    switch (cmp->getPredicate())
    {
    case CmpStmt::ICMP_SLT:
    case CmpStmt::ICMP_SLE: reverse = !taken; break;
    case CmpStmt::ICMP_SGT:
    case CmpStmt::ICMP_SGE: reverse = taken; break;
    case CmpStmt::ICMP_EQ: if (!taken) return std::nullopt; equality = true; break;
    case CmpStmt::ICMP_NE: if (taken) return std::nullopt; equality = true; break;
    default: return std::nullopt;
    }
    const auto makeEdge = [](const Term& left, const Term& right) -> std::optional<Edge>
    {
        if (left.source && right.source)
            return Edge{*right.source, *left.source};
        if (left.source)
            return Edge{opposite(*left.source), *left.source};
        if (right.source)
            return Edge{*right.source, opposite(*right.source)};
        return std::nullopt;
    };
    Requirements result;
    if (const auto edge = reverse ? makeEdge(rhs, lhs) : makeEdge(lhs, rhs))
        result.insert(canonical(*edge));
    if (equality)
        if (const auto edge = makeEdge(rhs, lhs))
            result.insert(canonical(*edge));
    return result;
}

Obligation SpePacking::mapQuery(const StatementPackingQuery& query) const
{
    Obligation result{query.node, {}, query.kind == "assert-condition" ||
        query.kind == "standard-assert-failure" || query.kind == "stub-bounds" ||
        query.kind == "gep-allocation-range", "unsupported-obligation", std::nullopt};
    if (query.kind == "assert-condition")
    {
        if (const auto requirement = comparison(query.operand, true))
            result.required = *requirement;
        result.reason = "unmodeled-assertion-predicate";
        return result;
    }
    if (query.kind == "standard-assert-failure")
    {
        result.reason = "unmodeled-error-control";
        std::set<const ICFGNode*> visited;
        const auto* node = query.node;
        while (visited.insert(node).second && node->getInEdges().size() == 1)
        {
            const auto* incoming = *node->getInEdges().begin();
            const auto* edge = SVFUtil::dyn_cast<IntraCFGEdge>(incoming);
            if (!edge || incoming->getSrcNode()->getFun() != query.node->getFun())
                break;
            node = incoming->getSrcNode();
            if (edge->getCondition() && !edge->isSwitchEdge())
            {
                if (const auto bounds = comparison(edge->getCondition(), edge->getSuccessorCondValue() == 0))
                {
                    result.point = node;
                    result.required = *bounds;
                }
                break;
            }
        }
        return result;
    }
    const auto* pointer = query.operand ? SVFUtil::dyn_cast<ValVar>(query.operand) : nullptr;
    if (!pointer || !pointer->isPointer())
        return result;
    const ValVar* index = nullptr;
    const GepStmt* gep = nullptr;
    s64_t bytes = 0;
    Rational offset(0);
    Rational width(0);
    if (query.statement &&
            (query.kind == "gep-allocation-range" || query.kind == "load-bounds" || query.kind == "store-bounds"))
    {
        gep = query.kind == "gep-allocation-range" ? SVFUtil::dyn_cast<GepStmt>(query.statement)
              : definedBy<GepStmt>(pointer);
        if (gep)
        {
            pointer = gep->getRHSVar();
            result.reason = "unmodeled-gep-index";
            for (const auto& [part, type] : gep->getOffsetVarAndGepTypePairVec())
            {
                if (!type)
                    return result;
                if (const auto* structure = SVFUtil::dyn_cast<SVFStructType>(type))
                {
                    offset += Rational(gep->getAccessPath().getStructFieldOffset(part, structure));
                    continue;
                }
                const auto* array = SVFUtil::dyn_cast<SVFArrayType>(type);
                if (!array && !SVFUtil::isa<SVFPointerType>(type))
                    return result;
                const s64_t stride = array ? array->getTypeOfElement()->getByteSize()
                                    : gep->getAccessPath().gepSrcPointeeType()->getByteSize();
                if (const auto* literal = SVFUtil::dyn_cast<ConstIntValVar>(part))
                    offset += Rational(literal->getSExtValue()) * Rational(stride);
                else if (!index)
                {
                    index = SVFUtil::dyn_cast<ValVar>(part);
                    if (!index)
                        return result;
                    bytes = stride;
                }
                else
                    return result;
            }
            if (query.kind != "gep-allocation-range")
            {
                if (query.statement->getAccessBytes() == 0)
                    return result;
                width = Rational(static_cast<s64_t>(query.statement->getAccessBytes()));
            }
        }
    }
    if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(query.node))
    {
        if (query.kind == "stub-bounds" && call->arg_size() >= 2)
        {
            index = call->getArgument(1);
            bytes = 1;
        }
        else if (const auto marker = query.kind.find("-len-"); marker != std::string::npos)
        {
            const auto ordinal = std::stoul(query.kind.substr(marker + 5));
            if (ordinal < call->arg_size())
                index = call->getArgument(ordinal);
            bytes = 1;
        }
    }
    const auto coordinate = numeric(index);
    const auto objects = pointees(pointer);
    if (!coordinate || bytes <= 0)
    {
        result.reason = "nonvariable-or-unsupported-index";
        return result;
    }
    if (objects.size() != 1)
    {
        result.reason = "ambiguous-base";
        return result;
    }
    const auto* base = ir_.getBaseObject((*objects.begin())->getId());
    const auto* size = base && base == *objects.begin() ? sizes_.find(base) : nullptr;
    if (size && size->known && size->elementBytes == bytes)
    {
        result.required.insert(canonical({{adapter_.sizeVariable(*base), false}, {*coordinate, false}}));
        result.indexLimit = ((Rational(0) - offset - width) / Rational(bytes)).floor();
    }
    else
        result.reason = "unmodeled-base-size-or-stride";
    return result;
}

bool SpePacking::knownNoContentEffect(const CallICFGNode* call) const
{
    const auto* function = call->getCalledFunction();
    if (!function)
        return false;
    const auto& name = function->getName();
    return name.rfind("__VERIFIER_nondet_", 0) == 0 ||
           name == "svf_assert" || name == "__VERIFIER_assume" || name == "llvm.assume" ||
           name == "rand" || name == "SAFE_BUFACCESS" || name == "UNSAFE_BUFACCESS" ||
           name == "SAFE_LOAD" || name == "UNSAFE_LOAD" ||
           name.rfind("llvm.dbg.", 0) == 0;
}

Effect SpePacking::nodeEffect(const ICFGNode* node) const
{
    Effect result;
    auto& writes = result.simultaneous;
    if (const auto found = phiFallbacks_.find(node); found != phiFallbacks_.end())
        writes = found->second;
    for (const auto* stmt : node->getSVFStmts())
    {
        if (const auto* bin = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
            if (const auto target = numeric(bin->getRes()))
                writes[*target] = expression(*bin);
        }
        else if (const auto* copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            if (const auto target = numeric(copy->getLHSVar()))
            {
                const auto kind = copy->getCopyKind();
                writes[*target] = kind == CopyStmt::COPYVAL || kind == CopyStmt::SEXT
                                  ? operand(copy->getRHSVar()) : Term{};
            }
        }
        else if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            if (const auto target = numeric(load->getLHSVar()))
            {
                const auto objects = pointees(load->getRHSVar());
                const auto source = objects.size() == 1 ? content(*objects.begin()) : std::nullopt;
                writes[*target] = source ? Term{Term::VariableOffset, Signed{*source, false}, 0} : Term{};
            }
        }
        else if (const auto* store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            const auto targets = pointees(store->getLHSVar());
            if (targets.empty())
                result.clobberedContents = &memory_;
            for (const auto* object : targets)
                if (const auto target = content(object))
                {
                    const auto* base = ir_.getBaseObject(object->getId());
                    const bool strong = targets.size() == 1 && base && !base->isHeap() &&
                                        !base->isConstDataOrConstGlobal() &&
                                        (base->isStack() || base->isGlobalObj());
                    writes[*target] = strong ? operand(store->getRHSVar()) : Term{};
                }
        }
        else if (const auto* addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            if (const auto* size = sizes_.find(addr))
            {
                const auto target = adapter_.sizeVariable(*size->object);
                if (!size->known)
                    writes[target] = {};
                else if (!size->sizeValue && !size->sizeSourcePointer)
                    writes[target] = {Term::Constant, std::nullopt, 0};
                else if (size->unitBytes == size->elementBytes && size->unitBytes != 0)
                    writes[target] = operand(size->sizeValue);
                else
                    writes[target] = {};
            }
        }
        else if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(stmt))
        {
            if (!SVFUtil::isa<PhiStmt>(stmt) && !SVFUtil::isa<CallPE>(stmt))
                if (const auto target = numeric(multi->getRes()))
                    writes[*target] = {};
        }
        else if (const auto* unary = SVFUtil::dyn_cast<UnaryOPStmt>(stmt))
        {
            if (const auto target = numeric(unary->getRes()))
                writes[*target] = {};
        }
    }
    if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(node))
    {
        const auto* callee = call->getCalledFunction();
        if (callee && (callee->getName() == "llvm.assume" || callee->getName() == "__VERIFIER_assume") &&
                call->arg_size() == 1)
            if (const auto guard = comparison(call->getArgument(0), true))
                result.guards.assign(guard->begin(), guard->end());
    }
    return result;
}

void SpePacking::compilePhis()
{
    ICFG* icfg = ir_.getICFG();
    for (const auto* statement : ir_.getSVFStmtSet(SVFStmt::Phi))
    {
        const auto* phi = SVFUtil::cast<PhiStmt>(statement);
        const auto target = numeric(phi->getRes());
        if (!target)
            continue;
        if (phi->isFunctionRetPhi())
        {
            for (u32_t index = 0; index < phi->getOpVarNum(); ++index)
                phiFallbacks_[phi->getOpICFGNode(index)][*target] = operand(phi->getOpVar(index));
            continue;
        }
        const auto* block = phi->getICFGNode()->getBB();
        const auto* first = block && !block->getICFGNodeList().empty()
                            ? block->getICFGNodeList().front() : phi->getICFGNode();
        std::vector<const ICFGNode*> predecessors;
        for (u32_t index = 0; index < phi->getOpVarNum(); ++index)
        {
            const auto* previous = phi->getOpICFGNode(index);
            if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(previous))
                previous = call->getRetICFGNode();
            if (!icfg->hasIntraICFGEdge(const_cast<ICFGNode*>(previous),
                                       const_cast<ICFGNode*>(first), ICFGEdge::IntraCF))
                break;
            predecessors.push_back(previous);
        }
        if (predecessors.size() != phi->getOpVarNum())
            phiFallbacks_[phi->getICFGNode()][*target] = {};
        else
            for (u32_t index = 0; index < phi->getOpVarNum(); ++index)
                phis_[{predecessors[index], first}][*target] = operand(phi->getOpVar(index));
    }
}

Effect SpePacking::edgeEffect(const ICFGEdge* edge) const
{
    Effect result;
    if (const auto* call = SVFUtil::dyn_cast<CallCFGEdge>(edge))
    {
        const auto* entry = SVFUtil::cast<FunEntryICFGNode>(call->getDstNode());
        const auto* site = call->getCallSite();
        const auto& formals = entry->getFormalParms();
        for (std::size_t index = 0; index < formals.size(); ++index)
            if (const auto target = numeric(formals[index]))
                result.simultaneous[*target] = index < site->arg_size()
                                               ? operand(site->getArgument(index)) : Term{};
    }
    else if (const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge))
    {
        if (const auto* binding = ret->getRetPE())
            if (const auto target = numeric(binding->getLHSVar()))
                result.simultaneous[*target] = operand(binding->getRHSVar());
        if (const auto locals = locals_.find(edge->getSrcNode()->getFun()); locals != locals_.end())
            result.scopeExit = &locals->second;
    }
    else if (const auto* intra = SVFUtil::dyn_cast<IntraCFGEdge>(edge))
    {
        if (intra->getCondition() && !intra->isSwitchEdge())
            if (const auto guard = comparison(intra->getCondition(), intra->getSuccessorCondValue() != 0))
                result.guards.assign(guard->begin(), guard->end());
        if (const auto found = phis_.find({edge->getSrcNode(), edge->getDstNode()}); found != phis_.end())
            result.simultaneous = found->second;
        if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(edge->getSrcNode()))
            if (const auto* ret = SVFUtil::dyn_cast<RetICFGNode>(edge->getDstNode());
                    ret && ret->getCallICFGNode() == call)
            {
                if (const auto returned = numeric(ret->getActualRet()))
                    result.simultaneous[*returned] = {};
                if (!knownNoContentEffect(call))
                    result.clobberedContents = &memory_;
            }
    }
    return result;
}

// A state in the preparation graph has a lexical ICFG point and a stack of
// call sites. RetCFG edges can only pop the call site that led to the callee.
struct Point
{
    const ICFGNode* node;
    std::vector<const CallICFGNode*> stack;
    bool operator<(const Point& other) const
    {
        return std::tie(node, stack) < std::tie(other.node, other.stack);
    }
};

struct Arc
{
    std::size_t from, to;
    const Effect* effect;
    const ICFGEdge* original;
};

struct MatchedGraph
{
    std::vector<Point> points;
    std::vector<Arc> arcs;
    std::vector<std::vector<std::size_t>> outgoing, incoming;
    std::vector<std::size_t> targets;
    bool recursive = false;
};

MatchedGraph matchCalls(const ICFGNode* root, const std::vector<const ICFGNode*>& entries,
                        const ICFGNode* query, const std::map<const ICFGEdge*, Effect>& effects,
                        Budget& budget)
{
    MatchedGraph result;
    std::set<const ICFGNode*> canReach;
    std::vector<const ICFGNode*> pending{query};
    while (!pending.empty())
    {
        const auto* node = pending.back();
        pending.pop_back();
        budget.use();
        if (canReach.insert(node).second)
            for (const auto* edge : node->getInEdges())
                pending.push_back(edge->getSrcNode());
    }
    std::map<Point, std::size_t> allocated;
    const auto add = [&](Point point)
    {
        const auto [it, fresh] = allocated.emplace(point, result.points.size());
        if (fresh)
        {
            budget.use();
            if (point.node == query)
                result.targets.push_back(it->second);
            result.points.push_back(std::move(point));
            result.outgoing.emplace_back();
            result.incoming.emplace_back();
        }
        return it->second;
    };
    const auto connect = [&](std::size_t from, Point to, const ICFGEdge* edge)
    {
        const auto index = add(std::move(to));
        result.outgoing[from].push_back(result.arcs.size());
        result.incoming[index].push_back(result.arcs.size());
        result.arcs.push_back({from, index, edge ? &effects.at(edge) : nullptr, edge});
    };
    add({root, {}});
    for (std::size_t index = 0; index < result.points.size(); ++index)
    {
        const auto current = result.points[index];
        const auto* node = current.node;
        if (node == root)
        {
            for (const auto* entry : entries)
                if (canReach.count(entry))
                    connect(index, {entry, {}}, nullptr);
            continue;
        }
        const auto* call = SVFUtil::dyn_cast<CallICFGNode>(node);
        const bool hasInternalCallee = call && std::any_of(node->getOutEdges().begin(),
                node->getOutEdges().end(), [](const auto* edge)
        {
            return SVFUtil::isa<CallCFGEdge>(edge) && !SVFUtil::isExtCall(edge->getDstNode()->getFun());
        });
        for (const auto* edge : node->getOutEdges())
        {
            budget.use();
            Point next{edge->getDstNode(), current.stack};
            if (!canReach.count(next.node))
                continue;
            if (const auto* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(edge))
            {
                const auto* callee = next.node->getFun();
                if (SVFUtil::isExtCall(callee))
                    continue;
                if (callee == node->getFun() || std::any_of(next.stack.begin(), next.stack.end(),
                        [&](const auto* active) { return active->getFun() == callee; }))
                {
                    result.recursive = true;
                    continue;
                }
                next.stack.push_back(callEdge->getCallSite());
            }
            else if (const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge))
            {
                if (next.stack.empty() || next.stack.back() != ret->getCallSite())
                    continue;
                next.stack.pop_back();
            }
            else if (hasInternalCallee && next.node == call->getRetICFGNode())
                continue;
            connect(index, std::move(next), edge);
        }
    }
    return result;
}

std::vector<Demand> inferInputs(const MatchedGraph& graph, const Requirements& root,
                                const std::map<const ICFGNode*, Effect>& effects,
                                Budget& budget)
{
    std::vector<Demand> demands(graph.points.size());
    std::deque<std::size_t> pending;
    std::vector<bool> queued(graph.points.size());
    for (auto target : graph.targets)
    {
        demands[target].finite = root;
        pending.push_back(target);
        queued[target] = true;
    }
    while (!pending.empty())
    {
        const auto index = pending.front();
        pending.pop_front();
        queued[index] = false;
        for (auto incoming : graph.incoming[index])
        {
            budget.use();
            const auto& arc = graph.arcs[incoming];
            auto need = arc.effect ? backward(demands[index], *arc.effect, budget) : demands[index];
            need = backward(std::move(need), effects.at(graph.points[arc.from].node), budget);
            auto& before = demands[arc.from];
            bool changed = need.impossible && !before.impossible;
            before.impossible |= need.impossible;
            for (auto edge : need.finite)
                changed |= before.finite.insert(edge).second;
            if (changed && !queued[arc.from])
            {
                queued[arc.from] = true;
                pending.push_back(arc.from);
            }
        }
    }
    return demands;
}

// A procedure has Top and at most one query-specific finite input class.
// The caller supplies the most precise class subsuming the bound state after
// parameter binding. Memoize the lexical solve for each such class. Caller
// SSA values survive separately and formal-to-actual substitution at the
// matching return instantiates the finite output relations.
class InputClassSolver
{
    using Entry = const FunEntryICFGNode*;
    using Key = std::pair<Entry, bool>;
    struct Summary
    {
        std::map<const ICFGNode*, std::optional<Facts>> points;
        Facts exit;
        bool returns = false;
        std::set<Variable> writes;
    };
    const std::map<const ICFGNode*, Effect>& nodes_;
    const std::map<const ICFGEdge*, Effect>& effects_;
    const std::map<const FunObjVar*, std::set<Variable>>& locals_;
    const std::set<Variable>& shared_;
    Budget& budget_;
    std::map<const ICFGNode*, std::set<const ICFGEdge*>> outgoing_;
    std::map<std::pair<const CallICFGNode*, const FunObjVar*>, const RetCFGEdge*> returns_;
    std::map<Entry, Requirements> selectors_;
    std::set<Entry> roots_;
    std::map<Key, Summary> summaries_;
    Facts global_;

    void recordWrites(const Effect& effect, Summary& summary) const
    {
        if (effect.clobberedContents)
            summary.writes.insert(effect.clobberedContents->begin(), effect.clobberedContents->end());
        for (const auto& [var, _] : effect.simultaneous)
            summary.writes.insert(var);
    }

    Key inputClass(const CallCFGEdge& call, const Facts& state)
    {
        auto bound = state;
        apply(bound, effects_.at(&call), budget_);
        const auto* entry = SVFUtil::cast<FunEntryICFGNode>(call.getDstNode());
        const auto found = selectors_.find(entry);
        const bool specific = found != selectors_.end() && !found->second.empty() &&
                              std::all_of(found->second.begin(), found->second.end(), [&](Edge edge)
        {
            return bound.count(edge) != 0;
        });
        return {entry, specific};
    }

    Facts instantiate(Facts caller, const Summary& callee, const CallCFGEdge& call,
                      const RetCFGEdge& ret)
    {
        const auto& bindings = effects_.at(&call).simultaneous;
        const auto& transfer = effects_.at(&ret).simultaneous;
        const auto scope = locals_.find(call.getDstNode()->getFun());
        const auto isLocal = [&](Variable coordinate)
        {
            return scope != locals_.end() && scope->second.count(coordinate) != 0;
        };
        Parallel forget;
        for (Variable coordinate : callee.writes)
            if (!isLocal(coordinate))
                forget[coordinate] = {};
        for (const auto& [target, _] : transfer)
            forget[target] = {};
        assign(caller, forget, budget_);
        std::map<Variable, Variable> returned;
        for (const auto& [target, term] : transfer)
            if (term.source)
                returned[term.source->first] = target;
        const auto substitute = [&](Signed end) -> std::optional<Signed>
        {
            if (const auto result = returned.find(end.first); result != returned.end())
                return Signed{result->second, end.second};
            if (const auto parameter = bindings.find(end.first); parameter != bindings.end())
                if (const auto actual = parameter->second.source)
                    return end.second ? opposite(*actual) : *actual;
            return isLocal(end.first) ? std::nullopt : std::optional<Signed>(end);
        };
        for (const auto& [bound, _] : callee.exit)
        {
            budget_.use();
            const auto from = substitute(bound.first), to = substitute(bound.second);
            if (from && to)
                addFinite(caller, {*from, *to}, budget_);
            else if (from || to)
            {
                const auto other = from ? bound.second.first : bound.first.first;
                if (const auto it = bindings.find(other); it != bindings.end() &&
                        it->second.kind == Term::Constant)
                {
                    if (from)
                        addFinite(caller, {*from, opposite(*from)}, budget_);
                    else
                        addFinite(caller, {opposite(*to), *to}, budget_);
                }
            }
        }
        return caller;
    }

    const Summary& summarize(Key key)
    {
        auto [slot, inserted] = summaries_.try_emplace(key);
        auto& result = slot->second;
        if (!inserted)
            return result;
        const auto [entry, specific] = key;
        Facts input = roots_.count(entry) ? global_ : Facts{};
        if (specific)
            for (auto edge : selectors_.at(entry))
                addFinite(input, edge, budget_);
        result.points[entry] = std::move(input);
        std::deque<const ICFGNode*> pending{entry};
        std::set<const ICFGNode*> inQueue{entry};
        const auto propagate = [&](const ICFGNode* to, Facts next)
        {
            // Provenance is recovered on the matched graph once the abstract
            // input-class solve accepts the query.
            for (auto& [edge, witnesses] : next)
                witnesses = {endpoints(edge)};
            if (join(result.points[to], std::move(next), budget_) && inQueue.insert(to).second)
                pending.push_back(to);
        };
        while (!pending.empty())
        {
            const auto* node = pending.front();
            pending.pop_front();
            inQueue.erase(node);
            budget_.use();
            auto after = *result.points.at(node);
            const auto& effect = nodes_.at(node);
            apply(after, effect, budget_);
            recordWrites(effect, result);
            if (SVFUtil::isa<FunExitICFGNode>(node))
            {
                result.returns = true;
                result.exit = std::move(after);
                continue;
            }
            const auto successors = outgoing_.find(node);
            if (successors == outgoing_.end())
                continue;
            for (const auto* edge : successors->second)
            {
                if (const auto* call = SVFUtil::dyn_cast<CallCFGEdge>(edge))
                {
                    const auto& callee = summarize(inputClass(*call, after));
                    result.writes.insert(callee.writes.begin(), callee.writes.end());
                    const auto ret = returns_.find({call->getCallSite(), edge->getDstNode()->getFun()});
                    if (callee.returns && ret != returns_.end())
                        propagate(ret->second->getDstNode(), instantiate(after, callee, *call, *ret->second));
                    continue;
                }
                auto next = after;
                const auto& edgeEffect = effects_.at(edge);
                apply(next, edgeEffect, budget_);
                recordWrites(edgeEffect, result);
                propagate(edge->getDstNode(), std::move(next));
            }
        }
        return result;
    }

public:
    InputClassSolver(const MatchedGraph& graph, const std::vector<Demand>& requirements,
             const std::map<const ICFGNode*, Effect>& nodes,
             const std::map<const ICFGEdge*, Effect>& effects,
             const std::map<const FunObjVar*, std::set<Variable>>& locals,
             const std::set<Variable>& shared, Budget& budget)
        : nodes_(nodes), effects_(effects), locals_(locals), shared_(shared), budget_(budget)
    {
        for (const auto& arc : graph.arcs)
        {
            if (!arc.original)
                roots_.insert(SVFUtil::cast<FunEntryICFGNode>(graph.points[arc.to].node));
            else if (const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(arc.original))
                returns_[{ret->getCallSite(), ret->getSrcNode()->getFun()}] = ret;
            else
                outgoing_[arc.original->getSrcNode()].insert(arc.original);
        }
        std::set<Entry> impossible;
        for (std::size_t index = 0; index < graph.points.size(); ++index)
            if (const auto* entry = SVFUtil::dyn_cast<FunEntryICFGNode>(graph.points[index].node))
            {
                const auto& need = requirements[index];
                if (need.impossible)
                {
                    impossible.insert(entry);
                    continue;
                }
                const auto frame = locals_.find(entry->getFun());
                const auto available = [&](Variable var)
                {
                    return shared_.count(var) || (frame != locals_.end() && frame->second.count(var));
                };
                for (auto edge : need.finite)
                    if (available(edge.first.first) && available(edge.second.first))
                        selectors_[entry].insert(edge);
            }
        for (const auto* entry : impossible)
            selectors_.erase(entry);
        apply(global_, nodes_.at(graph.points.front().node), budget_);
    }

    bool finiteAt(const ICFGNode* query, const Requirements& requirements, bool trace,
                  const std::string& identity)
    {
        std::vector<Key> pending;
        for (auto entry : roots_)
            pending.emplace_back(entry, false);
        std::set<Key> seen;
        bool reached = false;
        while (!pending.empty())
        {
            const auto key = pending.back();
            pending.pop_back();
            if (!seen.insert(key).second)
                continue;
            const auto& summary = summarize(key);
            if (trace)
            {
                std::cerr << "AE_SPE_FORWARD_CLASS query=" << identity
                          << " entry=" << key.first->getId() << " least=" << (key.second ? "finite" : "top");
                if (key.second)
                    for (const auto& [i,j] : selectors_.at(key.first))
                        std::cerr << ' ' << (i.second ? '-' : '+') << i.first.id()
                                  << ':' << (j.second ? '-' : '+') << j.first.id();
                std::cerr << '\n';
            }
            for (const auto& [node, input] : summary.points)
            {
                if (!input)
                    continue;
                if (node == query)
                {
                    reached = true;
                    for (const auto edge : requirements)
                        if (edge.first != edge.second && !input->count(edge))
                            return false;
                }
                if (const auto next = outgoing_.find(node); next != outgoing_.end())
                    for (const auto* edge : next->second)
                        if (const auto* call = SVFUtil::dyn_cast<CallCFGEdge>(edge))
                        {
                            auto after = *input;
                            apply(after, nodes_.at(node), budget_);
                            pending.push_back(inputClass(*call, after));
                        }
            }
        }
        return reached;
    }
};

std::vector<std::optional<Facts>> solve(const MatchedGraph& graph,
                                       const std::map<const ICFGNode*, Effect>& effects,
                                       Budget& budget)
{
    std::vector<std::optional<Facts>> states(graph.points.size());
    std::deque<std::size_t> pending{0};
    std::vector<bool> queued(graph.points.size());
    queued[0] = true;
    states[0].emplace();
    const bool trace = std::getenv("SVF_AE_TRACE_SPE_STATES") != nullptr;
    while (!pending.empty())
    {
        const auto index = pending.front();
        pending.pop_front();
        queued[index] = false;
        budget.use();
        auto after = *states[index];
        apply(after, effects.at(graph.points[index].node), budget);
        for (auto outgoing : graph.outgoing[index])
        {
            const auto& arc = graph.arcs[outgoing];
            auto next = after;
            if (arc.effect)
                apply(next, *arc.effect, budget);
            if (trace)
            {
                std::cerr << "AE_SPE_STATE " << graph.points[index].node->getId()
                          << "->" << graph.points[arc.to].node->getId()
                          << " stack=" << graph.points[index].stack.size()
                          << " guards=" << (arc.effect ? arc.effect->guards.size() : 0)
                          << " bindings=" << (arc.effect ? arc.effect->simultaneous.size() : 0)
                          << " node_writes=" << effects.at(graph.points[index].node).simultaneous.size();
                for (const auto& [edge, _] : next)
                    if (!edge.first.second && !edge.second.second)
                        std::cerr << ' ' << edge.first.first.id() << '>' << edge.second.first.id();
                std::cerr << '\n';
            }
            if (join(states[arc.to], std::move(next), budget) && !queued[arc.to])
            {
                pending.push_back(arc.to);
                queued[arc.to] = true;
            }
        }
    }
    return states;
}

RelationPacking SpePacking::construct(const std::vector<const ICFGNode*>& entries,
                                       const std::vector<StatementPackingQuery>& queries)
{
    const auto start = Clock::now();
    const bool trace = std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY") != nullptr;
    for (Variable variable : permitted_)
    {
        if (const auto* value = adapter_.value(variable))
        {
            if (value->getFunction())
                locals_[value->getFunction()].insert(variable);
        }
        else if (const auto* object = adapter_.contentObject(variable))
        {
            memory_.insert(variable);
            if (const auto* base = ir_.getBaseObject(object->getId()); base && base->isStack())
                locals_[base->getFunction()].insert(variable);
            else
                shared_.insert(variable);
        }
        else if (const auto* object = adapter_.sizeObject(variable))
        {
            const auto* base = ir_.getBaseObject(object->getId());
            if (base && base->isStack())
                locals_[base->getFunction()].insert(variable);
            else
                shared_.insert(variable);
        }
    }
    compilePhis();
    const ICFG* icfg = ir_.getICFG();
    for (auto it = icfg->begin(); it != icfg->end(); ++it)
    {
        const auto* node = it->second;
        nodes_.emplace(node, nodeEffect(node));
        for (const auto* edge : node->getOutEdges())
            edges_.emplace(edge, edgeEffect(edge));
    }

    const double compilationSeconds = std::chrono::duration<double>(Clock::now() - start).count();
    double backwardSeconds = 0, forwardSeconds = 0, extractionSeconds = 0;
    std::size_t promising = 0, native = 0, extensions = 0, skipped = 0, unsupported = 0;
    Budget total{10000000};
    Witnesses unique;
    for (const auto& query : queries)
    {
        const auto obligation = mapQuery(query);
        const auto report = [&](const char* reason)
        {
            if (trace)
                std::cerr << "AE_SPE_QUERY " << query.identity << ' ' << reason
                          << " mapping=" << (obligation.extension ? "svf-extension" : "buffer-upper")
                          << " kind=" << query.kind;
            if (trace && obligation.indexLimit)
                std::cerr << " limit=" << obligation.indexLimit->toString();
            if (trace)
                std::cerr << '\n';
        };
        if (obligation.required.empty())
        {
            ++unsupported;
            report(obligation.reason);
            continue;
        }
        if (obligation.extension)
            ++extensions;
        else
            ++native;
        constexpr std::size_t queryBudget = 250000;
        Budget budget{std::min(queryBudget, total.remaining)};
        const auto initial = budget.remaining;
        auto phase = Clock::now();
        double* active = &backwardSeconds;
        const auto transition = [&](double* next)
        {
            const auto now = Clock::now();
            *active += std::chrono::duration<double>(now - phase).count();
            phase = now;
            active = next;
        };
        try
        {
            const auto graph = matchCalls(icfg->getGlobalICFGNode(), entries, obligation.point, edges_, budget);
            if (graph.recursive || graph.targets.empty())
            {
                ++skipped;
                report(graph.recursive ? "recursive-slice" : "no-matched-path");
            }
            else
            {
                const auto need = inferInputs(graph, obligation.required, nodes_, budget);
                if (trace)
                    for (std::size_t index = 0; index < graph.points.size(); ++index)
                        if (SVFUtil::isa<FunEntryICFGNode>(graph.points[index].node) &&
                                (need[index].impossible || !need[index].finite.empty()))
                        {
                            std::cerr << "AE_SPE_INPUT_CLASS query=" << query.identity
                                      << " entry=" << graph.points[index].node->getId()
                                      << " impossible=" << need[index].impossible;
                            for (const auto& [i, j] : need[index].finite)
                                std::cerr << ' ' << (i.second ? '-' : '+') << i.first.id() << ':'
                                          << (j.second ? '-' : '+') << j.first.id();
                            std::cerr << '\n';
                        }
                transition(&forwardSeconds);
                InputClassSolver summaries(graph, need, nodes_, edges_, locals_, shared_, budget);
                if (!summaries.finiteAt(obligation.point, obligation.required, trace, query.identity))
                    report("class-top");
                else
                {
                    transition(&extractionSeconds);
                    const auto states = solve(graph, nodes_, budget);
                    bool finite = true;
                    Witnesses witnesses;
                    for (auto index : graph.targets)
                        for (auto bound : obligation.required)
                        {
                            if (bound.first == bound.second)
                                continue;
                            const auto& state = states[index];
                            if (!state)
                                continue;
                            const auto found = state->find(bound);
                            if (found == state->end())
                            {
                                finite = false;
                                break;
                            }
                            for (const auto& path : found->second)
                            {
                                budget.use();
                                witnesses.insert(path);
                            }
                        }
                    if (finite && !witnesses.empty())
                    {
                        ++promising;
                        report("finite");
                        if (trace)
                            for (const auto& witness : witnesses)
                            {
                                std::cerr << "AE_SPE_WITNESS " << query.identity;
                                for (auto variable : witness)
                                    std::cerr << ' ' << variable.id();
                                std::cerr << '\n';
                            }
                        unique.insert(witnesses.begin(), witnesses.end());
                    }
                    else
                        report("top");
                }
            }
        }
        catch (const LimitReached&)
        {
            ++skipped;
            report(initial < queryBudget ? "campaign-budget" : "query-budget");
        }
        *active += std::chrono::duration<double>(Clock::now() - phase).count();
        total.use(initial - budget.remaining);
    }
    auto uncovered = permitted_;
    for (const auto& pack : unique)
        for (auto variable : pack)
            uncovered.erase(variable);
    for (auto variable : uncovered)
        unique.insert({variable});

    SVFUtil::outs() << "AE_SPE_PACK packs=" << unique.size() << " native=" << native
                   << " extensions=" << extensions << " promising=" << promising
                   << " unsupported=" << unsupported << " skipped=" << skipped
                   << " compile_s=" << compilationSeconds << " backward_s=" << backwardSeconds
                   << " forward_s=" << forwardSeconds << " extraction_s=" << extractionSeconds
                   << " contexts=query-input-classes+matched-provenance\n";
    return {unique.begin(), unique.end()};
}
}

RelationPacking StatementRelationPacking::packSpe(const std::vector<Variable>& vocabulary,
        const std::vector<const ICFGNode*>& entries,
        const std::vector<StatementPackingQuery>& queries) const
{
    return SpePacking(ir_, adapter_, pointsTo_, *sizes_, vocabulary).construct(entries, queries);
}
}
