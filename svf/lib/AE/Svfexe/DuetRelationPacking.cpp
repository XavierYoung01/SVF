//===- DuetRelationPacking.cpp -- DUET variable packing --------===//
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
#include "AE/Svfexe/SVFIRAdapter.h"
#include "MemoryModel/PointerAnalysis.h"
#include "SVFIR/SVFIR.h"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <vector>

namespace SVF
{
namespace
{
enum class Scope { Local, Global, Unknown };

struct Event
{
    std::map<Variable, Scope> variables;
    bool resolved = true;
};

// Only follow address uses that leave the stack address within the function.
bool isNonescapingStack(const BaseObjVar& base)
{
    std::vector<const SVFVar*> pending{&base};
    std::set<const SVFVar*> seen;
    while (!pending.empty())
    {
        const SVFVar* variable = pending.back();
        pending.pop_back();
        if (!seen.insert(variable).second)
            continue;
        for (const auto* use : variable->getOutEdges())
        {
            if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(use))
            {
                if (load->getRHSVar() == variable)
                    continue;
            }
            if (const auto* store = SVFUtil::dyn_cast<StoreStmt>(use))
            {
                if (store->getLHSVar() == variable && store->getRHSVar() != variable)
                    continue;
            }
            if (const auto* assignment = SVFUtil::dyn_cast<AssignStmt>(use))
                if (assignment->getRHSVar() == variable &&
                        assignment->getLHSVar()->isPointer() &&
                        assignment->getLHSVar()->getFunction() == base.getFunction() &&
                        (SVFUtil::isa<AddrStmt>(use) || SVFUtil::isa<GepStmt>(use) ||
                         SVFUtil::isa<CopyStmt>(use)))
                {
                    pending.push_back(assignment->getLHSVar());
                    continue;
                }
            return false;
        }
    }
    return true;
}
}

RelationPacking StatementRelationPacking::packDuet(const std::vector<Variable>& vocabulary) const
{
    const std::set<Variable> permitted(vocabulary.begin(), vocabulary.end());
    const bool trace = std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY") != nullptr;
    std::vector<RelationEdge> edges;
    std::map<const BaseObjVar*, Scope> objectScopes;
    unsigned events = 0, merged = 0;
    const auto addValue = [&](Event& event, const SVFVar* variable)
    {
        if (variable && SVFUtil::isa<ConstDataValVar>(variable))
            return;
        const auto* value = SVFUtil::dyn_cast<ValVar>(variable);
        if (!value || value->isPointer() || !adapter_.contains(*value))
        {
            event.resolved = false;
            return;
        }
        const auto coordinate = adapter_.variable(*value);
        if (permitted.count(coordinate))
            event.variables.emplace(coordinate, value->getFunction() ? Scope::Local : Scope::Unknown);
        else
            event.resolved = false;
    };
    const auto addContents = [&](Event& event, const ValVar* address)
    {
        const auto& targets = pointsTo_.getPts(address->getId());
        if (targets.empty() || targets.test(IRGraph::BlackHole))
            event.resolved = false;
        for (NodeID id : targets)
        {
            const auto* object = SVFUtil::dyn_cast<ObjVar>(ir_.getGNode(id));
            const auto* base = ir_.getBaseObject(id);
            if (!object || !base || id == IRGraph::BlackHole || object->isPointer() ||
                    base->isConstDataOrConstGlobal() ||
                    !permitted.count(adapter_.contentVariable(*object)))
            {
                event.resolved = false;
                continue;
            }
            const auto [it, inserted] = objectScopes.try_emplace(base, Scope::Unknown);
            if (inserted)
            {
                if (base->isGlobalObj())
                    it->second = Scope::Global;
                else if (base->isStack() && isNonescapingStack(*base))
                    it->second = Scope::Local;
            }
            event.variables.emplace(adapter_.contentVariable(*object), it->second);
        }
    };
    const auto submit = [&](const Event& event, bool assume, unsigned site,
                            const char* kind, const ICFGNode* predecessor = nullptr)
    {
        ++events;
        const auto& variables = event.variables;
        const bool eligible = event.resolved && !variables.empty() &&
                              (assume || variables.size() == 2) &&
                              variables.begin()->second != Scope::Unknown &&
                              std::all_of(variables.begin(), variables.end(), [&](const auto& member)
        {
            return member.second == variables.begin()->second;
        });
        if (eligible && variables.size() > 1)
        {
            ++merged;
            for (auto it = std::next(variables.begin()); it != variables.end(); ++it)
                edges.emplace_back(variables.begin()->first, it->first);
        }
        if (trace)
        {
            std::cerr << "AE_DUET_EVENT kind=" << kind << " site=" << site
                      << " resolved=" << event.resolved << " eligible=" << eligible;
            if (predecessor)
                std::cerr << " predecessor=" << predecessor->getId();
            for (const auto& [variable, scope] : variables)
                std::cerr << ' ' << variable.id() << ':' << static_cast<unsigned>(scope);
            std::cerr << '\n';
        }
    };
    const auto collectGuard = [&](const ValVar* guard)
    {
        Event event;
        std::set<const ValVar*> seen;
        std::vector<const ValVar*> pending{guard};
        while (!pending.empty())
        {
            const auto* value = pending.back();
            pending.pop_back();
            if (!seen.insert(value).second)
                continue;
            bool expanded = false;
            for (const auto* definition : value->getInEdges())
            {
                if (const auto* cmp = SVFUtil::dyn_cast<CmpStmt>(definition))
                {
                    for (const auto* operand : cmp->getOpndVars())
                        addValue(event, operand);
                    expanded = true;
                }
                const auto* type = value->getType() ? SVFUtil::dyn_cast<SVFIntegerType>(value->getType()) : nullptr;
                if (const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(definition))
                    if (type && type->isBoolean() &&
                            (binary->getOpcode() == BinaryOPStmt::And ||
                             binary->getOpcode() == BinaryOPStmt::Or ||
                             binary->getOpcode() == BinaryOPStmt::Xor))
                    {
                        for (const auto* operand : binary->getOpndVars())
                            pending.push_back(operand);
                        expanded = true;
                    }
            }
            if (!expanded)
                addValue(event, value);
        }
        return event;
    };

    std::vector<const SVFStmt*> statements;
    for (auto kind : {SVFStmt::BinaryOp, SVFStmt::UnaryOp, SVFStmt::Copy, SVFStmt::Phi,
                      SVFStmt::Select, SVFStmt::Call, SVFStmt::Ret, SVFStmt::Load,
                      SVFStmt::Store, SVFStmt::Branch})
    {
        const auto& group = ir_.getSVFStmtSet(kind);
        statements.insert(statements.end(), group.begin(), group.end());
    }
    std::sort(statements.begin(), statements.end(), [](const auto* a, const auto* b)
    {
        return a->getEdgeID() < b->getEdgeID();
    });
    for (const auto* statement : statements)
    {
        const auto id = statement->getEdgeID();
        Event event;
        const char* kind = "assignment";
        if (const auto* branch = SVFUtil::dyn_cast<BranchStmt>(statement))
        {
            if (branch->isConditional())
                submit(collectGuard(branch->getCondition()), true, id, "branch-assume");
            continue;
        }
        if (const auto* call = SVFUtil::dyn_cast<CallPE>(statement))
        {
            for (u32_t index = 0; index < call->getOpVarNum(); ++index)
            {
                Event binding;
                addValue(binding, call->getRes());
                addValue(binding, call->getOpVar(index));
                submit(binding, false, id, "call-binding", call->getOpCallICFGNode(index));
            }
            continue;
        }
        if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(statement))
        {
            for (u32_t index = 0; index < phi->getOpVarNum(); ++index)
            {
                Event copy;
                addValue(copy, phi->getRes());
                addValue(copy, phi->getOpVar(index));
                submit(copy, false, id, "phi-copy", phi->getOpICFGNode(index));
            }
            continue;
        }
        if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(statement))
        {
            addValue(event, load->getLHSVar());
            addContents(event, load->getRHSVar());
            kind = "load";
        }
        else if (const auto* store = SVFUtil::dyn_cast<StoreStmt>(statement))
        {
            addContents(event, store->getLHSVar());
            const auto* rhs = store->getRHSVar();
            const auto& definitions = rhs->getInEdges();
            const auto* load = definitions.size() == 1
                               ? SVFUtil::dyn_cast<LoadStmt>(*definitions.begin()) : nullptr;
            const auto* loadNode = load ? load->getICFGNode() : nullptr;
            // Preserve a source-level content-to-content copy when the two
            // instructions are adjacent and the load has no other successor.
            if (loadNode && loadNode->getOutEdges().size() == 1 &&
                    (*loadNode->getOutEdges().begin())->getDstNode() == store->getICFGNode())
            {
                addContents(event, load->getRHSVar());
                kind = "content-copy";
            }
            else
            {
                addValue(event, rhs);
                kind = "store";
            }
        }
        else if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(statement))
        {
            addValue(event, multi->getRes());
            for (const auto* operand : multi->getOpndVars())
                addValue(event, operand);
            if (const auto* select = SVFUtil::dyn_cast<SelectStmt>(statement))
                addValue(event, select->getCondition());
        }
        else if (const auto* unary = SVFUtil::dyn_cast<UnaryOPStmt>(statement))
        {
            addValue(event, unary->getRes());
            addValue(event, unary->getOpVar());
        }
        else if (const auto* assign = SVFUtil::dyn_cast<AssignStmt>(statement))
        {
            addValue(event, assign->getLHSVar());
            addValue(event, assign->getRHSVar());
            if (SVFUtil::isa<RetPE>(statement))
                kind = "return-binding";
        }
        submit(event, false, id, kind);
    }
    for (auto it = ir_.getICFG()->begin(); it != ir_.getICFG()->end(); ++it)
        if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(it->second))
            if (const auto* function = call->getCalledFunction(); function && call->arg_size() == 1)
                if (function->getName() == "llvm.assume" || function->getName() == "__VERIFIER_assume")
                    submit(collectGuard(call->getArgument(0)), true, call->getId(), "explicit-assume");

    auto packs = connectedComponentPacking(vocabulary, edges);
    SVFUtil::outs() << "AE_DUET_PACK packs=" << packs.size() << " events=" << events
                   << " eligible_merges=" << merged << '\n';
    return packs;
}
}
