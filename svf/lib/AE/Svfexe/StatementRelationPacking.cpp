//===- StatementRelationPacking.cpp -- Statement Relation Packing --------===//
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
#include "AE/Svfexe/AbstractInterpretation.h"
#include "AE/Svfexe/SVFIRAdapter.h"
#include "AE/Svfexe/AllocationSize.h"
#include "AE/Svfexe/PackSSA.h"
#include "MemoryModel/PointerAnalysis.h"
#include "SVFIR/SVFIR.h"
#include "Util/Options.h"
#include <algorithm>
#include <functional>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>

namespace SVF
{

StatementPackingResult StatementRelationPacking::pack(
    const std::vector<SVF::Variable>& vocabulary,
    bool differencesOnly, bool queryComponents) const
{
    const std::set<SVF::Variable> permitted(vocabulary.begin(), vocabulary.end());
    StatementPackingResult result;
    std::vector<SVF::RelationEdge> edges;
    const bool traceRoots = std::getenv("SVF_AE_TRACE_ROOT_REASONS") != nullptr;
    std::map<SVF::Variable, std::set<std::string>> rootReasons;
    const auto recordRoot = [&](SVF::Variable variable, const char* reason)
    {
        result.queries.push_back(variable);
        if (traceRoots) rootReasons[variable].insert(reason);
    };
    const auto numeric = [&](const SVFVar* variable) -> std::optional<SVF::Variable>
    {
        const auto* value = SVFUtil::dyn_cast<ValVar>(variable);
        if (!value || value->isPointer() || !adapter_.contains(*value))
            return std::nullopt;
        const auto mapped = adapter_.variable(*value);
        if (mapped.type().kind == SVF::NumericKind::IEEEFloat ||
                permitted.count(mapped) == 0)
            return std::nullopt;
        return mapped;
    };
    const auto add = [&](std::optional<SVF::Variable> left,
                         std::optional<SVF::Variable> right,
                         const SVFStmt* statement, const char* kind)
    {
        if (queryComponents && (std::string(kind) == "index" || std::string(kind) == "length"))
        {
            if (left)
                recordRoot(*left, "query");
            if (right)
                recordRoot(*right, "query");
        }
        if (!left || !right || *left == *right)
            return;
        SVF::RelationEdge edge{std::min(*left, *right), std::max(*left, *right)};
        edges.push_back(edge);
        result.edges.push_back({edge, statement->getEdgeID(), kind});
    };
    const auto contentEdges = [&](const ValVar* pointer,
                                  const SVFVar* value,
                                  const SVFStmt* statement, const char* kind)
    {
        const auto scalar = numeric(value);
        if (!scalar)
            return;
        for (NodeID id : pointsTo_.getPts(pointer->getId()))
        {
            const auto* object = SVFUtil::dyn_cast<ObjVar>(ir_.getGNode(id));
            if (!object || object->isPointer())
                continue;
            const auto content = adapter_.contentVariable(*object);
            if (content.type().kind != SVF::NumericKind::IEEEFloat &&
                    permitted.count(content) != 0)
                add(scalar, content, statement, kind);
        }
    };
    std::vector<const SVFStmt*> statements;
    for (auto kind :
            {
                SVFStmt::BinaryOp, SVFStmt::UnaryOp, SVFStmt::Cmp,
                SVFStmt::Copy, SVFStmt::Phi, SVFStmt::Select,
                SVFStmt::Call, SVFStmt::Ret, SVFStmt::Load, SVFStmt::Store
            })
    {
        const auto& set = ir_.getSVFStmtSet(kind);
        statements.insert(statements.end(), set.begin(), set.end());
    }
    std::sort(statements.begin(), statements.end(),
              [](const SVFStmt* a, const SVFStmt* b)
    {
        return a->getEdgeID() < b->getEdgeID();
    });
    for (const auto* statement : statements)
    {
        if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(statement))
            contentEdges(load->getRHSVar(), load->getLHSVar(), statement, "load");
        else if (const auto* store = SVFUtil::dyn_cast<StoreStmt>(statement))
            contentEdges(store->getLHSVar(), store->getRHSVar(), statement, "store");
        else if (const auto* cmp = SVFUtil::dyn_cast<CmpStmt>(statement))
            // The Boolean result is not an affine partner of either operand.
            add(numeric(cmp->getOpVar(0)), numeric(cmp->getOpVar(1)), statement, "cmp");
        else if (const auto* unary = SVFUtil::dyn_cast<UnaryOPStmt>(statement))
        {
            if (differencesOnly)
                continue;
            add(numeric(unary->getRes()), numeric(unary->getOpVar()), statement, "unary");
        }
        else if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(statement))
        {
            if (differencesOnly)
                if (const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(statement))
                {
                    const bool leftConstant = SVFUtil::isa<ConstIntValVar>(binary->getOpVar(0));
                    const bool rightConstant = SVFUtil::isa<ConstIntValVar>(binary->getOpVar(1));
                    const bool affineCopy = (binary->getOpcode() == BinaryOPStmt::Add &&
                                             leftConstant != rightConstant) ||
                                            (binary->getOpcode() == BinaryOPStmt::Sub && rightConstant);
                    const bool difference = binary->getOpcode() == BinaryOPStmt::Sub &&
                                            !leftConstant && !rightConstant;
                    if (!affineCopy && !difference)
                        continue;
                }
            const char* kind = SVFUtil::isa<BinaryOPStmt>(statement) ? "binary" :
                               SVFUtil::isa<PhiStmt>(statement) ? "phi" :
                               SVFUtil::isa<SelectStmt>(statement) ? "select" : "call";
            for (const auto* operand : multi->getOpndVars())
                add(numeric(multi->getRes()), numeric(operand), statement, kind);
        }
        else if (const auto* assign = SVFUtil::dyn_cast<AssignStmt>(statement))
            add(numeric(assign->getLHSVar()), numeric(assign->getRHSVar()), statement,
                SVFUtil::isa<RetPE>(statement) ? "ret" : "copy");
    }
    // Loop-carried values share an iteration schedule. Keep their header
    // tuple together so counter bounds can constrain the evolving data.
    std::map<const SVFBasicBlock*, const PhiStmt*> loopPhis;
    for (const SVFStmt* statement : statements)
        if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(statement))
        {
            const auto* node = phi->getICFGNode();
            const auto* block = node->getBB();
            if (phi->isFunctionRetPhi() || !block || !node->getFun() ||
                    !node->getFun()->isLoopHeader(block) || !numeric(phi->getRes()))
                continue;
            const auto inserted = loopPhis.emplace(block, phi);
            if (!inserted.second)
                add(numeric(phi->getRes()), numeric(inserted.first->second->getRes()),
                    phi, "loop-phi");
        }
    if (sizes_)
    {
        // D-005: Size(o) := allocated count, and every variable array index
        // is compared against the Size(o) of its possible base objects.
        const auto sizeOf = [&](const BaseObjVar* object) -> std::optional<SVF::Variable>
        {
            const AllocationSize* size = object ? sizes_->find(object) : nullptr;
            if (!size)
                return std::nullopt;
            const auto variable = adapter_.sizeVariable(*size->object);
            return permitted.count(variable) ? std::optional<SVF::Variable>(variable)
                            : std::nullopt;
        };
        for (const auto& size : sizes_->all())
            if (size.sizeValue)
                add(sizeOf(size.object), numeric(size.operand ? size.operand : size.sizeValue),
                    size.site, "size");
        for (const SVFStmt* statement : ir_.getSVFStmtSet(SVFStmt::Gep))
        {
            const auto* gep = SVFUtil::cast<GepStmt>(statement);
            if (gep->isConstantOffset())
                continue;
            std::set<const BaseObjVar*> bases;
            for (NodeID id : pointsTo_.getPts(gep->getRHSVarID()))
                if (const auto* base = ir_.getBaseObject(id))
                    bases.insert(base);
            for (const auto& part : gep->getOffsetVarAndGepTypePairVec())
                if (!SVFUtil::isa<ConstIntValVar>(part.first))
                    for (const auto* base : bases)
                        add(numeric(part.first), sizeOf(base), statement, "index");
        }
        for (auto it = ir_.getICFG()->begin(); it != ir_.getICFG()->end(); ++it)
        {
            const auto* call = SVFUtil::dyn_cast<CallICFGNode>(it->second);
            const auto* function = call ? call->getCalledFunction() : nullptr;
            if (!function || call->arg_size() < 3)
                continue;
            const auto& name = function->getName();
            if (name != "memcpy" && name != "memmove" && name != "strncpy" &&
                    name != "__memcpy_chk" && name != "__memmove_chk" &&
                    name.rfind("llvm.memcpy.", 0) != 0 && name.rfind("llvm.memmove.", 0) != 0 &&
                    name.rfind("llvm_memcpy", 0) != 0 && name.rfind("llvm_memmove", 0) != 0)
                continue;
            for (unsigned argument :
                    {
                        0u, 1u
                    })
                for (NodeID id : pointsTo_.getPts(call->getArgument(argument)->getId()))
                    if (const auto* base = ir_.getBaseObject(id))
                        if (const auto* size = sizes_->find(base))
                            add(numeric(call->getArgument(2)), sizeOf(base), size->site, "length");
        }
    }
    result.packs = SVF::connectedComponentPacking(vocabulary, edges);
    if (queryComponents)
    {
        const auto queryVariable = [&](const SVFVar* value, const char* reason = "query")
        {
            if (!SVFUtil::isa<ConstIntValVar>(value))
                if (const auto variable = numeric(value))
                    recordRoot(*variable, reason);
        };
        const auto assertion = [&](const SVFVar* condition, const char* reason = "query")
        {
            std::vector<const SVFVar*> pending{condition};
            std::set<const SVFVar*> seen;
            while (!pending.empty())
            {
                bool taken = true;
                const auto* value = SVFIRAdapter::booleanCondition(pending.back(), taken);
                pending.pop_back();
                if (!value || !seen.insert(value).second)
                    continue;
                queryVariable(value, reason);
                for (const SVFStmt* def : value->getInEdges())
                {
                    if (const auto* cmp = SVFUtil::dyn_cast<CmpStmt>(def))
                    {
                        queryVariable(cmp->getOpVar(0), reason);
                        queryVariable(cmp->getOpVar(1), reason);
                    }
                    else if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(def))
                    {
                        const auto* type = SVFUtil::dyn_cast<SVFIntegerType>(value->getType());
                        const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(multi);
                        if (type && type->isBoolean() &&
                                (SVFUtil::isa<PhiStmt>(multi) || SVFUtil::isa<SelectStmt>(multi) ||
                                 (binary && (binary->getOpcode() == BinaryOPStmt::And ||
                                             binary->getOpcode() == BinaryOPStmt::Or))))
                            for (const auto* operand : multi->getOpndVars())
                                pending.push_back(operand);
                    }
                }
            }
        };
        if (Options::AESVComp() || std::getenv("SVF_IMPACT_ASSERT_QUERIES"))
            for (auto it = ir_.getICFG()->begin(); it != ir_.getICFG()->end(); ++it)
            {
                const auto* call = SVFUtil::dyn_cast<CallICFGNode>(it->second);
                const auto* function = call ? call->getCalledFunction() : nullptr;
                if (!function)
                    continue;
                const auto& name = function->getName();
                if (name == "svf_assert" && call->arg_size())
                    assertion(call->getArgument(0));
                else if (name == "__assert_fail" || name == "__assert_rtn" ||
                         name == "__assert_func" || name == "__assert2" ||
                         (Options::AESVComp() && (name == "reach_error" || name == "__VERIFIER_error")))
                {
                    std::vector<const ICFGNode*> pending{call};
                    std::set<const ICFGNode*> seen;
                    while (!pending.empty())
                    {
                        const auto* current = pending.back();
                        pending.pop_back();
                        if (!seen.insert(current).second)
                            continue;
                        for (const auto* edge : current->getInEdges())
                            if (const auto* intra = SVFUtil::dyn_cast<IntraCFGEdge>(edge))
                            {
                                if (intra->getCondition() && !intra->isSwitchEdge())
                                    assertion(intra->getCondition());
                                else
                                    pending.push_back(edge->getSrcNode());
                            }
                    }
                }
            }
        if (Options::AEClosureDependencySlice())
        {
            // Only a closed scalar component with a common concrete witness
            // may lose its relations. Memory, control and call interfaces stay.
            std::vector<SVF::RelationEdge> dependencies = edges;
            std::set<std::string> fallbackReasons;
            const PackSSA control(*ir_.getICFG(), {}, {}, {});
            if (!control.hasReducibleControlFlow())
                fallbackReasons.insert("multi-entry-control-cycle");
            struct PureDefinition
            {
                enum Kind { Free, Copy, Add, Sub } kind;
                const ValVar* value;
                const SVFVar* source;
                const ConstIntValVar* constant;
                const SVFStmt* statement;
                bool constantLeft = false;
            };
            std::map<SVF::Variable, PureDefinition> definitions;
            const auto retain = [&](const SVFVar* value, const char* reason) { queryVariable(value, reason); };
            const auto definitionReason = [](const SVFStmt* statement)
            {
                if (!statement) return "definition";
                if (SVFUtil::isa<LoadStmt>(statement) || SVFUtil::isa<StoreStmt>(statement)) return "memory";
                if (SVFUtil::isa<CallPE>(statement) || SVFUtil::isa<RetPE>(statement)) return "interface";
                if (SVFUtil::isa<PhiStmt>(statement) || SVFUtil::isa<SelectStmt>(statement)) return "merge";
                if (SVFUtil::isa<CmpStmt>(statement) || SVFUtil::isa<BranchStmt>(statement)) return "control";
                if (SVFUtil::isa<CopyStmt>(statement)) return "cast";
                if (SVFUtil::isa<BinaryOPStmt>(statement) || SVFUtil::isa<UnaryOPStmt>(statement)) return "arithmetic";
                return "definition";
            };
            const auto depend = [&](const SVFVar* target, const SVFVar* source)
            {
                const auto lhs = numeric(target), rhs = numeric(source);
                if (lhs && rhs && *lhs != *rhs)
                    dependencies.push_back({*lhs, *rhs});
            };
            const auto freeInput = [&](const ValVar* value)
            {
                const auto* node = value->getICFGNode();
                const auto* ret = node ? SVFUtil::dyn_cast<RetICFGNode>(node) : nullptr;
                const auto* call = ret ? ret->getCallICFGNode()
                    : node ? SVFUtil::dyn_cast<CallICFGNode>(node) : nullptr;
                const auto* function = call ? call->getCalledFunction() : nullptr;
                if (!function || !function->isDeclaration() || call->arg_size() ||
                        !call->getRetICFGNode() || call->getRetICFGNode()->getActualRet() != value)
                    return false;
                const auto& name = function->getName();
                return name == "rand" || name.rfind("__VERIFIER_nondet_", 0) == 0;
            };
            for (const auto variable : vocabulary)
            {
                const auto* value = adapter_.value(variable);
                const auto* type = value && value->getType()
                    ? SVFUtil::dyn_cast<SVFIntegerType>(value->getType()) : nullptr;
                if (!value || !type || type->isBoolean())
                {
                    recordRoot(variable, !value ? "memory" : type && type->isBoolean() ? "control" : "definition");
                    continue;
                }
                if (freeInput(value))
                {
                    definitions.emplace(variable, PureDefinition{PureDefinition::Free, value, nullptr, nullptr, nullptr});
                    continue;
                }
                const auto& incoming = value->getInEdges();
                const SVFStmt* def = incoming.size() == 1 ? *incoming.begin() : nullptr;
                if (const auto* copy = def ? SVFUtil::dyn_cast<CopyStmt>(def) : nullptr)
                {
                    if (copy->getCopyKind() == CopyStmt::COPYVAL &&
                            copy->getLHSVar()->getType() == copy->getRHSVar()->getType())
                    {
                        definitions.emplace(variable, PureDefinition{PureDefinition::Copy, value,
                            copy->getRHSVar(), nullptr, def});
                        continue;
                    }
                }
                if (const auto* binary = def ? SVFUtil::dyn_cast<BinaryOPStmt>(def) : nullptr)
                {
                    const auto* lhs = SVFUtil::dyn_cast<ConstIntValVar>(binary->getOpVar(0));
                    const auto* rhs = SVFUtil::dyn_cast<ConstIntValVar>(binary->getOpVar(1));
                    if ((binary->getOpcode() == BinaryOPStmt::Add || binary->getOpcode() == BinaryOPStmt::Sub) &&
                            (lhs || rhs))
                    {
                        definitions.emplace(variable, PureDefinition{
                            binary->getOpcode() == BinaryOPStmt::Add ? PureDefinition::Add : PureDefinition::Sub,
                            value, rhs ? binary->getOpVar(0) : binary->getOpVar(1), rhs ? rhs : lhs, def, !rhs});
                        continue;
                    }
                }
                recordRoot(variable, definitionReason(def));
            }
            std::set<const SVFStmt*> allStatements;
            for (auto it = ir_.begin(); it != ir_.end(); ++it)
                allStatements.insert(it->second->getOutEdges().begin(), it->second->getOutEdges().end());
            for (const auto* statement : allStatements)
            {
                const auto kind = statement->getEdgeKind();
                const bool known = kind == SVFStmt::Addr || kind == SVFStmt::Copy ||
                    kind == SVFStmt::Phi || kind == SVFStmt::Select || kind == SVFStmt::Cmp ||
                    kind == SVFStmt::BinaryOp || kind == SVFStmt::UnaryOp || kind == SVFStmt::Branch ||
                    kind == SVFStmt::Load || kind == SVFStmt::Store || kind == SVFStmt::Gep ||
                    kind == SVFStmt::Call || kind == SVFStmt::Ret;
                if (!known)
                    fallbackReasons.insert("unknown-statement-effect");
                if (const auto* comparison = SVFUtil::dyn_cast<CmpStmt>(statement))
                {
                    retain(comparison->getRes(), "control");
                    retain(comparison->getOpVar(0), "control");
                    retain(comparison->getOpVar(1), "control");
                    depend(comparison->getRes(), comparison->getOpVar(0));
                    depend(comparison->getRes(), comparison->getOpVar(1));
                }
                if (const auto* assign = SVFUtil::dyn_cast<AssignStmt>(statement))
                {
                    const auto target = numeric(assign->getLHSVar());
                    if (!target || !definitions.count(*target))
                    {
                        retain(assign->getLHSVar(), definitionReason(statement));
                        retain(assign->getRHSVar(), definitionReason(statement));
                    }
                }
                if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(statement))
                {
                    const auto target = numeric(multi->getRes());
                    if (!target || !definitions.count(*target))
                    {
                        retain(multi->getRes(), definitionReason(statement));
                        for (const auto* operand : multi->getOpndVars())
                            retain(operand, definitionReason(statement));
                    }
                }
                if (const auto* unary = SVFUtil::dyn_cast<UnaryOPStmt>(statement))
                {
                    retain(unary->getRes(), "arithmetic");
                    retain(unary->getOpVar(), "arithmetic");
                }
                if (const auto* select = SVFUtil::dyn_cast<SelectStmt>(statement))
                    retain(select->getCondition(), "control");
                if (const auto* branch = SVFUtil::dyn_cast<BranchStmt>(statement))
                    if (branch->isConditional())
                        assertion(branch->getCondition(), "control");
                if (const auto* gep = SVFUtil::dyn_cast<GepStmt>(statement))
                    for (const auto& part : gep->getOffsetVarAndGepTypePairVec())
                        retain(part.first, "address");
            }
            for (auto it = ir_.getICFG()->begin(); it != ir_.getICFG()->end(); ++it)
                if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(it->second))
                {
                    for (const auto* argument : call->getActualParms())
                        retain(argument, "interface");
                    const auto* ret = call->getRetICFGNode();
                    const auto* returned = ret && ret->getActualRet()
                        ? SVFUtil::dyn_cast<ValVar>(ret->getActualRet()) : nullptr;
                    if (returned && !freeInput(returned))
                        retain(returned, "interface");
                }
            std::map<SVF::Variable, SVF::Rational> witnesses;
            std::set<SVF::Variable> visiting;
            std::function<std::optional<SVF::Rational>(const SVFVar*)> witness;
            witness = [&](const SVFVar* source) -> std::optional<SVF::Rational>
            {
                if (const auto* constant = SVFUtil::dyn_cast<ConstIntValVar>(source))
                {
                    if (constant->getType()->getByteSize() > sizeof(s64_t))
                        return std::nullopt;
                    return SVF::Rational(constant->getSExtValue());
                }
                const auto variable = numeric(source);
                if (!variable)
                    return std::nullopt;
                if (const auto found = witnesses.find(*variable); found != witnesses.end())
                    return found->second;
                const auto found = definitions.find(*variable);
                if (found == definitions.end() || !visiting.insert(*variable).second)
                    return std::nullopt;
                const auto& def = found->second;
                auto value = def.kind == PureDefinition::Free ? std::optional<SVF::Rational>(SVF::Rational(0))
                             : witness(def.source);
                if (value && def.constant)
                {
                    const SVF::Rational constant(def.constant->getSExtValue());
                    value = def.kind == PureDefinition::Add ? *value + constant
                          : def.constantLeft ? constant - *value : *value - constant;
                }
                visiting.erase(*variable);
                if (!value)
                    return std::nullopt;
                const auto* type = SVFUtil::cast<SVFIntegerType>(def.value->getType());
                SVF::Rational modulus(1);
                for (u32_t bit = 0; bit < type->getByteSize() * 8; ++bit)
                    modulus = modulus * SVF::Rational(2);
                const auto lower = type->isSigned() ? SVF::Rational(0) - modulus / SVF::Rational(2)
                                   : SVF::Rational(0);
                const auto upper = type->isSigned() ? modulus / SVF::Rational(2) - SVF::Rational(1)
                                   : modulus - SVF::Rational(1);
                if (*value < lower || upper < *value)
                    return std::nullopt;
                witnesses.emplace(*variable, *value);
                return value;
            };
            for (const auto& item : definitions)
                if (!witness(item.second.value))
                    recordRoot(item.first, "witness");
            if (!fallbackReasons.empty())
                for (const auto variable : vocabulary)
                    recordRoot(variable, "fallback");
            const auto dependencyGroups = SVF::connectedComponentPacking(vocabulary, dependencies);
            const std::set<SVF::Variable> demanded(result.queries.begin(), result.queries.end());
            if (traceRoots)
                for (const auto& [variable, reasons] : rootReasons)
                    for (const auto& reason : reasons)
                        std::cerr << "AE_SLICE_ROOT_REASON " << variable.id() << ' ' << reason << '\n';
            for (const auto& group : dependencyGroups)
                if (std::any_of(group.begin(), group.end(),
                                [&](SVF::Variable variable) { return demanded.count(variable); }))
                    result.queries.insert(result.queries.end(), group.begin(), group.end());
            if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
            {
                for (std::size_t i = 0; i < result.packs.size(); ++i)
                {
                    std::cerr << "AE_SLICE_REFERENCE " << i;
                    for (const auto variable : result.packs[i])
                        std::cerr << ' ' << variable.id();
                    std::cerr << '\n';
                }
                for (const auto& edge : dependencies)
                    std::cerr << "AE_SLICE_DEPENDENCY " << edge.first.id() << ' ' << edge.second.id() << '\n';
                for (const auto variable : demanded)
                    std::cerr << "AE_SLICE_ROOT " << variable.id() << '\n';
                for (const auto& item : witnesses)
                {
                    const auto& def = definitions.at(item.first);
                    const auto source = def.source ? numeric(def.source) : std::nullopt;
                    std::cerr << "AE_SLICE_WITNESS " << item.first.id() << ' ' << item.second.toString()
                        << " kind=" << def.kind << " source=" << (source ? source->id() : 0)
                        << " constant=" << (def.constant ? def.constant->getSExtValue() : 0)
                        << " constant_left=" << def.constantLeft
                        << " literal_source=" << (def.source && SVFUtil::isa<ConstIntValVar>(def.source)
                            ? SVFUtil::cast<ConstIntValVar>(def.source)->getSExtValue() : 0)
                        << " source_is_literal=" << bool(def.source && SVFUtil::isa<ConstIntValVar>(def.source))
                        << " bits=" << def.value->getType()->getByteSize() * 8
                        << " signed=" << SVFUtil::cast<SVFIntegerType>(def.value->getType())->isSigned()
                        << " svf=" << def.value->getId()
                        << " stmt=" << (def.statement ? def.statement->getEdgeID() : 0) << '\n';
                }
            }
            SVFUtil::outs() << "AE_CLOSURE_SLICE schema=2 fallback=" << !fallbackReasons.empty();
            for (const auto& reason : fallbackReasons)
                SVFUtil::outs() << " reason=" << reason;
            SVFUtil::outs() << '\n';
        }
        std::sort(result.queries.begin(), result.queries.end());
        result.queries.erase(std::unique(result.queries.begin(), result.queries.end()), result.queries.end());
        std::map<SVF::Variable, std::size_t> component;
        for (std::size_t i = 0; i < result.packs.size(); ++i)
            for (const auto variable : result.packs[i])
                component.emplace(variable, i);
        std::set<std::size_t> retained;
        for (const auto& query : result.queries)
            retained.insert(component.at(query));
        SVF::RelationPacking filtered;
        for (std::size_t i = 0; i < result.packs.size(); ++i)
            if (retained.count(i))
                filtered.push_back(std::move(result.packs[i]));
            else
                for (const auto variable : result.packs[i])
                    filtered.push_back({variable});
        std::sort(filtered.begin(), filtered.end());
        result.packs = std::move(filtered);
    }
    return result;
}

StatementPackingDemand StatementRelationPacking::selectDemand(
    const SVF::RelationPacking& full,
    const std::vector<StatementPackingQuery>& queries) const
{
    const bool trace = std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY") != nullptr;
    std::map<Variable, std::vector<std::size_t>> owners;
    for (std::size_t index = 0; index < full.size(); ++index)
        for (const auto variable : full[index])
            owners[variable].push_back(index);

    std::map<NodeID, std::vector<const StoreStmt*>> stores;
    for (const auto* statement : ir_.getSVFStmtSet(SVFStmt::Store))
    {
        const auto* store = SVFUtil::cast<StoreStmt>(statement);
        const auto& targets = pointsTo_.getPts(store->getLHSVarID());
        for (const auto target : targets)
            if (const auto* base = ir_.getBaseObject(target))
                stores[base->getId()].push_back(store);
    }

    std::map<std::size_t, std::set<std::string>> retained;
    std::vector<const ICFGNode*> pendingNodes;
    std::vector<const SVFStmt*> pendingStatements;
    std::vector<const SVFVar*> pendingValues;
    std::set<const ICFGNode*> seenNodes;
    std::set<const SVFStmt*> seenStatements;
    std::set<const SVFVar*> seenValues;
    std::set<const BaseObjVar*> seenObjects;

    const auto keep = [&](SVF::Variable variable, const char* reason)
    {
        const auto found = owners.find(variable);
        if (found == owners.end())
            return;
        for (const auto index : found->second)
        {
            auto& reasons = retained[index];
            if (reasons.empty())
                for (const auto member : full[index])
                {
                    if (const auto* value = adapter_.value(member))
                        pendingValues.push_back(value);
                    if (const auto* object = adapter_.contentObject(member))
                        pendingValues.push_back(object);
                    if (const auto* object = adapter_.sizeObject(member))
                        pendingValues.push_back(object);
                }
            reasons.insert(reason);
        }
    };
    const auto enqueuePointer = [&](const ValVar* value)
    {
        const auto& targets = pointsTo_.getPts(value->getId());
        for (const auto target : targets)
        {
            const auto* object = SVFUtil::dyn_cast<ObjVar>(ir_.getGNode(target));
            if (object && target != IRGraph::BlackHole)
                pendingValues.push_back(object);
        }
    };

    for (const auto& query : queries)
    {
        if (trace)
            std::cerr << "AE_BOX_MAY_QUERY " << query.identity << '\n';
        pendingNodes.push_back(query.node);
        if (query.statement)
            pendingStatements.push_back(query.statement);
        if (query.operand)
            pendingValues.push_back(query.operand);

        if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(query.node))
        {
            if (query.kind == "stub-bounds" && call->arg_size() > 1)
                pendingValues.push_back(call->getArgument(1));
            else if (const auto length = query.kind.rfind("-len-"); length != std::string::npos)
            {
                // The length index is part of the detector's obligation ID.
                const auto index = std::stoul(query.kind.substr(length + 5));
                if (index < call->arg_size())
                    pendingValues.push_back(call->getArgument(index));
            }
            else if (query.kind == "ext-string-destination")
                for (const auto* argument : call->getActualParms())
                    pendingValues.push_back(argument);
        }
    }

    while (!pendingNodes.empty() || !pendingStatements.empty() || !pendingValues.empty())
    {
        if (!pendingNodes.empty())
        {
            const auto* node = pendingNodes.back();
            pendingNodes.pop_back();
            if (!seenNodes.insert(node).second)
                continue;
            if (const auto* ret = SVFUtil::dyn_cast<RetICFGNode>(node))
                pendingNodes.push_back(ret->getCallICFGNode());
            for (const auto* edge : node->getInEdges())
            {
                pendingNodes.push_back(edge->getSrcNode());
                if (const auto* intra = SVFUtil::dyn_cast<IntraCFGEdge>(edge))
                    if (const auto* condition = intra->getCondition())
                        pendingValues.push_back(condition);
            }
            continue;
        }
        if (!pendingStatements.empty())
        {
            const auto* statement = pendingStatements.back();
            pendingStatements.pop_back();
            if (!seenStatements.insert(statement).second)
                continue;
            if (const auto* node = statement->getICFGNode())
                pendingNodes.push_back(node);
            if (const auto* gep = SVFUtil::dyn_cast<GepStmt>(statement))
                for (const auto& part : gep->getOffsetVarAndGepTypePairVec())
                    pendingValues.push_back(part.first);
            if (const auto* address = SVFUtil::dyn_cast<AddrStmt>(statement))
                for (const auto* size : address->getArrSize())
                    pendingValues.push_back(size);
            if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(statement))
                for (u32_t index = 0; index < phi->getOpVarNum(); ++index)
                    pendingNodes.push_back(phi->getOpICFGNode(index));
            if (const auto* select = SVFUtil::dyn_cast<SelectStmt>(statement))
                pendingValues.push_back(select->getCondition());
            if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(statement))
            {
                pendingValues.push_back(multi->getRes());
                for (const auto* operand : multi->getOpndVars())
                    pendingValues.push_back(operand);
            }
            else if (const auto* unary = SVFUtil::dyn_cast<UnaryOPStmt>(statement))
            {
                pendingValues.push_back(unary->getRes());
                pendingValues.push_back(unary->getOpVar());
            }
            else if (const auto* assign = SVFUtil::dyn_cast<AssignStmt>(statement))
            {
                pendingValues.push_back(assign->getLHSVar());
                pendingValues.push_back(assign->getRHSVar());
            }
            continue;
        }
        const auto* variable = pendingValues.back();
        pendingValues.pop_back();
        if (!variable || !seenValues.insert(variable).second ||
            SVFUtil::isa<ConstIntValVar>(variable) || SVFUtil::isa<ConstFPValVar>(variable))
            continue;
        if (const auto* value = SVFUtil::dyn_cast<ValVar>(variable))
        {
            if (adapter_.contains(*value))
                keep(adapter_.variable(*value), "demand-or-transfer");
            if (value->isPointer() && !SVFUtil::isa<ConstNullPtrValVar>(value))
                enqueuePointer(value);
            if (const auto* node = value->getICFGNode())
                pendingNodes.push_back(node);
            for (const auto* definition : value->getInEdges())
                pendingStatements.push_back(definition);
            // A transfer narrowing a pack can also narrow an input coordinate.
            // Include its numerical interface across fixed component boundaries.
            for (const auto* use : value->getOutEdges())
                if (SVFUtil::isa<CopyStmt>(use) || SVFUtil::isa<BinaryOPStmt>(use) ||
                    SVFUtil::isa<UnaryOPStmt>(use) ||
                    SVFUtil::isa<PhiStmt>(use) || SVFUtil::isa<SelectStmt>(use) ||
                    SVFUtil::isa<CallPE>(use) || SVFUtil::isa<RetPE>(use) ||
                    SVFUtil::isa<LoadStmt>(use) || SVFUtil::isa<StoreStmt>(use))
                    pendingStatements.push_back(use);
        }
        else if (const auto* object = SVFUtil::dyn_cast<ObjVar>(variable))
        {
            if (!object->isPointer())
                keep(adapter_.contentVariable(*object), "alias-content");
            const auto* base = ir_.getBaseObject(object->getId());
            if (!base || !seenObjects.insert(base).second)
                continue;
            if (const auto found = stores.find(base->getId()); found != stores.end())
                pendingStatements.insert(pendingStatements.end(), found->second.begin(), found->second.end());
            if (const auto* size = sizes_ ? sizes_->find(base) : nullptr)
            {
                keep(adapter_.sizeVariable(*base), "allocation-size");
                if (size->sizeValue)
                    pendingValues.push_back(size->sizeValue);
                if (size->operand)
                    pendingValues.push_back(size->operand);
            }
            for (const auto id : ir_.getAllFieldsObjVars(base->getId()))
                if (const auto* field = SVFUtil::dyn_cast<ObjVar>(ir_.getGNode(id)))
                    pendingValues.push_back(field);
        }
    }

    std::set<std::size_t> selected;
    for (const auto& [index, reasons] : retained)
    {
        selected.insert(index);
        if (trace)
        {
            std::cerr << "AE_BOX_MAY_RETAIN " << index;
            for (const auto& reason : reasons)
                std::cerr << ' ' << reason;
            std::cerr << '\n';
        }
    }
    SVFUtil::outs() << "AE_BOX_MAY_SLICE fallback=0\n";
    return {std::move(selected), std::move(seenNodes), std::move(seenStatements),
            std::move(seenValues)};
}
}
