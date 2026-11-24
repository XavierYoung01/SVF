//===- BuiltInPacking.cpp -- Built-in AE packing --------===//
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
#include "AE/Svfexe/AbstractInterpretation.h"
#include "AE/Core/PackedRelationalDomain.h"
#include "AE/Svfexe/AllocationSize.h"
#include "AE/Svfexe/ImpactRelationPacking.h"
#include "AE/Svfexe/SAS16FeatureExtraction.h"
#include "AE/Svfexe/StatementRelationPacking.h"
#include "Util/Options.h"
#include "WPA/Andersen.h"
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <ctime>
#include <deque>
#include <fstream>
#include <iostream>
#include <unordered_set>

using namespace SVF;
using namespace SVFUtil;

static std::vector<const ValVar*> definitionOperands(const SVFStmt* statement)
{
    std::vector<const ValVar*> result;
    const auto add = [&](const SVFVar* variable)
    {
        if (const auto* value = SVFUtil::dyn_cast<ValVar>(variable))
            result.push_back(value);
    };
    // Loads are an explicit memory boundary for the initial static slice. The
    // loaded result can still be selected, but its relational payload is
    // reconstructed from the global Box hull rather than following a pointer.
    if (SVFUtil::isa<LoadStmt>(statement))
        return result;
    if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(statement))
    {
        for (const ValVar* operand : multi->getOpndVars())
            add(operand);
    }
    else if (const auto* unary = SVFUtil::dyn_cast<UnaryOPStmt>(statement))
        add(unary->getOpVar());
    else if (const auto* assignment =
                 SVFUtil::dyn_cast<AssignStmt>(statement))
        add(assignment->getRHSVar());
    if (const auto* address = SVFUtil::dyn_cast<AddrStmt>(statement))
        for (const SVFVar* size : address->getArrSize())
            add(size);
    std::sort(result.begin(), result.end(),
              [](const ValVar* left, const ValVar* right)
    {
        return left->getId() < right->getId();
    });
    result.erase(std::unique(result.begin(), result.end()), result.end());
    return result;
}

bool AbstractInterpretation::initializeBuiltInPacking()
{
    initializeRelationalPolicy();
    const bool publishedFixed = relationalPolicy() == DuetPackedRelational ||
                                relationalPolicy() == SpePackedRelational;
    if (publishedFixed)
        dumpFixedPacking("AE_POLICY_RAW_PACK");
    else
        initializeObjectPacking();
    const bool lateFieldsUseBox = publishedFixed || !objectPacks_.empty();
    if (usesBuiltInOnDemand())
    {
        const auto selectionStart = std::chrono::steady_clock::now();
        const auto selectionCpu = std::clock();
        selectBoxMayPacks();
        const double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - selectionStart).count();
        const double cpu = double(std::clock() - selectionCpu) / CLOCKS_PER_SEC;
        SVFUtil::outs() << "AE_BOX_MAY_SELECTION_SECONDS " << seconds
                       << " cpu_s=" << cpu << '\n';
    }
    return lateFieldsUseBox;
}

void AbstractInterpretation::initializeRelationalPolicy()
{
    const u32_t policy = relationalPolicy();
    if (policy == ClosurePackedRelational || policy == ImpactPackedRelational ||
            policy == LearnedPackedRelational || policy == DuetPackedRelational ||
            policy == SpePackedRelational)
    {
        initializeFixedPacking();
        return;
    }
    if (policy == SyntaxPackedRelational)
    {
        initializeSyntaxPacking();
        return;
    }
    if (policy == WholeRelational)
        return;
    if (numericalDomain() == AENumericalDomain::Box)
    {
        assert(false && "partial relational policies require octagon or polyhedra");
        std::abort();
    }

    std::vector<const ValVar*> seeds;
    const auto addSeed = [&](const SVFVar* variable)
    {
        if (const auto* value = SVFUtil::dyn_cast<ValVar>(variable))
            if (adapter_.contains(*value))
                seeds.push_back(value);
    };
    for (auto iterator = icfg->begin(); iterator != icfg->end(); ++iterator)
    {
        const ICFGNode* node = iterator->second;
        if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(node))
        {
            const FunObjVar* function = call->getCalledFunction();
            if (function &&
                    (function->getName() == "SAFE_BUFACCESS" ||
                     function->getName() == "UNSAFE_BUFACCESS") &&
                    call->arg_size() >= 2)
                addSeed(call->getArgument(1));
            if (function && SVFUtil::isExtCall(function) &&
                    call->arg_size() != 0)
            {
                bool sizedMemoryOperation = false;
                for (const std::string& annotation :
                        ExtAPI::getExtAPI()->getExtFuncAnnotations(function))
                    sizedMemoryOperation |=
                        annotation.find("MEMCPY") != std::string::npos ||
                        annotation.find("MEMSET") != std::string::npos;
                if (sizedMemoryOperation)
                    addSeed(call->getArgument(call->arg_size() - 1));
            }
        }
        for (const SVFStmt* statement : node->getSVFStmts())
        {
            // Branch guards are the numerical proof obligations that decide
            // whether detector checkpoints are reachable. Seed their operands
            // even when the eventual query operand is a pointer (for example
            // an infeasible null-dereference branch).
            if (const auto* compare = SVFUtil::dyn_cast<CmpStmt>(statement))
                for (const ValVar* operand : compare->getOpndVars())
                    addSeed(operand);
            if (const auto* gep = SVFUtil::dyn_cast<GepStmt>(statement))
                for (const auto& [index, type] :
                        gep->getOffsetVarAndGepTypePairVec())
                {
                    (void)type;
                    addSeed(index);
                }
            if (const auto* address = SVFUtil::dyn_cast<AddrStmt>(statement))
                for (const SVFVar* size : address->getArrSize())
                    addSeed(size);
        }
    }

    const auto byVariable = [&](const ValVar* left, const ValVar* right)
    {
        return left->getId() < right->getId();
    };
    std::sort(seeds.begin(), seeds.end(), byVariable);
    seeds.erase(std::unique(seeds.begin(), seeds.end()), seeds.end());
    relationalSeedCount_ = seeds.size();

    // The query slice is deliberately computed independently from Eva-style
    // expression recognition. This keeps the two policy dimensions
    // measurable instead of silently changing the existing baseline.
    std::deque<const ValVar*> worklist(seeds.begin(), seeds.end());
    std::unordered_set<NodeID> seen;
    std::vector<SVF::Variable> queryClosure;
    while (!worklist.empty())
    {
        const ValVar* value = worklist.front();
        worklist.pop_front();
        if (!seen.insert(value->getId()).second)
            continue;
        if (adapter_.contains(*value))
            queryClosure.push_back(adapter_.variable(*value));

        std::vector<const SVFStmt*> definitions(
            value->getInEdges().begin(), value->getInEdges().end());
        std::sort(definitions.begin(), definitions.end(),
                  [](const SVFStmt* left, const SVFStmt* right)
        {
            return left->getEdgeID() < right->getEdgeID();
        });
        std::vector<const ValVar*> operands;
        for (const SVFStmt* definition : definitions)
        {
            std::vector<const ValVar*> current =
                definitionOperands(definition);
            operands.insert(operands.end(), current.begin(), current.end());
        }
        std::sort(operands.begin(), operands.end(), byVariable);
        operands.erase(std::unique(operands.begin(), operands.end()),
                       operands.end());
        for (const ValVar* operand : operands)
            if (seen.count(operand->getId()) == 0)
                worklist.push_back(operand);
    }

    // Eva's native Octagon creates relations only from recognizable affine
    // shapes. The current SVF carrier still stores a complete Octagon over the
    // selected vocabulary, so these pairs induce candidate variables rather
    // than claiming Eva's sparse-pair carrier or partial saturation.
    std::vector<SVF::Variable> evaCandidates;
    std::unordered_set<NodeID> evaSeen;
    std::size_t recognizedPairs = 0;
    // SVF formal-return ghosts can lose the source integer type and are then
    // conservatively represented as Real by the adapter. Octagons support
    // both Integer and Real coordinates; only pointer and IEEE-float values
    // are outside this policy's affine numerical vocabulary.
    const auto octagonalValue = [&](const ValVar* value)
    {
        return value && adapter_.contains(*value) && !value->isPointer() &&
               adapter_.variable(*value).type().kind !=
               SVF::NumericKind::IEEEFloat;
    };
    const auto addCandidate = [&](const ValVar* value)
    {
        if (octagonalValue(value) && evaSeen.insert(value->getId()).second)
            evaCandidates.push_back(adapter_.variable(*value));
    };
    const auto addPair = [&](const ValVar* left, const ValVar* right)
    {
        const bool leftOctagonal = octagonalValue(left);
        const bool rightOctagonal = octagonalValue(right);
        if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
        {
            const auto printValue = [&](const ValVar* value,
                                        bool accepted)
            {
                std::cerr << (value ? value->getId() : 0) << ':'
                          << accepted << ':'
                          << (value && adapter_.contains(*value)) << ':'
                          << (value && value->isPointer()) << ':';
                if (value && adapter_.contains(*value))
                    std::cerr << static_cast<unsigned>(
                                  adapter_.variable(*value).type().kind);
                else
                    std::cerr << '-';
            };
            std::cerr << "AE_RELATIONAL_PAIR=";
            printValue(left, leftOctagonal);
            std::cerr << ',';
            printValue(right, rightOctagonal);
            std::cerr << '\n';
        }
        if (!leftOctagonal || !rightOctagonal || left == right)
            return;
        ++recognizedPairs;
        addCandidate(left);
        addCandidate(right);
    };

    if (policy == EvaStyleRelational || policy == QueryEvaRelational)
    {
        const bool throughCalls =
            Options::AERelationalCallPolicy() == ThroughCalls;
        // Function-return phis and interprocedural edges are not guaranteed to
        // appear in an ICFG node's local statement list. A RetPE is also an
        // outgoing edge of the formal-return ghost, so walking only value
        // definitions misses one endpoint. Collect the canonical statement
        // sets for every recognized kind, then sort by stable edge identity
        // for a deterministic bounded vocabulary.
        std::vector<const SVFStmt*> statements;
        const auto addStatements = [&](SVFStmt::PEDGEK kind)
        {
            const SVFStmt::SVFStmtSetTy& current =
                svfir->getSVFStmtSet(kind);
            statements.insert(statements.end(), current.begin(),
                              current.end());
        };
        addStatements(SVFStmt::BinaryOp);
        addStatements(SVFStmt::Cmp);
        addStatements(SVFStmt::Phi);
        addStatements(SVFStmt::Select);
        addStatements(SVFStmt::Copy);
        if (throughCalls)
        {
            addStatements(SVFStmt::Call);
            addStatements(SVFStmt::Ret);
            addStatements(SVFStmt::ThreadFork);
            addStatements(SVFStmt::ThreadJoin);
        }
        std::sort(statements.begin(), statements.end(),
                  [](const SVFStmt* left, const SVFStmt* right)
        {
            return left->getEdgeID() < right->getEdgeID();
        });
        statements.erase(std::unique(statements.begin(), statements.end()),
                         statements.end());
        for (const SVFStmt* statement : statements)
        {
            if (const auto* binary =
                        SVFUtil::dyn_cast<BinaryOPStmt>(statement))
            {
                if (binary->getOpcode() == BinaryOPStmt::Add ||
                        binary->getOpcode() == BinaryOPStmt::Sub)
                    for (const ValVar* operand : binary->getOpndVars())
                        addPair(binary->getRes(), operand);
            }
            else if (const auto* compare =
                         SVFUtil::dyn_cast<CmpStmt>(statement))
            {
                if (compare->getOpVarNum() == 2)
                    addPair(compare->getOpVar(0), compare->getOpVar(1));
            }
            else if (const auto* phi =
                         SVFUtil::dyn_cast<PhiStmt>(statement))
            {
                for (const ValVar* operand : phi->getOpndVars())
                    addPair(phi->getRes(), operand);
            }
            else if (const auto* select =
                         SVFUtil::dyn_cast<SelectStmt>(statement))
            {
                for (const ValVar* operand : select->getOpndVars())
                    addPair(select->getRes(), operand);
            }
            else if (throughCalls)
            {
                if (const auto* call =
                            SVFUtil::dyn_cast<CallPE>(statement))
                    for (const ValVar* operand : call->getOpndVars())
                        addPair(call->getRes(), operand);
                else if (const auto* ret =
                             SVFUtil::dyn_cast<RetPE>(statement))
                    addPair(ret->getLHSVar(), ret->getRHSVar());
                else if (const auto* copy =
                             SVFUtil::dyn_cast<CopyStmt>(statement))
                    addPair(copy->getLHSVar(), copy->getRHSVar());
            }
            else if (const auto* copy =
                         SVFUtil::dyn_cast<CopyStmt>(statement))
                addPair(copy->getLHSVar(), copy->getRHSVar());
        }
    }

    std::vector<SVF::Variable> selected;
    if (policy == QuerySliceRelational)
        selected = queryClosure;
    else if (policy == EvaStyleRelational)
        selected = evaCandidates;
    else
    {
        const std::set<SVF::Variable> recognized(evaCandidates.begin(),
                evaCandidates.end());
        for (SVF::Variable variable : queryClosure)
            if (recognized.count(variable) != 0)
                selected.push_back(variable);
        // Query operands remain available even when the current IR has no
        // recognizable binary partner. This fallback can only add precision
        // to the global Box state and makes an empty candidate set explicit.
        for (const ValVar* seed : seeds)
            if (adapter_.contains(*seed))
                selected.push_back(adapter_.variable(*seed));
    }

    // Query-slice BFS order prioritizes query seeds. Eva-style order follows
    // deterministic ICFG/statement traversal. Canonicalize only after the cap.
    std::vector<SVF::Variable> uniqueSelected;
    std::set<SVF::Variable> selectedSeen;
    for (SVF::Variable variable : selected)
        if (selectedSeen.insert(variable).second)
            uniqueSelected.push_back(variable);
    const std::size_t limit = Options::AERelationalMaxVars();
    relationalDroppedCount_ = uniqueSelected.size() > limit
                              ? uniqueSelected.size() - limit : 0;
    if (uniqueSelected.size() > limit)
        uniqueSelected.resize(limit);
    std::sort(uniqueSelected.begin(), uniqueSelected.end());
    relationalVocabulary_ =
        std::make_shared<const std::vector<SVF::Variable>>(
            std::move(uniqueSelected));

    const char* policyName = policy == QuerySliceRelational ? "query-slice" :
                             policy == EvaStyleRelational ? "eva-style" :
                             "query-eva";
    const char* callName =
        Options::AERelationalCallPolicy() == ThroughCalls
        ? "through" : "intraprocedural";

    SVFUtil::outs()
            << "AE_RELATIONAL_POLICY policy=" << policyName
            << " calls=" << callName << " seeds="
            << relationalSeedCount_
            << " recognized_pairs=" << recognizedPairs
            << " candidates=" << evaCandidates.size()
            << " selected=" << relationalVocabulary_->size()
            << " dropped=" << relationalDroppedCount_
            << " max=" << Options::AERelationalMaxVars() << '\n';
    if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
    {
        const auto printVariables = [&](const char* label,
                                        const std::vector<SVF::Variable>& values)
        {
            std::cerr << label << '=';
            for (SVF::Variable variable : values)
            {
                const ValVar* value = adapter_.value(variable);
                std::cerr << variable.id() << ':'
                          << (value ? value->getId() : 0) << ',';
            }
            std::cerr << '\n';
        };
        printVariables("AE_RELATIONAL_QUERY_CLOSURE", queryClosure);
        printVariables("AE_RELATIONAL_EVA_CANDIDATES", evaCandidates);
        printVariables("AE_RELATIONAL_SELECTED", *relationalVocabulary_);
    }
}


void AbstractInterpretation::initializeSyntaxPacking()
{
    if (numericalDomain() != Octagon)
    {
        assert(false && "syntax-pack currently requires native Octagon");
        std::abort();
    }
    const std::size_t cap = Options::AEPackMaxVars();
    if (cap == 0) throw std::invalid_argument("ae-pack-max-vars must be positive");
    using Group = std::set<SVF::Variable>;
    std::vector<Group> candidates;
    std::map<const SVFBasicBlock*, Group> blocks;
    std::map<const ICFGNode*, Group> nodeGroups;
    const auto addValue = [&](Group& group, const SVFVar* var)
    {
        const auto* value = SVFUtil::dyn_cast<ValVar>(var);
        if (value && !value->isPointer() && adapter_.contains(*value))
        {
            const auto variable = adapter_.variable(*value);
            if (variable.type().kind != SVF::NumericKind::IEEEFloat) group.insert(variable);
        }
    };
    const auto addObjects = [&](Group& group, const ValVar* pointer)
    {
        for (NodeID id : preAnalysis->getPointerAnalysis()->getPts(pointer->getId()))
            if (const auto* object = SVFUtil::dyn_cast<ObjVar>(svfir->getGNode(id)))
            {
                const auto content = adapter_.contentVariable(*object);
                if (content.type().kind != SVF::NumericKind::IEEEFloat) group.insert(content);
            }
    };
    std::vector<const SVFStmt*> statements;
    for (auto kind :
            {
                SVFStmt::BinaryOp, SVFStmt::Cmp, SVFStmt::Copy,
                SVFStmt::Phi, SVFStmt::Select, SVFStmt::Call,
                SVFStmt::Ret, SVFStmt::Load, SVFStmt::Store
            })
    {
        const auto& current = svfir->getSVFStmtSet(kind);
        statements.insert(statements.end(), current.begin(), current.end());
    }
    std::sort(statements.begin(), statements.end(), [](const SVFStmt* a, const SVFStmt* b)
    {
        return a->getEdgeID() < b->getEdgeID();
    });
    for (const auto* statement : statements)
    {
        if (const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(statement))
            if (binary->getOpcode() != BinaryOPStmt::Add && binary->getOpcode() != BinaryOPStmt::Sub &&
                    binary->getOpcode() != BinaryOPStmt::Mul) continue;
        Group group;
        for (const auto* value : definitionOperands(statement)) addValue(group, value);
        if (const auto* multi = SVFUtil::dyn_cast<MultiOpndStmt>(statement)) addValue(group, multi->getRes());
        if (const auto* assignment = SVFUtil::dyn_cast<AssignStmt>(statement)) addValue(group, assignment->getLHSVar());
        if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(statement)) addObjects(group, load->getRHSVar());
        if (const auto* store = SVFUtil::dyn_cast<StoreStmt>(statement)) addObjects(group, store->getLHSVar());
        if (group.empty()) continue;
        candidates.push_back(group); // preserves each expression/call binding independently
        if (statement->getBB()) blocks[statement->getBB()].insert(group.begin(), group.end());
    }
    for (const auto& block : blocks) candidates.push_back(block.second);
    for (auto it=icfg->begin(); it!=icfg->end(); ++it)
        if (it->second->getBB()) nodeGroups[it->second]=blocks[it->second->getBB()];
    // Natural/WTO loop locality, including phi operands and nested cycles.
    std::function<Group(const ICFGWTOComp*)> collect = [&](const ICFGWTOComp* component)
    {
        if (const auto* singleton=SVFUtil::dyn_cast<ICFGSingletonWTO>(component))
            return nodeGroups[singleton->getICFGNode()];
        Group group;
        if (const auto* cycle=SVFUtil::dyn_cast<ICFGCycleWTO>(component))
        {
            group=nodeGroups[cycle->head()->getICFGNode()];
            for (const auto* child:cycle->getWTOComponents())
            {
                auto sub=collect(child);
                group.insert(sub.begin(),sub.end());
            }
            if (!group.empty()) candidates.push_back(group);
        }
        return group;
    };
    for (const auto& function:preAnalysis->getFuncToWTO())
        if (function.second) for (const auto* component:function.second->getWTOComponents()) collect(component);
    std::set<std::vector<SVF::Variable>> unique;
    Group all;
    for (const auto& group:candidates)
    {
        std::vector<SVF::Variable> chunk;
        for (auto v:group)
        {
            all.insert(v);
            chunk.push_back(v);
            if (chunk.size()==cap)
            {
                unique.insert(chunk);
                chunk.clear();
            }
        }
        if (!chunk.empty()) unique.insert(chunk);
    }
    // Remove exact subsets: a larger pack already carries that local relation.
    // This is deterministic and does not transitively merge overlapping packs.
    std::vector<std::vector<SVF::Variable>> result;
    for (const auto& group:unique)
    {
        bool subsumed=false;
        for (const auto& other:unique)
            if (other.size()>group.size() && std::includes(other.begin(),other.end(),group.begin(),group.end()))
            {
                subsumed=true;
                break;
            }
        if (!subsumed) result.push_back(group);
    }
    std::size_t memberships=0,maxSize=0;
    for (const auto& group:result)
    {
        memberships+=group.size();
        maxSize=std::max(maxSize,group.size());
    }
    relationalPacking_=std::make_shared<const std::vector<std::vector<SVF::Variable>>>(std::move(result));
    relationalVocabulary_=std::make_shared<const std::vector<SVF::Variable>>(all.begin(),all.end());
    SVFUtil::outs()<<"AE_SYNTAX_PACK packs="<<relationalPacking_->size()<<" variables="<<all.size()
                   <<" memberships="<<memberships<<" max="<<maxSize<<" cap="<<cap
                   <<" candidates="<<candidates.size()<<" locality=ir-basic-block-wto-loop\n";
    if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
        for (std::size_t i=0; i<relationalPacking_->size(); ++i)
        {
            std::cerr << "AE_SYNTAX_PACK_MEMBERS " << i;
            for (auto variable:relationalPacking_->at(i)) std::cerr << ' ' << variable.id();
            std::cerr << '\n';
        }
}

void AbstractInterpretation::initializeFixedPacking()
{
    const bool impact = relationalPolicy() == ImpactPackedRelational;
    if (numericalDomain() != Octagon)
        throw std::invalid_argument(impact ? "impact-pack requires native Octagon" :
                                    "fixed packing requires native Octagon");
    initializePackingVocabulary();
    // B0 control: the same packed executor with every variable in its own
    // pack, separating executor effects from multi-variable relations.
    if (std::getenv("SVF_AE_SINGLETON_PACKS"))
    {
        if (relationalPolicy() != ClosurePackedRelational)
        {
            assert(false && "SVF_AE_SINGLETON_PACKS requires closure-pack");
            std::abort();
        }
        SVF::RelationPacking packs;
        for (auto variable : *relationalVocabulary_)
            packs.push_back({variable});
        relationalPacking_ = std::make_shared<const SVF::RelationPacking>(std::move(packs));
        SVFUtil::outs() << "AE_SINGLETON_PACK packs=" << relationalPacking_->size()
                        << " variables=" << relationalVocabulary_->size()
                        << " max=1 edges=0 cap=none control=b0\n";
        return;
    }
    if (relationalPolicy() == DuetPackedRelational)
    {
        auto packs = StatementRelationPacking(*svfir, adapter_,
                     *preAnalysis->getPointerAnalysis()).packDuet(*relationalVocabulary_);
        relationalPacking_ = std::make_shared<const RelationPacking>(std::move(packs));
        return;
    }
    if (relationalPolicy() == SpePackedRelational)
    {
        std::vector<const ICFGNode*> entries;
        auto functions = collectProgEntryFuns();
        while (!functions.empty())
            entries.push_back(icfg->getFunEntryICFGNode(functions.pop()));
        std::vector<StatementPackingQuery> queries;
        for (const auto& [key, record] : queryLedger_)
        {
            (void)key;
            queries.push_back({queryIdentityFields(record).front(), icfg->getICFGNode(record.icfgNode),
                record.statement, record.operand ? svfir->getSVFVar(record.operand) : nullptr,
                record.queryKind});
        }
        std::sort(queries.begin(), queries.end(), [](const auto& a, const auto& b)
        {
            return a.identity < b.identity;
        });
        auto packs = StatementRelationPacking(*svfir, adapter_, *preAnalysis->getPointerAnalysis(),
            &allocationSizeModel()).packSpe(*relationalVocabulary_, entries, queries);
        relationalPacking_ = std::make_shared<const RelationPacking>(std::move(packs));
        return;
    }
    if (relationalPolicy() == LearnedPackedRelational)
    {
        using PhaseClock = std::chrono::steady_clock;
        const auto secondsSince = [](PhaseClock::time_point start)
        {
            return std::chrono::duration<double>(PhaseClock::now() - start).count();
        };
        const auto* path = std::getenv("SVF_LEARNED_MODEL");
        if (!path) throw std::invalid_argument("learned-pack requires SVF_LEARNED_MODEL");
        std::ifstream input(path);
        auto model = SVF::PackingDecisionTree::read(input);
        const auto featureStart = PhaseClock::now();
        auto context = extractSAS16Features(*svfir, adapter_, *preAnalysis->getPointerAnalysis(), *relationalVocabulary_,std::getenv("SVF_SAS16_LEGACY_FEATURES")!=nullptr);
        const auto featureSeconds = secondsSince(featureStart);
        const auto schema=context.schema;
        SVF::LearnedRelationPacking learned(std::move(context),std::move(model));
        const auto classifierStart = PhaseClock::now();
        auto result = learned.pack(*relationalVocabulary_);
        const auto classifierSeconds = secondsSince(classifierStart);
        relationalPacking_ = std::make_shared<const SVF::RelationPacking>(std::move(result.packs));
        std::size_t maximum = 0;
        for (const auto& pack : *relationalPacking_) maximum = std::max(maximum, pack.size());
        SVFUtil::outs() << "AE_LEARNED_PACK packs=" << relationalPacking_->size()
                        << " variables=" << relationalVocabulary_->size() << " max=" << maximum
                        << " edges=" << result.edges.size() << " pairs=" << result.pairs
                        << " profiles="<<result.profiles<<" profile_evaluations="<<result.profileEvaluations
                        << " exceptional_pairs="<<result.exceptionalPairs
                        << " feature_s=" << featureSeconds << " classifier_s=" << classifierSeconds
                        << " features=30 cap=none impact_executed=0 schema="
                        <<(schema==SVF::PackingFeatureSchema::LegacyV1?"svf-sas16-adaptation-v1":"svf-sas16-paper-features-v2")<<'\n';
        if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
            for (std::size_t i = 0; i < relationalPacking_->size(); ++i)
            {
                std::cerr << "AE_LEARNED_PACK_MEMBERS " << i;
                for (auto v : relationalPacking_->at(i)) std::cerr << ' ' << v.id();
                std::cerr << '\n';
            }
        return;
    }
    if (impact)
    {
        using ImpactClock = std::chrono::steady_clock;
        const auto intervalStart = ImpactClock::now();
        const auto intervalCpuStart = std::clock();
        std::unique_ptr<AbstractInterpretation> intervals;
        if (!Options::AEImpactQueryComponents() &&
                !std::getenv("SVF_SPARROW_PACK_IMPORT") &&
                !std::getenv("SVF_SPARROW_VOCAB_EXPORT"))
            intervals = intervalPreanalysis();
        const double intervalSeconds = std::chrono::duration<double>(
            ImpactClock::now() - intervalStart).count();
        const double intervalCpu = double(std::clock() - intervalCpuStart) / CLOCKS_PER_SEC;
        std::vector<const ICFGNode*> entries;
        auto functions = collectProgEntryFuns();
        while (!functions.empty()) entries.push_back(icfg->getFunEntryICFGNode(functions.pop()));
        auto result = ImpactRelationPacking(*svfir, adapter_,
                                            *preAnalysis->getPointerAnalysis(), std::move(entries),
                                            &allocationSizeModel(), intervals.get()).pack(*relationalVocabulary_);
        relationalPacking_ = std::make_shared<const SVF::RelationPacking>(std::move(result.packs));
        std::size_t maximum = 0, promising = 0, unsupported = 0;
        for (const auto& pack : *relationalPacking_) maximum = std::max(maximum, pack.size());
        for (const auto& query : result.queries)
        {
            promising += query.promising;
            unsupported += !query.supported;
        }
        SVFUtil::outs() << "AE_IMPACT_PACK packs=" << relationalPacking_->size()
                        << " variables=" << relationalVocabulary_->size() << " max=" << maximum
                        << " edges=" << result.edges.size() << " queries=" << result.queries.size()
                        << " promising=" << promising << " unsupported=" << unsupported
                        << " transfers=" << result.transfers << " commands=" << result.commands
                        << " phi_fallbacks=" << result.phiFallbacks
                        << " cap=none locality="
                        << (std::getenv("SVF_SPARROW_PACK_IMPORT") ? "native-partition" : "promising-query-snapshots")
                        << " semantics="
                        << (std::getenv("SVF_SPARROW_PACK_IMPORT") ? "checked-native-packs" : "svf-impact-adaptation") << '\n';
        if (std::getenv("SVF_SPARROW_PACK_IMPORT"))
            SVFUtil::outs() << "AE_NATIVE_PACK_PREANALYSIS external=1 cost_source=manifest\n"
                            << "AE_NATIVE_PACK_IMPORT_SECONDS " << result.extractionSeconds << '\n';
        else
            SVFUtil::outs() << "AE_IMPACT_INTERVAL_SECONDS " << intervalSeconds << '\n'
                            << "AE_IMPACT_INTERVAL_CPU_SECONDS " << intervalCpu << '\n'
                            << "AE_IMPACT_PREANALYSIS_SECONDS " << result.preanalysisSeconds << '\n'
                            << "AE_IMPACT_EXTRACTION_SECONDS " << result.extractionSeconds << '\n';
        if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
        {
            for (auto variable : *relationalVocabulary_)
            {
                const auto* value = adapter_.value(variable);
                const auto* object = adapter_.contentObject(variable);
                const auto* sized = adapter_.sizeObject(variable);
                std::cerr << "AE_IMPACT_VARIABLE id=" << variable.id()
                          << " facet=" << (value ? "value" : object ? "content" : "size")
                          << " svf=" << (value ? value->getId() : object ? object->getId()
                                         : sized->getId()) << '\n';
            }
            for (const auto& query : result.queries)
            {
                std::cerr << "AE_IMPACT_QUERY node=" << query.node << " kind=" << query.kind
                          << " supported=" << query.supported << " promising=" << query.promising << '\n';
                for (const auto& edge : query.snapshot)
                    std::cerr << "AE_IMPACT_SNAPSHOT node=" << query.node
                              << " src=" << edge.first.id() << " dst=" << edge.second.id() << '\n';
            }
            for (const auto& edge : result.edges)
                std::cerr << "AE_IMPACT_EDGE kind=impact lhs=" << edge.first.id()
                          << " rhs=" << edge.second.id() << '\n';
            for (std::size_t i = 0; i < relationalPacking_->size(); ++i)
            {
                std::cerr << "AE_IMPACT_PACK_MEMBERS " << i;
                for (auto variable : relationalPacking_->at(i)) std::cerr << ' ' << variable.id();
                std::cerr << '\n';
            }
        }
        return;
    }
    auto result = StatementRelationPacking(
                      *svfir, adapter_, *preAnalysis->getPointerAnalysis(),
                      &allocationSizeModel()).pack(*relationalVocabulary_,
                              Options::AEClosureDifferences(), Options::AEClosureQueries());
    relationalPacking_ = std::make_shared<const SVF::RelationPacking>(std::move(result.packs));
    std::size_t maximum = 0;
    for (const auto& pack : *relationalPacking_)
        maximum = std::max(maximum, pack.size());
    SVFUtil::outs() << "AE_CLOSURE_PACK packs=" << relationalPacking_->size()
                    << " variables=" << relationalVocabulary_->size() << " max=" << maximum
                    << " edges=" << result.edges.size()
                    << " query_variables=" << result.queries.size()
                    << " differences=" << Options::AEClosureDifferences()
                    << " query_filter=" << Options::AEClosureQueries()
                    << " cap=none locality=statement-points-to-components\n";
    if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
    {
        for (auto variable : *relationalVocabulary_)
        {
            const auto* value = adapter_.value(variable);
            const auto* object = adapter_.contentObject(variable);
            const auto* sized = adapter_.sizeObject(variable);
            std::cerr << "AE_CLOSURE_VARIABLE id=" << variable.id()
                      << " facet=" << (value ? "value" : object ? "content" : "size")
                      << " svf=" << (value ? value->getId() : object ? object->getId()
                                     : sized->getId()) << '\n';
        }
        for (const auto& edge : result.edges)
            std::cerr << "AE_CLOSURE_EDGE kind=" << edge.kind
                      << " stmt=" << edge.statement
                      << " lhs=" << edge.variables.first.id()
                      << " rhs=" << edge.variables.second.id() << '\n';
        for (const auto& query : result.queries)
            std::cerr << "AE_CLOSURE_QUERY variable=" << query.id() << '\n';
        for (std::size_t i = 0; i < relationalPacking_->size(); ++i)
        {
            std::cerr << "AE_CLOSURE_PACK_MEMBERS " << i;
            for (auto variable : relationalPacking_->at(i))
                std::cerr << ' ' << variable.id();
            std::cerr << '\n';
        }
    }
}

void AbstractInterpretation::initializeObjectPacking()
{
    if (!relationalPacking_ || numericalDomain() != Octagon ||
            std::getenv("SVF_AE_SINGLETON_PACKS"))
        return;
    std::map<SVF::Variable, SVF::Variable> parents;
    const auto add = [&](SVF::Variable variable)
    {
        parents.emplace(variable, variable);
    };
    std::function<SVF::Variable(SVF::Variable)> root = [&](SVF::Variable variable)
    {
        const auto parent = parents.at(variable);
        if (parent == variable) return variable;
        return parents.at(variable) = root(parent);
    };
    const auto connect = [&](SVF::Variable left, SVF::Variable right)
    {
        add(left);
        add(right);
        left = root(left);
        right = root(right);
        if (left != right) parents.at(std::max(left, right)) = std::min(left, right);
    };
    std::map<const ObjVar*, SVF::Variable> bases;
    for (const auto& pack : *relationalPacking_)
        for (const auto variable : pack)
        {
            add(variable);
            connect(pack.front(), variable);
            const auto* object = adapter_.contentObject(variable);
            if (!object) object = adapter_.sizeObject(variable);
            if (!object) continue;
            const auto* base = svfir->getBaseObject(object->getId());
            if (!base->isArray() && base->getMaxFieldOffsetLimit() <= 1)
                continue;
            const auto anchor = adapter_.contentVariable(*base);
            if (anchor.type().kind == SVF::NumericKind::IEEEFloat) continue;
            bases.emplace(base, anchor);
            connect(anchor, variable);
            const auto size = adapter_.sizeVariable(*base);
            connect(anchor, size);
            if (std::getenv("SVF_AE_TRACE_ROOT_REASONS"))
                std::cerr << "AE_PACK_BASE_LINK " << anchor.id() << ' ' << variable.id()
                          << ' ' << size.id() << '\n';
        }
    std::map<SVF::Variable, std::vector<SVF::Variable>> components;
    for (const auto& [variable, parent] : parents)
    {
        (void)parent;
        components[root(variable)].push_back(variable);
    }
    SVF::PackedRelationalDomain::Packing packing;
    std::map<SVF::Variable, std::size_t> indices;
    for (auto& [representative, variables] : components)
    {
        indices.emplace(representative, packing.size());
        packing.push_back(std::move(variables));
    }
    relationalPacking_ = std::make_shared<const SVF::PackedRelationalDomain::Packing>(std::move(packing));
    for (const auto& [base, anchor] : bases) objectPacks_.emplace(base, indices.at(root(anchor)));
    adapter_.setObjectRegistration([this](const ObjVar& object, SVF::Variable variable)
    {
        if (variable.type().kind == SVF::NumericKind::IEEEFloat) return;
        const auto* base = svfir->getBaseObject(object.getId());
        const auto found = objectPacks_.find(base);
        if (found == objectPacks_.end()) return;
        SVF::PackedRelationalDomain::registerVariable(relationalPacking_, found->second, variable);
        if (std::getenv("SVF_AE_TRACE_PACK_OFFSETS"))
            SVFUtil::outs() << "AE_PACK_OFFSET base=" << base->getId()
                           << " object=" << object.getId() << " variable=" << variable.id()
                           << " pack=" << found->second << '\n';
    });
    SVFUtil::outs() << "AE_BASE_OBJECT_PACK packs=" << relationalPacking_->size()
                   << " objects=" << objectPacks_.size() << '\n';
    dumpFixedPacking("AE_BASE_PACK");
}

void AbstractInterpretation::selectBoxMayPacks()
{
    std::vector<StatementPackingQuery> demands;
    for (const auto& [key, record] : queryLedger_)
    {
        (void)key;
        const auto id = queryIdentityFields(record).front();
        if (boxQueries_.at(id).outcome == "May")
            demands.push_back({id, icfg->getICFGNode(record.icfgNode),
                record.statement, record.operand ? svfir->getSVFVar(record.operand) : nullptr,
                record.queryKind});
    }
    const auto demand = StatementRelationPacking(
        *svfir, adapter_, *preAnalysis->getPointerAnalysis(), &allocationSizeModel())
        .selectDemand(*relationalPacking_, demands);

    const bool trace = std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY") != nullptr;
    RelationPacking filtered;
    std::map<std::size_t, std::size_t> newIndices;
    for (std::size_t index = 0; index < relationalPacking_->size(); ++index)
    {
        const auto& pack = relationalPacking_->at(index);
        if (demand.packs.count(index))
        {
            newIndices.emplace(index, filtered.size());
            if (trace)
            {
                std::cerr << "AE_BOX_MAY_PACK_MEMBERS " << filtered.size();
                for (auto variable : pack)
                    std::cerr << ' ' << variable.id();
                std::cerr << '\n';
            }
            filtered.push_back(pack);
        }
    }
    for (auto it = objectPacks_.begin(); it != objectPacks_.end();)
        if (const auto index = newIndices.find(it->second); index != newIndices.end())
        {
            it->second = index->second;
            ++it;
        }
        else
            it = objectPacks_.erase(it);
    relationalPacking_ = std::make_shared<const RelationPacking>(std::move(filtered));
    SVFUtil::outs() << "AE_BOX_MAY_PACK packs=" << relationalPacking_->size() << '\n';
    if (std::getenv("SVF_AE_TRACE_ONDEMAND_DEPENDENCIES"))
    {
        for (const auto* point : demand.points)
            std::cerr << "AE_BOX_MAY_POINT " << point->getId() << '\n';
        for (const auto* transfer : demand.transfers)
            std::cerr << "AE_BOX_MAY_TRANSFER " << transfer->getEdgeID() << '\n';
        for (const auto* value : demand.values)
            std::cerr << "AE_BOX_MAY_VALUE " << value->getId() << '\n';
    }
}
