//===- AbstractExecution.cpp -- Abstract Execution---------------------------------//
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
//===----------------------------------------------------------------------===//


//
//  Created on: Jan 10, 2024
//      Author: Xiao Cheng, Jiawei Wang
//

#include "AE/Svfexe/AbstractInterpretation.h"
#include "AE/Core/NumericalDomain.h"
#include "AE/Core/PackedRelationalDomain.h"
#include "AE/Core/PartialRelationalDomain.h"
#include "AE/Svfexe/AbsExtAPI.h"
#include "AE/Svfexe/AllocationSize.h"
#include "AE/Svfexe/ImpactRelationPacking.h"
#include "AE/Svfexe/OhPackedAbstractInterpretation.h"
#include "AE/Svfexe/SparseAbstractInterpretation.h"
#include "AE/Svfexe/VersionedSparseAbstractInterpretation.h"
#include "Graphs/CallGraph.h"
#include "Graphs/SparseObjGraph.h"
#include "MSSA/SVFGBuilder.h"
#include "SVFIR/SVFIR.h"
#include "Util/Options.h"
#include "Util/WorkList.h"
#include "WPA/Andersen.h"
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdlib>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <memory>
#include <set>
#include <sstream>
#include <tuple>
#include <unordered_set>

using namespace SVF;
using namespace SVFUtil;

static std::vector<const ICFGEdge*> orderedIncomingEdges(const ICFGNode* node)
{
    std::vector<const ICFGEdge*> edges(node->getInEdges().begin(),
                                       node->getInEdges().end());
    std::sort(edges.begin(), edges.end(),
              [](const ICFGEdge* lhs, const ICFGEdge* rhs)
    {
        return std::make_tuple(lhs->getSrcID(),
                               lhs->getEdgeKindWithoutMask()) <
               std::make_tuple(rhs->getSrcID(),
                               rhs->getEdgeKindWithoutMask());
    });
    return edges;
}

static const char* queryDetectorName(AEDetector::DetectorKind detector)
{
    switch (detector)
    {
    case AEDetector::BUF_OVERFLOW:
        return "buffer-overflow";
    case AEDetector::NULL_DEREF:
        return "null-dereference";
    case AEDetector::ASSERTION:
        return "assertion";
    case AEDetector::UNKNOWN:
    default:
        return "unknown";
    }
}

static const char* queryOutcomeName(AbstractInterpretation::QueryOutcome outcome)
{
    switch (outcome)
    {
    case AbstractInterpretation::QueryOutcome::Safe:
        return "Safe";
    case AbstractInterpretation::QueryOutcome::May:
        return "May";
    case AbstractInterpretation::QueryOutcome::Unsupported:
        return "Unsupported";
    case AbstractInterpretation::QueryOutcome::Unreachable:
    default:
        return "Unreachable";
    }
}

static unsigned queryOutcomeRank(AbstractInterpretation::QueryOutcome outcome)
{
    switch (outcome)
    {
    case AbstractInterpretation::QueryOutcome::Safe:
        return 1;
    case AbstractInterpretation::QueryOutcome::Unsupported:
        return 2;
    case AbstractInterpretation::QueryOutcome::May:
        return 3;
    case AbstractInterpretation::QueryOutcome::Unreachable:
    default:
        return 0;
    }
}

static std::string queryKey(AEDetector::DetectorKind detector,
                            const ICFGNode* node, const std::string& queryKind, const SVFStmt* site = nullptr)
{
    if (site)
    {
        if (site->getQuerySite().empty())
        {
            assert(false && "detector site lacks LLVM semantic identity");
            std::abort();
        }
        return std::to_string(static_cast<unsigned>(detector)) + ":v2:" +
               site->getQuerySite() + ':' + queryKind;
    }
    if (!node || node->getSemanticSite().empty())
        throw std::invalid_argument("detector node lacks LLVM semantic identity");
    return std::to_string(static_cast<unsigned>(detector)) + ":v2:icfg:" +
           node->getSemanticSite() + ':' + queryKind;
}

static std::string escapeQueryField(const std::string& field)
{
    std::string result;
    result.reserve(field.size());
    for (char character : field)
    {
        switch (character)
        {
        case '\t':
            result += "\\t";
            break;
        case '\n':
            result += "\\n";
            break;
        case '\r':
            result += "\\r";
            break;
        default:
            result += character;
            break;
        }
    }
    return result;
}

SVF::AddressSet AbstractInterpretation::blackHoleAddressSet() const
{
    const auto* object = SVFUtil::dyn_cast<ObjVar>(
                             svfir->getGNode(IRGraph::BlackHole));
    if (!object)
    {
        assert(false && "SVFIR has no BlackHole object");
        std::abort();
    }
    return SVF::AddressSet::singleton(adapter_.location(*object));
}

void AbstractInterpretation::handleGlobalNode()
{
    const ICFGNode* node = icfg->getGlobalICFGNode();
    abstractTrace_.insert_or_assign(node, topState());
    for (const SVFStmt* statement : node->getSVFStmts())
        handleSVFStatement(statement);

    if (const auto* variable = SVFUtil::dyn_cast<ValVar>(
                                   svfir->getGNode(PAG::getPAG()->getBlkPtr())))
        updateValue(variable, SVF::Interval::top(),
                    blackHoleAddressSet(), node);
    // Global initialization executes once. Its GEP properties must not be
    // left as Unreachable merely because no ordinary ICFG visitor runs here.
    for (auto& detector : detectors)
        detector->detect(node);
}

void AbstractInterpretation::initializeObjectValue(
    const ObjVar* object, SVF::Interval& interval, SVF::AddressSet& addresses,
    const ICFGNode* node)
{
    interval = SVF::Interval::bottom();
    addresses = SVF::AddressSet::bottom();
    State& denseState = ensureState(node);


    const BaseObjVar* base = PAG::getPAG()->getBaseObject(object->getId());
    if (intervalPreanalysis_ && ImpactRelationPacking::isExternalObject(base->getId()))
    {
        const auto initialize = [&](const ObjVar* external)
        {
            const auto content = adapter_.contentVariable(*external);
            if (external->getType()->isPointerTy())
                denseState.setAddressSet(content, blackHoleAddressSet());
            else if (SVFUtil::isa<SVFIntegerType>(external->getType()))
                denseState.setInterval(content, unknownInterval(external));
        };
        initialize(object);
        if (object == base)
            for (NodeID id : svfir->getAllFieldsObjVars(base->getId()))
                if (const auto* field = SVFUtil::dyn_cast<ObjVar>(svfir->getGNode(id)))
                    initialize(field);
    }
    if (base->isStack())
    {
        // Fresh payload facets are uninitialized, independently of their
        // physical Box/Address slots (whose missing payload still means Top).
        // A heap allocation site can also represent earlier live allocations;
        // revisiting it must not erase those objects' summarized contents.
        denseState.resetValue(adapter_.contentVariable(*object));
        for (NodeID fieldId : svfir->getAllFieldsObjVars(base->getId()))
        {
            const auto* field = SVFUtil::dyn_cast<ObjVar>(svfir->getGNode(fieldId));
            if (field)
                denseState.resetValue(adapter_.contentVariable(*field));
        }
    }
    if (base->isBlackHoleObj())
    {
        addresses = blackHoleAddressSet();
        return;
    }
    if (base->isConstDataOrConstGlobal() || base->isConstantArray() ||
            base->isConstantStruct())
    {
        if (const auto* integer = SVFUtil::dyn_cast<ConstIntObjVar>(object))
        {
            const auto* type = SVFUtil::dyn_cast<SVFIntegerType>(integer->getType());
            const bool boolean = numericalDomain() != AENumericalDomain::Box && type && type->isBoolean();
            interval = SVF::Interval::singleton(SVF::Rational(
                                                    boolean ? (integer->getSExtValue() != 0 ? 1 : 0) : integer->getSExtValue()));
        }
        else if (const auto* floating =
                     SVFUtil::dyn_cast<ConstFPObjVar>(object))
            interval = SVFIRAdapter::floatingConstant(floating->getFPValue());
        else if (SVFUtil::isa<ConstNullPtrObjVar>(object))
            addresses = SVF::AddressSet::singleton(SVF::Location::null());
        else if (!SVFUtil::isa<GlobalObjVar>(object))
            interval = SVF::Interval::top();
        if (!interval.isBottom() || !addresses.isBottom())
            return;
    }
    addresses = SVF::AddressSet::singleton(adapter_.location(*object));
}

void AbstractInterpretation::initializePackingVocabulary()
{
    std::set<SVF::Variable> vocabulary;
    for (auto it = svfir->begin(); it != svfir->end(); ++it)
    {
        if (const auto* value = SVFUtil::dyn_cast<ValVar>(it->second))
            if (!value->isPointer() && adapter_.contains(*value))
            {
                const auto variable = adapter_.variable(*value);
                if (variable.type().kind != SVF::NumericKind::IEEEFloat)
                    vocabulary.insert(variable);
            }
        // Andersen may create field objects after adapter construction. Bind
        // their content identities before freezing V and initializing states.
        if (const auto* object = SVFUtil::dyn_cast<ObjVar>(it->second))
            if (!object->isPointer())
            {
                const auto content = adapter_.contentVariable(*object);
                if (content.type().kind != SVF::NumericKind::IEEEFloat)
                    vocabulary.insert(content);
            }
    }
    // D-005: Sparrow's Size(a) coordinates belong to V for every policy.
    for (const auto& size : allocationSizeModel().all())
        vocabulary.insert(adapter_.sizeVariable(*size.object));
    relationalVocabulary_ = std::make_shared<const std::vector<SVF::Variable>>(
                                vocabulary.begin(), vocabulary.end());
}

void AbstractInterpretation::initializeProvidedPacking()
{
    if (!packingProvider_)
        throw std::logic_error("the provided packing has already been used");
    initializePackingVocabulary();
    auto provider = std::exchange(packingProvider_, {});
    auto packing = provider({*svfir, adapter_, *relationalVocabulary_});

    std::set<RelationPacking::value_type> uniquePacks;
    std::set<Variable> sparseOwners;
    for (auto& pack : packing)
    {
        std::sort(pack.begin(), pack.end());
        if (pack.empty() || std::adjacent_find(pack.begin(), pack.end()) != pack.end())
            throw std::invalid_argument("each provided pack must be nonempty with distinct coordinates");
        if (!uniquePacks.insert(pack).second)
            throw std::invalid_argument("the provided family contains duplicate packs");
        for (const auto variable : pack)
        {
            if (!std::binary_search(relationalVocabulary_->begin(), relationalVocabulary_->end(), variable))
                throw std::invalid_argument("unknown packing coordinate " + std::to_string(variable.id()));
            if (packSSAEnabled() && !sparseOwners.insert(variable).second)
                throw std::invalid_argument("provided pack-SSA packs must be disjoint");
        }
    }
    relationalPacking_ = std::make_shared<const RelationPacking>(std::move(packing));
}

void AbstractInterpretation::dumpFixedPacking(const char* prefix) const
{
    if (std::getenv("SVF_AE_TRACE_RELATIONAL_POLICY"))
    {
        for (std::size_t pack = 0; pack < relationalPacking_->size(); ++pack)
        {
            SVFUtil::outs() << prefix << "_MEMBERS " << pack;
            for (auto variable : relationalPacking_->at(pack))
                SVFUtil::outs() << ' ' << variable.id();
            SVFUtil::outs() << '\n';
            for (auto variable : relationalPacking_->at(pack))
            {
                const auto* value = adapter_.value(variable);
                const auto* object = adapter_.contentObject(variable);
                const auto* sized = adapter_.sizeObject(variable);
                const SVFVar* origin = value ? static_cast<const SVFVar*>(value) : object ? object : sized;
                SVFUtil::outs() << prefix << "_VARIABLE " << variable.id()
                                << ' ' << (value ? "value" : object ? "content" : "size")
                                << ' ' << origin->getId()
                                << ' ' << static_cast<unsigned>(variable.type().kind)
                                << ' ' << variable.type().floatFormat.exponentBits
                                << ' ' << variable.type().floatFormat.significandBits
                                << ' ' << escapeQueryField(origin->getValueName()) << '\n';
            }
        }
    }
}

void AbstractInterpretation::runOnModule()
{
    using PhaseClock = std::chrono::steady_clock;
    const auto secondsSince = [](PhaseClock::time_point start)
    {
        return std::chrono::duration<double>(PhaseClock::now() - start).count();
    };
    const bool phaseStats = std::getenv("SVF_AE_PHASE_STATS") != nullptr;
    const bool domainStats = std::getenv("SVF_AE_DOMAIN_STATS") != nullptr;
    const auto cpuSince = [](std::clock_t start)
    {
        return double(std::clock() - start) / CLOCKS_PER_SEC;
    };
    double querySeconds = 0.0;
    double queryCpu = 0.0;

    stat->startClk();
    utils = new AbsExtAPI(this);
    const PhaseClock::time_point queryEnumerationStart = PhaseClock::now();
    const auto queryEnumerationCpu = std::clock();
    enumerateQueries();
    if (usesBuiltInOnDemand() && !prepareBoxMayDemand())
    {
        stat->endClk();
        return;
    }
    querySeconds += secondsSince(queryEnumerationStart);
    queryCpu += cpuSince(queryEnumerationCpu);
    /// collect checkpoint
    utils->collectCheckPoint();

    const auto packingStart = PhaseClock::now();
    const auto packingCpu = std::clock();
    bool lateFieldsUseBox = true;
    if (providedPacking_)
        initializeProvidedPacking();
    else
        lateFieldsUseBox = initializeBuiltInPacking();
    const bool duet = relationalPolicy() == DuetPackedRelational;
    const bool publishedFixed = !providedPacking_ &&
        (duet || relationalPolicy() == SpePackedRelational);
    initializeExecutionPolicy();
    if (providedPacking_)
    {
        dumpFixedPacking("AE_POLICY_EXEC_PACK");
        SVFUtil::outs() << "AE_POLICY_EXEC policy=provided-pack solver="
                       << (packSSAEnabled() ? "pack-ssa" : "dense")
                       << " backend=octagon field_fallback=box\n";
    }
    if (publishedFixed)
    {
        dumpFixedPacking("AE_POLICY_EXEC_PACK");
        SVFUtil::outs() << (duet ? "AE_POLICY_EXEC policy=duet12 solver=pack-ssa"
                                : "AE_POLICY_EXEC policy=spe17-pack solver=dense")
                       << " backend=octagon field_fallback=box\n";
    }
    if (std::getenv("SVF_AE_VERIFY_PACKED_EXECUTOR"))
    {
        const auto probe = makeNumericalDomain(false);
        if (!probe->isDomain<SVF::PackedRelationalDomain>())
        {
            assert(false && "requested packed executor verification failed");
            std::abort();
        }
        SVFUtil::outs() << "AE_PACKING_EXECUTOR packed\n";
    }
    if (providedPacking_ || publishedFixed || relationalPolicy() == SyntaxPackedRelational ||
            relationalPolicy() == ClosurePackedRelational ||
            relationalPolicy() == ImpactPackedRelational ||
            relationalPolicy() == LearnedPackedRelational)
        SVFUtil::outs() << "AE_PACKING_SECONDS " << secondsSince(packingStart) << '\n';
    if (phaseStats)
        SVFUtil::outs() << "AE_PACKING_CPU_SECONDS " << cpuSince(packingCpu) << '\n';
    if (std::getenv("SVF_AE_PACK_ONLY"))
    {
        SVFUtil::outs() << "AE_PACK_ONLY complete\n";
        SVFUtil::outs().flush();
        stat->endClk();
        return;
    }

    if (domainStats)
        SVF::NumericalDomain::beginTelemetry();
    const PhaseClock::time_point solveStart = PhaseClock::now();
    const auto solveCpuStart = std::clock();
    // Diagnostic for D-005 item 3: objects whose content coordinate is
    // created during the analysis (outside the frozen V).
    const SVF::Variable frozenFrontier = adapter_.syntheticVariable(SVF::NumericType::integer());
    // Published policies leave fields outside the frozen family in Box.
    if (numericalDomain() != AENumericalDomain::Box && !lateFieldsUseBox)
        adapter_.freezeRuntimeFields();
    analyse();
    const double solveSeconds = secondsSince(solveStart);
    const double solveCpu = cpuSince(solveCpuStart);
    if (phaseStats && sparsity() == AbstractInterpretation::Dense)
    {
        std::size_t edgeBlocks = 0;
        for (const auto& [block, edgeTransfer] : phiEdgeBlocks_)
        {
            (void)block;
            edgeBlocks += edgeTransfer;
        }
        SVFUtil::outs() << "AE_PHI_EDGE blocks=" << edgeBlocks
                        << " fallback_blocks=" << phiEdgeFallbackBlocks_ << '\n';
    }
    if (std::getenv("SVF_AE_TRACE_RUNTIME_FIELDS"))
    {
        std::size_t created = 0, fields = 0, stringBases = 0;
        std::map<const BaseObjVar*, std::size_t> bases;
        for (const ObjVar* object : adapter_.objectsRegisteredAfter(frozenFrontier))
        {
            ++created;
            fields += SVFUtil::isa<GepObjVar>(object);
            ++bases[svfir->getBaseObject(object->getId())];
        }
        for (const auto& [base, count] : bases)
        {
            (void)count;
            stringBases += base && base->isConstDataOrConstGlobal();
        }
        SVFUtil::outs() << "AE_RUNTIME_FIELDS summarized=" << adapter_.summarizedFieldCount()
                        << " summaries=" << adapter_.summaryCount()
                        << " created=" << created << " fields=" << fields
                        << " bases=" << bases.size() << " constant_bases=" << stringBases << '\n';
        std::size_t shown = 0;
        for (const auto& [base, count] : bases)
            if (base && shown++ < 8)
                SVFUtil::outs() << "AE_RUNTIME_FIELDS_BASE " << base->getName() << " count=" << count
                                << " const=" << base->isConstDataOrConstGlobal()
                                << " heap=" << base->isHeap() << '\n';
    }
    if (domainStats)
    {
        const SVF::NumericalTelemetry operations =
            SVF::NumericalDomain::endTelemetry();
        std::size_t activeProperties = 0;
        std::size_t totalSupport = 0;
        std::size_t maximumSupport = 0;
        std::size_t components = 0;
        std::size_t maximumComponent = 0;
        const auto measure = [&](const State& property)
        {
            const SVF::NumericalDomain& numerical = property.numerical();
            if (numerical.isBottom())
                return;
            ++activeProperties;
            const std::vector<SVF::Variable> support =
                numerical.supportVariables();
            totalSupport += support.size();
            maximumSupport = std::max(maximumSupport, support.size());
            if (numerical.isDomain<SVF::BoxDomain>())
            {
                components += support.size();
                if (!support.empty())
                    maximumComponent = std::max<std::size_t>(
                                           maximumComponent, 1);
                return;
            }
            std::set<SVF::Variable> remaining(support.begin(), support.end());
            while (!remaining.empty())
            {
                const std::vector<SVF::Variable> component =
                    numerical.relationalClosure({*remaining.begin()});
                ++components;
                maximumComponent = std::max(maximumComponent,
                                            component.size());
                for (SVF::Variable variable : component)
                    remaining.erase(variable);
            }
        };
        for (const auto& [node, property] : abstractTrace_)
        {
            (void)property;
            measure(state(node));
        }
        if (const SVF::AbstractDomain* carrier = getScalarAbstractState())
            measure(static_cast<const State&>(*carrier));
        SVFUtil::outs()
                << "AE_DOMAIN_STATS flow_states=" << abstractTrace_.size()
                << " active_properties=" << activeProperties
                << " total_support=" << totalSupport
                << " max_support=" << maximumSupport
                << " components=" << components
                << " max_component=" << maximumComponent
                << " closure_calls=" << operations.relationalClosureCalls
                << " closure_exports="
                << operations.relationalClosureConstraintExports
                << " closure_indexed="
                << operations.relationalClosureIndexedQueries
                << " join_calls=" << operations.joinCalls
                << " widen_calls=" << operations.wideningCalls
                << " narrow_calls=" << operations.narrowingCalls << '\n';
        if (relationalPolicy() != WholeRelational)
            SVFUtil::outs()
                    << "AE_PARTIAL_RELATIONAL_STATS inside_ops="
                    << operations.partialInsideOperations
                    << " fallback_ops="
                    << operations.partialFallbackOperations
                    << " projections=" << operations.partialProjections
                    << '\n';
    }
    if (unknownTargetTelemetryEnabled_)
    {
        const UnknownTargetTelemetry& telemetry = unknownTargetTelemetry_;
        SVFUtil::outs()
                << "AE_UNKNOWN_TARGET_STATS loads=" << telemetry.loads
                << " stores=" << telemetry.stores
                << " store_cells_visited=" << telemetry.storeCellsVisited
                << " sparse_definition_cells_visited="
                << telemetry.sparseDefinitionCellsVisited << '\n';
    }
    utils->checkPointAllSet();
    stat->endClk();
    stat->finializeStat();
    if (Options::PStat())
        stat->performStat();
    const PhaseClock::time_point queryReportStart = PhaseClock::now();
    const auto queryReportCpu = std::clock();
    for (auto& detector : detectors)
        detector->reportBug();
    writeQueryLedger();
    querySeconds += secondsSince(queryReportStart);
    queryCpu += cpuSince(queryReportCpu);
    const PhaseClock::time_point postStart = PhaseClock::now();
    const auto postCpu = std::clock();
    verifyPostFixpoint();
    if (usesBuiltInOnDemand())
    {
        const auto relational = readCertifiedQueries(queryLedgerPath(), true);
        writeBoxMayLedger(&relational);
        SVFUtil::outs() << "AE_BOX_MAY status=complete\n";
    }
    else if (strictQueryCoverage())
        readCertifiedQueries(queryLedgerPath(), true);
    const double postSeconds = secondsSince(postStart);
    if (phaseStats)
        SVFUtil::outs() << std::defaultfloat << std::setprecision(9)
                        << "AE_PHASE_TIMES ai_s=" << solveSeconds
                        << " query_s=" << querySeconds
                        << " post_s=" << postSeconds
                        << " ai_cpu_s=" << solveCpu << " query_cpu_s=" << queryCpu
                        << " post_cpu_s=" << cpuSince(postCpu) << '\n';
    // L4 export runs only after every timed phase has been reported, so it
    // cannot change packing, analysis, query or Post timings.
    if (const char* invariantPath = std::getenv("SVF_AE_L4_STATES"))
    {
        SVFUtil::outs().flush();
        const PhaseClock::time_point invariantStart = PhaseClock::now();
        writeInvariantStates(invariantPath);
        SVFUtil::outs() << "AE_L4_SECONDS " << secondsSince(invariantStart) << '\n';
        SVFUtil::outs().flush();
    }
}

namespace
{
std::string invariantBoundText(const SVF::Bound& bound)
{
    if (bound.isMinusInfinity())
        return "-inf";
    if (bound.isPlusInfinity())
        return "+inf";
    return (bound.isStrict() ? "s" : "") + bound.value().toString();
}

/// Whether a two-variable constraint `e op 0` already follows from the
/// interval projection of the same state.
bool impliedByIntervals(const SVF::LinearConstraint& constraint,
                        const SVF::NumericalDomain& numerical)
{
    const SVF::LinearExpression& expression = constraint.expression();
    bool lowerFinite = true, upperFinite = true;
    SVF::Rational lower = expression.constant(), upper = expression.constant();
    for (const auto& [variable, coefficient] : expression.terms())
    {
        const SVF::Interval range = numerical.bound(variable);
        const SVF::Bound& forUpper = coefficient.sign() > 0 ? range.upper() : range.lower();
        const SVF::Bound& forLower = coefficient.sign() > 0 ? range.lower() : range.upper();
        if (forUpper.isFinite())
            upper += coefficient * forUpper.value();
        else
            upperFinite = false;
        if (forLower.isFinite())
            lower += coefficient * forLower.value();
        else
            lowerFinite = false;
    }
    const SVF::Rational zero(std::int64_t{0});
    switch (constraint.kind())
    {
    case SVF::ConstraintKind::LessEqual:
        return upperFinite && upper <= zero;
    case SVF::ConstraintKind::LessThan:
        return upperFinite && upper < zero;
    case SVF::ConstraintKind::GreaterEqual:
        return lowerFinite && zero <= lower;
    case SVF::ConstraintKind::GreaterThan:
        return lowerFinite && zero < lower;
    case SVF::ConstraintKind::Equal:
        return upperFinite && lowerFinite && upper <= zero && zero <= lower;
    case SVF::ConstraintKind::NotEqual:
        return true;
    }
    return true;
}
} // namespace

void AbstractInterpretation::writeInvariantStates(const std::string& path) const
{
    std::ofstream output(path, std::ios::out | std::ios::trunc);
    if (!output)
        throw std::runtime_error("cannot open AE invariant state file: " + path);
    std::set<NodeID> nodes;
    for (const auto& [key, record] : queryLedger_)
    {
        (void)key;
        nodes.insert(record.icfgNode);
    }
    const auto variableKey = [&](SVF::Variable variable) -> std::string
    {
        if (const ValVar* value = adapter_.value(variable))
            return "v\t" + std::to_string(value->getId()) + "\t-";
        if (const ObjVar* object = adapter_.contentObject(variable))
        {
            if (const auto* field = SVFUtil::dyn_cast<GepObjVar>(object))
                return "f\t" + std::to_string(field->getBaseNode()) + '\t' +
                std::to_string(field->getConstantFieldIdx());
            return "o\t" + std::to_string(object->getId()) + "\t-";
        }
        if (const ObjVar* object = adapter_.sizeObject(variable))
            return "s\t" + std::to_string(object->getId()) + "\t-";
        return "";
    };
    output << "#l4-v2\tN node status support exported unnamed finite_bounds nontrivial related"
           "\tV node facet svf field lower upper\tU facet svf field (fixed vocabulary)\n";
    // The fixed vocabulary V is frozen before analysis; fields created later
    // (for example modelled array bytes) are outside every pack.
    if (relationalVocabulary_)
        for (SVF::Variable variable : *relationalVocabulary_)
        {
            const std::string key = variableKey(variable);
            if (!key.empty())
                output << "U\t" << key << '\n';
        }
    for (NodeID id : nodes)
    {
        const auto found = abstractTrace_.find(icfg->getICFGNode(id));
        if (found == abstractTrace_.end())
        {
            output << "N\t" << id << "\tmissing\n";
            continue;
        }
        const SVF::NumericalDomain& numerical = found->second.numerical();
        if (numerical.isBottom())
        {
            output << "N\t" << id << "\tbottom\n";
            continue;
        }
        std::size_t support = 0, exported = 0, unnamed = 0, finiteBounds = 0;
        std::ostringstream rows;
        for (SVF::Variable variable : numerical.supportVariables())
        {
            if (variable.type().kind == SVF::NumericKind::IEEEFloat)
                continue;
            ++support;
            const std::string key = variableKey(variable);
            if (key.empty())
            {
                ++unnamed;
                continue;
            }
            const SVF::Interval range = numerical.bound(variable);
            if (range.isTop())
                continue;
            finiteBounds += range.lower().isFinite() + range.upper().isFinite();
            ++exported;
            rows << "V\t" << id << '\t' << key << '\t'
                 << invariantBoundText(range.lower()) << '\t'
                 << invariantBoundText(range.upper()) << '\n';
        }
        std::size_t nontrivial = 0;
        std::set<SVF::Variable> related;
        if (!numerical.isDomain<SVF::BoxDomain>())
            for (const SVF::LinearConstraint& constraint : numerical.toConstraints())
            {
                const auto& terms = constraint.expression().terms();
                if (terms.size() != 2 || impliedByIntervals(constraint, numerical))
                    continue;
                ++nontrivial;
                for (const auto& [variable, coefficient] : terms)
                {
                    (void)coefficient;
                    related.insert(variable);
                }
            }
        output << "N\t" << id << "\tstate\t" << support << '\t' << exported << '\t'
               << unnamed << '\t' << finiteBounds << '\t' << nontrivial << '\t'
               << related.size() << '\n' << rows.str();
    }
}

bool AbstractInterpretation::strictQueryCoverage() const
{
    return Options::AEVerifyQueryCoverage() || usesBuiltInOnDemand();
}

std::string AbstractInterpretation::queryLedgerPath() const
{
    return Options::AEQueryLedgerFile() + (usesBuiltInOnDemand() ? ".octagon" : "");
}

bool AbstractInterpretation::queryLedgerEnabled() const
{
    return !intervalPreanalysis_ && !Options::AEQueryLedgerFile().empty();
}

void AbstractInterpretation::enumerateQueries()
{
    if (!queryLedgerEnabled())
        return;
    if (Options::AEQueryInputID().empty())
    {
        assert(false && "-ae-query-input-id is required with -ae-query-ledger");
        std::abort();
    }
    for (auto& detector : detectors)
        detector->enumerateQueries();
    enumerateStandardAssertionQueries();
}

namespace
{
bool isStandardAssertionFailure(const CallICFGNode* call)
{
    const FunObjVar* function = call ? call->getCalledFunction() : nullptr;
    if (!function)
        return false;
    const std::string name = function->getName();
    return name == "__assert_fail" || name == "__assert_rtn" ||
           name == "__assert_func" || name == "__assert2" ||
           (Options::AESVComp() &&
            (name == "reach_error" || name == "__VERIFIER_error"));
}

bool isDirectSVFAssertion(const CallICFGNode* call)
{
    const FunObjVar* function = call ? call->getCalledFunction() : nullptr;
    return function && function->getName() == "svf_assert" &&
           call->arg_size() >= 1;
}
} // namespace

void AbstractInterpretation::enumerateStandardAssertionQueries()
{
    for (auto iterator = icfg->begin(); iterator != icfg->end(); ++iterator)
    {
        const auto* call = SVFUtil::dyn_cast<CallICFGNode>(iterator->second);
        if (isStandardAssertionFailure(call))
            registerQuery(AEDetector::ASSERTION, call, nullptr,
                          "standard-assert-failure");
        else if (isDirectSVFAssertion(call))
            registerQuery(AEDetector::ASSERTION, call, call->getArgument(0),
                          "assert-condition");
    }
}

bool AbstractInterpretation::isAssertionTrue(const ValVar* condition,
        const ICFGNode* node)
{
    const SVF::Interval value = getInterval(condition, node);
    if (value == SVF::Interval::singleton(SVF::Rational(1)))
        return true;
    // SVF sign-extends literal i1 true to -1, while comparison transfers use
    // 1. Both encode the set bit. Do not accept -1 for wider integer helpers.
    const auto* type = SVFUtil::dyn_cast<SVFIntegerType>(condition->getType());
    return type && type->isBoolean() &&
           value == SVF::Interval::singleton(SVF::Rational(-1));
}

void AbstractInterpretation::recordReachedAssertion(
    const CallICFGNode* call)
{
    if (isStandardAssertionFailure(call))
    {
        recordQuery(AEDetector::ASSERTION, call, nullptr,
                    "standard-assert-failure", QueryOutcome::May,
                    "assertion failure block is abstractly reachable");
    }
    else if (isDirectSVFAssertion(call))
    {
        const ValVar* condition = call->getArgument(0);
        const bool safe = isAssertionTrue(condition, call);
        recordQuery(AEDetector::ASSERTION, call, condition,
                    "assert-condition", safe ? QueryOutcome::Safe
                    : QueryOutcome::May,
                    safe ? "assertion condition is definitely true"
                    : "assertion condition may be false");
    }
}

void AbstractInterpretation::registerQuery(
    AEDetector::DetectorKind detector, const ICFGNode* node,
    const SVFVar* operand, const std::string& queryKind, const SVFStmt* site)
{
    if (!queryLedgerEnabled())
        return;
    if (!node)
    {
        assert(false && "AE query has no ICFG node");
        std::abort();
    }

    QueryRecord record;
    record.detector = detector;
    record.icfgNode = node->getId();
    record.operand = operand ? operand->getId() : 0;
    record.queryKind = queryKind;
    record.function = node->getFun() ? node->getFun()->getName() : "<global>";
    record.sourceLocation = node->getSourceLoc();
    record.semanticSite = site ? site->getQuerySite()
                          : "icfg:" + node->getSemanticSite();
    record.statement = site;
    auto inserted = queryLedger_.emplace(queryKey(detector, node, queryKind, site),
                                         std::move(record));
    if (!inserted.second &&
            (inserted.first->second.statement != site ||
             inserted.first->second.icfgNode != node->getId() ||
             inserted.first->second.operand != (operand ? operand->getId() : 0)))
        throw std::invalid_argument("duplicate detector semantic query: " +
                                    inserted.first->second.semanticSite + ':' + queryKind);
}

void AbstractInterpretation::recordQuery(
    AEDetector::DetectorKind detector, const ICFGNode* node,
    const SVFVar* operand, const std::string& queryKind, QueryOutcome outcome,
    const std::string& reason, const SVFStmt* site)
{
    if (!queryLedgerEnabled())
        return;
    const auto key = queryKey(detector, node, queryKind, site);
    if (strictQueryCoverage() && !queryLedger_.count(key))
        throw std::runtime_error("observation outside AE query inventory: " + key);
    registerQuery(detector, node, operand, queryKind, site);
    QueryRecord& record = queryLedger_.at(key);
    record.observed = true;
    // A Safe query keeps the relational-size tag if any visit needed it.
    const bool keepRelational = outcome == QueryOutcome::Safe &&
                                record.outcome == QueryOutcome::Safe &&
                                record.reason.find("[relational-size]") != std::string::npos;
    if (queryOutcomeRank(outcome) >= queryOutcomeRank(record.outcome) && !keepRelational)
    {
        record.outcome = outcome;
        record.reason = reason;
    }
}

void AbstractInterpretation::writeQueryLedger()
{
    if (!queryLedgerEnabled())
        return;
    writeQueryLedgerTo(queryLedgerPath() + ".iterations.tsv");
    // Iteration history can retain a May from before pointer/size widening.
    // Report the converged solver states; Post reconstructs them independently.
    recheckQueriesOnFinalStates(abstractTrace_, queryLedgerPath(), true);
}

void AbstractInterpretation::recheckQueriesOnFinalStates(
    Map<const ICFGNode*, State>& finals, const std::string& path, bool readSolverStates)
{
    if (!queryLedgerEnabled())
        return;
    const Map<std::string, QueryRecord> saved = queryLedger_;
    for (auto& [key, record] : queryLedger_)
    {
        (void)key;
        record.outcome = QueryOutcome::Unreachable;
        record.reason = "recheck: no Post final state";
    }
    std::vector<std::unique_ptr<AEDetector>> fresh;
    for (const auto& detector : detectors)
    {
        if (detector->getKind() == AEDetector::BUF_OVERFLOW)
            fresh.push_back(std::make_unique<BufOverflowDetector>());
        else if (detector->getKind() == AEDetector::NULL_DEREF)
            fresh.push_back(std::make_unique<NullptrDerefDetector>());
    }
    std::vector<const ICFGNode*> nodes;
    for (const auto& [node, state] : finals)
    {
        (void)state;
        nodes.push_back(node);
    }
    std::sort(nodes.begin(), nodes.end(),
              [](const ICFGNode* a, const ICFGNode* b)
    {
        return a->getId() < b->getId();
    });
    recheckStates_ = readSolverStates ? nullptr : &finals;
    // Pass 1 rebuilds detector side tables (gep offsets) from the final
    // states; pass 2 records the outcomes.
    for (int pass = 0; pass < 2; ++pass)
    {
        if (pass == 1)
            for (auto& [key, record] : queryLedger_)
            {
                (void)key;
                record.observed = false;
                record.outcome = QueryOutcome::Unreachable;
                record.reason = "recheck: no Post final state";
            }
        for (const ICFGNode* node : nodes)
        {
            if ((readSolverStates ? state(node) : finals.at(node)).isBottom())
                continue;
            if (const auto* call = SVFUtil::dyn_cast<CallICFGNode>(node))
                recordReachedAssertion(call);
            for (auto& detector : fresh)
                if (pass == 0)
                    detector->prepare(node);
                else
                    detector->detect(node);
            if (readSolverStates)
                finalizeAbstractState(node);
        }
    }
    if (strictQueryCoverage())
        for (const auto& [key, record] : queryLedger_)
        {
            const auto* node = icfg->getICFGNode(record.icfgNode);
            const auto found = finals.find(node);
            if (!record.observed && found != finals.end() &&
                    !(readSolverStates ? state(node) : found->second).isBottom())
                throw std::runtime_error("reachable AE query has no observation: " + key);
        }
    recheckStates_ = nullptr;
    writeQueryLedgerTo(path);
    queryLedger_ = saved;
}

static constexpr const char* queryLedgerHeader =
    "query_id\tinput_id\tdetector\tfunction\tsource_location\t"
    "icfg_node\toperand\tquery_kind\toutcome\treason\tsemantic_site";

std::vector<std::string> AbstractInterpretation::queryIdentityFields(
    const QueryRecord& record) const
{
    if (record.semanticSite.empty())
        throw std::logic_error("query ledger lacks semantic identity");
    const std::string input = escapeQueryField(Options::AEQueryInputID());
    const std::string detector = queryDetectorName(record.detector);
    const std::string identity = input + ":v2:" + detector + ':' +
                                 record.semanticSite + ':' + record.queryKind;
    return {escapeQueryField(identity), input, detector,
            escapeQueryField(record.function), escapeQueryField(record.sourceLocation),
            std::to_string(record.icfgNode), std::to_string(record.operand),
            escapeQueryField(record.queryKind), escapeQueryField(record.semanticSite)};
}

void AbstractInterpretation::writeQueryLedgerTo(const std::string& path) const
{
    std::ofstream output(path, std::ios::out | std::ios::trunc);
    if (!output)
        throw std::runtime_error("cannot open AE query ledger: " + path);

    output << queryLedgerHeader << '\n';
    std::vector<const QueryRecord*> records;
    records.reserve(queryLedger_.size());
    for (const auto& [key, record] : queryLedger_)
    {
        (void)key;
        records.push_back(&record);
    }
    std::sort(records.begin(), records.end(),
              [](const QueryRecord* left, const QueryRecord* right)
    {
        return std::make_tuple(left->detector, left->semanticSite, left->queryKind) <
               std::make_tuple(right->detector, right->semanticSite, right->queryKind);
    });
    for (const auto* record : records)
    {
        const auto fields = queryIdentityFields(*record);
        for (std::size_t index = 0; index < 8; ++index)
            output << fields[index] << '\t';
        output << queryOutcomeName(record->outcome) << '\t'
               << escapeQueryField(
                   record->outcome == QueryOutcome::Unreachable &&
                   record->reason.empty()
                   ? "not reached from configured analysis entries"
                   : record->reason) << '\t' << fields.back() << '\n';
    }
    output.close();
    if (!output)
        throw std::runtime_error("failed to write AE query ledger: " + path);
}

AbstractInterpretation::CertifiedQueries AbstractInterpretation::readCertifiedQueries(
    const std::string& path, bool sameRun) const
{
    std::map<std::string, std::vector<std::string>> expected;
    for (const auto& [key, record] : queryLedger_)
    {
        (void)key;
        auto fields = queryIdentityFields(record);
        const auto id = fields.front();
        if (!expected.emplace(id, std::move(fields)).second)
            throw std::runtime_error("duplicate exported AE query identity: " + id);
    }
    const auto read = [&](const std::string& file)
    {
        std::ifstream input(file);
        const auto invalid = [&file](const std::string& reason)
        {
            return std::runtime_error("invalid AE query ledger " + file + ": " + reason);
        };
        std::string line;
        if (!std::getline(input, line) || line != queryLedgerHeader)
            throw invalid("missing or invalid header");
        CertifiedQueries result;
        while (std::getline(input, line))
        {
            std::vector<std::string> fields;
            std::istringstream row(line);
            std::string field;
            while (std::getline(row, field, '\t'))
                fields.push_back(field);
            if (fields.size() != 11)
                throw invalid("malformed row");
            const auto found = expected.find(fields[0]);
            if (found == expected.end())
                throw invalid("unexpected query " + fields[0]);
            const auto& identity = found->second;
            for (std::size_t index = 1; index < 8; ++index)
                if ((sameRun || (index != 5 && index != 6)) &&
                        fields[index] != identity[index])
                    throw invalid("mismatched query metadata " + fields[0]);
            if (fields[10] != identity.back() ||
                    (fields[8] != "Safe" && fields[8] != "May" &&
                     fields[8] != "Unreachable" && fields[8] != "Unsupported"))
                throw invalid("invalid site or outcome for " + fields[0]);
            if (!result.emplace(fields[0], CertifiedQuery{line, fields[8]}).second)
                throw invalid("duplicate query " + fields[0]);
        }
        if (input.bad() || result.size() != expected.size())
            throw invalid("incomplete query inventory");
        return result;
    };
    const auto ledger = read(path);
    const auto rechecked = read(path + ".recheck.tsv");
    for (const auto& [id, query] : ledger)
        if (query.outcome != rechecked.at(id).outcome)
            throw std::runtime_error("independent final reevaluation disagrees: " + id);
    return ledger;
}

void AbstractInterpretation::writeBoxMayLedger(const CertifiedQueries* relational) const
{
    const auto path = Options::AEQueryLedgerFile();
    const auto staging = path + ".partial";
    std::ofstream output(staging, std::ios::out | std::ios::trunc);
    output << queryLedgerHeader << "\torigin\n";
    for (const auto& [id, box] : boxQueries_)
    {
        const bool refined = relational && box.outcome == "May";
        output << (refined ? relational->at(id).row : box.row)
               << (refined ? "\tOctagon\n" : "\tBox\n");
    }
    output.close();
    if (!output)
        throw std::runtime_error("failed to write Box-May ledger: " + staging);
    std::filesystem::rename(staging, path);
}

bool AbstractInterpretation::prepareBoxMayDemand()
{
    boxQueries_ = readCertifiedQueries(Options::AEQueryLedgerFile() + ".box", false);
    writeBoxMayLedger(nullptr);
    const auto may = std::count_if(boxQueries_.begin(), boxQueries_.end(),
        [](const auto& entry) { return entry.second.outcome == "May"; });
    if (may)
        SVFUtil::outs() << "AE_BOX_MAY status=box-certified may=" << may << '\n';
    else
        SVFUtil::outs() << "AE_BOX_MAY status=skipped-octagon may=0\n";
    SVFUtil::outs().flush();
    return may != 0;
}

AbstractInterpretation::AbstractInterpretation(bool intervalPreanalysis)
    : intervalPreanalysis_(intervalPreanalysis), adapter_(*PAG::getPAG()),
      unknownTargetTelemetryEnabled_(
          std::getenv("SVF_AE_UNKNOWN_TARGET_STATS") != nullptr)
{
    stat = new AEStat(this);
    // Run Andersen's pointer analysis and build WTO
    svfir = PAG::getPAG();
    icfg = svfir->getICFG();
    preAnalysis = new AEWTO(svfir, icfg);
    callGraph = preAnalysis->getCallGraph();
    icfg->updateCallGraph(callGraph);
    preAnalysis->initWTO();
}

AbstractInterpretation::AENumericalDomain AbstractInterpretation::numericalDomain() const
{
    return intervalPreanalysis_ ? Box : static_cast<AENumericalDomain>(Options::AEDomain());
}

AbstractInterpretation::AESparsity AbstractInterpretation::sparsity() const
{
    return intervalPreanalysis_ ? Dense : static_cast<AESparsity>(Options::AESparsity());
}

AbstractInterpretation::AERelationalPolicy AbstractInterpretation::relationalPolicy() const
{
    return intervalPreanalysis_ ? WholeRelational
           : static_cast<AERelationalPolicy>(Options::AERelationalPolicy());
}

bool AbstractInterpretation::packSSAEnabled() const
{
    return !intervalPreanalysis_ && (providedPacking_ ? sparsity() != Dense : usesPackSSA());
}

std::unique_ptr<AbstractInterpretation> AbstractInterpretation::intervalPreanalysis()
{
    std::unique_ptr<AbstractInterpretation> analysis(new AbstractInterpretation(true));
    analysis->utils = new AbsExtAPI(analysis.get());
    analysis->stat->startClk();
    analysis->analyse();
    analysis->stat->endClk();
    return analysis;
}

const AbstractInterpretation::State* AbstractInterpretation::intervalInputState(
    const ICFGNode* node) const
{
    const auto found = intervalInputs_.find(node);
    return hasAbsState(node) && found != intervalInputs_.end() && !found->second.isBottom()
           ? &found->second : nullptr;
}

const AbstractInterpretation::State* AbstractInterpretation::intervalInputState(
    const SVFStmt* statement) const
{
    const auto found = intervalStatementInputs_.find(statement);
    return hasAbsState(statement->getICFGNode()) &&
           found != intervalStatementInputs_.end() && !found->second.isBottom()
           ? &found->second : nullptr;
}

SVF::Variable AbstractInterpretation::intervalOffsetVariable(const SVFVar* variable) const
{
    const auto found = intervalOffsets_.find(variable->getId());
    if (found != intervalOffsets_.end())
        return found->second;
    const auto symbol = adapter_.syntheticVariable(SVF::NumericType::integer());
    intervalOffsets_.emplace(variable->getId(), symbol);
    return symbol;
}

SVF::Interval AbstractInterpretation::intervalPointerOffset(
    const SVFVar* variable, const State& state) const
{
    const auto found = intervalOffsets_.find(variable->getId());
    if (found == intervalOffsets_.end())
        return SVF::Interval::top();
    const auto result = state.interval(found->second);
    return result.isBottom() ? SVF::Interval::top() : result;
}

void AbstractInterpretation::updateIntervalPointerOffsets(
    const SVFStmt* statement, const State& before)
{
    const auto* node = statement->getICFGNode();
    State& after = ensureState(node);
    if (after.isBottom())
        return;
    const auto pointer = [](const SVFVar* variable)
    {
        const auto* returned = SVFUtil::dyn_cast<RetValPN>(variable);
        return returned ? returned->getFunction()->getReturnType()->isPointerTy()
                        : variable->isPointer();
    };
    const auto assign = [&](const SVFVar* variable, const SVF::Interval& offset)
    {
        after.setInterval(intervalOffsetVariable(variable), offset);
    };
    const auto range = [&](const SVFVar* rawValue)
    {
        const auto* value = SVFUtil::dyn_cast<ValVar>(rawValue);
        if (!value)
            return SVF::Interval::top();
        if (const auto* constant = SVFUtil::dyn_cast<ConstIntValVar>(value))
            return SVF::Interval::singleton(SVF::Rational(constant->getSExtValue()));
        if (!adapter_.contains(*value))
            return SVF::Interval::top();
        const auto interval = before.interval(adapter_.variable(*value));
        return interval.isBottom() ? SVF::Interval::top() : interval;
    };
    if (const auto* address = SVFUtil::dyn_cast<AddrStmt>(statement))
        assign(address->getLHSVar(), SVF::Interval::singleton(SVF::Rational(0)));
    else if (const auto* copy = SVFUtil::dyn_cast<CopyStmt>(statement))
    {
        if (pointer(copy->getLHSVar()) || pointer(copy->getRHSVar()))
            assign(copy->getLHSVar(), intervalPointerOffset(copy->getRHSVar(), before));
    }
    else if (const auto* gep = SVFUtil::dyn_cast<GepStmt>(statement))
    {
        // External-API field edges carry flattened indices without byte types.
        const auto offsets = gep->getOffsetVarAndGepTypePairVec();
        if (std::any_of(offsets.begin(), offsets.end(),
                        [](const auto& part) { return !part.second; }))
        {
            assign(gep->getLHSVar(), SVF::Interval::top());
            return;
        }
        SVF::Interval delta = SVF::Interval::singleton(SVF::Rational(0));
        if (gep->isConstantOffset())
            delta = SVF::Interval::singleton(SVF::Rational(gep->accumulateConstantByteOffset()));
        else for (const auto& part : offsets)
        {
            if (const auto* structure = SVFUtil::dyn_cast<SVFStructType>(part.second))
                delta = SVF::add(delta, SVF::Interval::singleton(SVF::Rational(
                    gep->getAccessPath().getStructFieldOffset(part.first, structure))));
            else if (SVFUtil::isa<SVFArrayType>(part.second) ||
                     SVFUtil::isa<SVFPointerType>(part.second))
            {
                const auto* array = SVFUtil::dyn_cast<SVFArrayType>(part.second);
                const auto width = array ? array->getTypeOfElement()->getByteSize()
                    : gep->getAccessPath().gepSrcPointeeType()->getByteSize();
                delta = SVF::add(delta, SVF::multiply(range(part.first),
                    SVF::Interval::singleton(SVF::Rational(width))));
            }
            else delta = SVF::Interval::top();
        }
        assign(gep->getLHSVar(), SVF::add(intervalPointerOffset(gep->getRHSVar(), before), delta));
    }
    else if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(statement))
    {
        if (!pointer(load->getLHSVar()))
            return;
        const auto addresses = before.addressSet(adapter_.variable(*load->getRHSVar()));
        SVF::Interval result = SVF::Interval::bottom();
        if (addresses.isFinite())
            for (const auto location : addresses.locations())
            {
                const auto* object = objectAt(location);
                result.joinWith(object ? intervalPointerOffset(object, before) : SVF::Interval::top());
            }
        assign(load->getLHSVar(), result.isBottom() ? SVF::Interval::top() : result);
    }
    else if (const auto* store = SVFUtil::dyn_cast<StoreStmt>(statement))
    {
        const auto addresses = before.addressSet(adapter_.variable(*store->getLHSVar()));
        if (!addresses.isFinite())
        {
            std::vector<SVF::Variable> forgotten;
            for (const auto& entry : intervalOffsets_)
                if (SVFUtil::isa<ObjVar>(svfir->getSVFVar(entry.first)))
                    forgotten.push_back(entry.second);
            for (const auto symbol : forgotten)
                after.setInterval(symbol, SVF::Interval::top());
            return;
        }
        for (const auto location : addresses.locations())
        {
            const auto* object = objectAt(location);
            if (!object || !pointer(object))
                continue;
            auto result = intervalPointerOffset(store->getRHSVar(), before);
            if (!canStrongStore(addresses, *object, before))
                result.joinWith(intervalPointerOffset(object, before));
            assign(object, result);
        }
    }
    else if (const auto* select = SVFUtil::dyn_cast<SelectStmt>(statement))
    {
        if (!pointer(select->getRes()))
            return;
        const auto condition = range(select->getCondition());
        const auto yes = intervalPointerOffset(select->getTrueValue(), before);
        const auto no = intervalPointerOffset(select->getFalseValue(), before);
        auto result = condition.isSingleton() ? (condition.isZero() ? no : yes) : yes;
        if (!condition.isSingleton())
            result.joinWith(no);
        assign(select->getRes(), result);
    }
    else if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(statement))
    {
        if (!pointer(phi->getRes()) || phiEdgeBlock(node->getBB()))
            return;
        SVF::Interval result = SVF::Interval::bottom();
        for (u32_t i = 0; i < phi->getOpVarNum(); ++i)
        {
            const auto* from = phi->getOpICFGNode(i);
            if (!hasAbsState(from))
                continue;
            const auto* edge = icfg->getICFGEdge(from, node, ICFGEdge::IntraCF);
            if (const auto* branch = edge ? SVFUtil::dyn_cast<IntraCFGEdge>(edge) : nullptr)
                if (branch->getCondition() && !isBranchEdgeFeasibleAt(branch, from))
                    continue;
            result.joinWith(intervalPointerOffset(phi->getOpVar(i), state(from)));
        }
        assign(phi->getRes(), result.isBottom() ? SVF::Interval::top() : result);
    }
    else if (const auto* call = SVFUtil::dyn_cast<CallPE>(statement))
    {
        if (!pointer(call->getRes()))
            return;
        SVF::Interval result = SVF::Interval::bottom();
        for (u32_t i = 0; i < call->getOpVarNum(); ++i)
        {
            const auto* from = call->getOpCallICFGNode(i);
            if (hasAbsState(from))
                result.joinWith(intervalPointerOffset(call->getOpVar(i), state(from)));
        }
        assign(call->getRes(), result.isBottom() ? SVF::Interval::top() : result);
    }
    else if (const auto* ret = SVFUtil::dyn_cast<RetPE>(statement))
    {
        if (pointer(ret->getLHSVar()))
            assign(ret->getLHSVar(), intervalPointerOffset(ret->getRHSVar(), before));
    }
}

/// Factory: first call allocates the concrete subclass based on
/// sparsity(); all subsequent calls return the same instance.
/// Must only be called after the option parser has populated AESparsity.
bool AbstractInterpretation::usesOnDemand()
{
    return Options::AEOnDemand() || Options::AEClosureBoxMay();
}

bool AbstractInterpretation::usesBuiltInOnDemand() const
{
    return !providedPacking_ && usesOnDemand();
}

bool AbstractInterpretation::usesPackSSA()
{
    return Options::AESparsity() == OhPackedSparse ||
           (Options::AESparsity() == Sparse && Options::AEDomain() == Octagon &&
            (Options::AERelationalPolicy() == SyntaxPackedRelational ||
             Options::AERelationalPolicy() == ClosurePackedRelational ||
             Options::AERelationalPolicy() == ImpactPackedRelational ||
             Options::AERelationalPolicy() == DuetPackedRelational));
}

AbstractInterpretation& AbstractInterpretation::getAEInstance()
{
    return getAEInstanceImpl({});
}

AbstractInterpretation& AbstractInterpretation::getAEInstanceWithPacking(RelationPacking packing)
{
    return getAEInstanceWithPacking(
        [packing = std::move(packing)](const PackingInput&) mutable
        {
            return std::move(packing);
        });
}

AbstractInterpretation& AbstractInterpretation::getAEInstanceWithPacking(PackingProvider provider)
{
    if (!provider)
        throw std::invalid_argument("a packing provider is required");
    return getAEInstanceImpl(std::move(provider));
}

AbstractInterpretation& AbstractInterpretation::getAEInstanceImpl(PackingProvider provider)
{
    // Keep the singleton alive until process exit. Several owned analysis
    // objects refer to process-global SVF state whose destruction order is
    // outside AE's control.
    static AbstractInterpretation* instance = [&]() -> AbstractInterpretation*
    {
        if (provider)
        {
            const auto mode = Options::AESparsity();
            const bool packSSA = mode == Sparse || mode == OhPackedSparse;
            if (Options::AEDomain() != Octagon || (!packSSA && mode != Dense))
                throw std::invalid_argument("provided packs require dense or pack-SSA Octagon");
            if (packSSA && Options::AEPostCheckFile().empty())
                throw std::invalid_argument("provided pack-SSA packs require a Post ledger");
            AbstractInterpretation* analysis = packSSA
                ? static_cast<AbstractInterpretation*>(new OhPackedAbstractInterpretation())
                : new AbstractInterpretation();
            analysis->providedPacking_ = true;
            analysis->packingProvider_.swap(provider);
            return analysis;
        }
        if (Options::AESparsity() == AESparsity::Sparse &&
                Options::AEDomain() != AENumericalDomain::Box && !usesPackSSA())
            throw std::invalid_argument("relational sparse AE requires native Octagon packing");
        if (Options::AESparsity() == AESparsity::VersionedSparse &&
                (Options::AEDomain() == AENumericalDomain::Box ||
                 (Options::AERelationalPolicy() != WholeRelational &&
                  Options::AERelationalPolicy() != SyntaxPackedRelational)))
        {
            assert(false && "-ae-sparsity=d3 requires a relational domain with " "-ae-relational-policy=whole or syntax-pack");
            std::abort();
        }
        if (Options::AERelationalPolicy() != WholeRelational &&
                Options::AEDomain() == AENumericalDomain::Box)
        {
            assert(false && "partial relational policies require octagon or polyhedra");
            std::abort();
        }
        if (usesPackSSA())
        {
            if (Options::AEDomain() != Octagon ||
                    (Options::AERelationalPolicy() != SyntaxPackedRelational &&
                     Options::AERelationalPolicy() != ClosurePackedRelational &&
                     Options::AERelationalPolicy() != ImpactPackedRelational &&
                     Options::AERelationalPolicy() != DuetPackedRelational) ||
                    Options::AEPostCheckFile().empty())
            {
                assert(false && "oh-packed requires native octagon, syntax/closure/impact packs, Post checking");
                std::abort();
            }
            return new OhPackedAbstractInterpretation();
        }
        switch (Options::AESparsity())
        {
        case AESparsity::SemiSparse:
            return new SemiSparseAbstractInterpretation();
        case AESparsity::Sparse:
            return new FullSparseAbstractInterpretation();
        case AESparsity::VersionedSparse:
            return new VersionedSparseAbstractInterpretation();
        case AESparsity::Dense:
        default:
            return new AbstractInterpretation();
        }
    }();
    if (provider)
        throw std::logic_error("packing must be supplied before the first getAEInstance call");
    return *instance;
}

/// Destructor
AbstractInterpretation::~AbstractInterpretation()
{
    delete utils;
    delete stat;
    delete preAnalysis;
}

/// Collect entry point functions for analysis.
/// In main mode, entry is main/svf.main. In no-main mode,
/// entries are SCCs with no external caller in the Andersen-resolved CallGraph.
FIFOWorkList<const FunObjVar*> AbstractInterpretation::collectProgEntryFuns()
{
    FIFOWorkList<const FunObjVar*> entryFunctions;
    const bool mainEntry = Options::AEFunEntry() == AEFunEntryMode::MAIN;
    Set<NodeID> visitedEntrySCCs;
    auto* callGraphSCC = preAnalysis->getCallGraphSCC();

    for (auto it = callGraph->begin(); it != callGraph->end(); ++it)
    {
        const CallGraphNode* cgNode = it->second;
        const FunObjVar* fun = cgNode->getFunction();

        // Skip declarations
        if (fun->isDeclaration())
            continue;

        if (mainEntry)
        {
            if (SVFUtil::isProgEntryFunction(fun))
            {
                entryFunctions.push(fun);
                break;
            }
        }
        else
        {
            NodeID repNodeId = callGraphSCC->repNode(cgNode->getId());
            if (visitedEntrySCCs.count(repNodeId))
                continue;

            const NodeBS& cgSCCNodes = callGraphSCC->subNodes(repNodeId);
            bool hasExternalCaller = false;
            for (NodeID nodeId : cgSCCNodes)
            {
                const CallGraphNode* sccNode = callGraph->getGNode(nodeId);
                for (auto inEdge : sccNode->getInEdges())
                {
                    if (!cgSCCNodes.test(inEdge->getSrcID()))
                    {
                        hasExternalCaller = true;
                        break;
                    }
                }
                if (hasExternalCaller)
                    break;
            }

            if (hasExternalCaller)
                continue;

            visitedEntrySCCs.insert(repNodeId);
            const FunObjVar* entryFun = fun;
            for (NodeID nodeId : cgSCCNodes)
            {
                const FunObjVar* sccFun =
                    callGraph->getGNode(nodeId)->getFunction();
                if (SVFUtil::isProgEntryFunction(sccFun))
                {
                    entryFun = sccFun;
                    break;
                }
            }
            entryFunctions.push(entryFun);
        }
    }

    if (mainEntry && entryFunctions.empty())
    {
        SVFUtil::errs() << SVFUtil::errMsg(
                            "AE -ae-fun-entry=main requires a program entry function, but "
                            "main/svf.main was not found.\n");
        assert(false &&
               "No program entry function found for -ae-fun-entry=main");
        abort();
    }

    return entryFunctions;
}

/// Program entry - entry policy is selected by -ae-fun-entry.
void AbstractInterpretation::analyse()
{
    analyzeFromAllProgEntries();
}

void AbstractInterpretation::initializeRootArguments(
    const FunEntryICFGNode* entry, const ICFGNode* node)
{
    for (const SVFVar* argument : entry->getFormalParms())
    {
        if (argument->getType()->isPointerTy())
            updateAddressSet(argument, blackHoleAddressSet(), node);
        else
            updateInterval(argument, unknownInterval(argument), node);
    }
    const auto main = AllocationSizeModel::mainArguments(*svfir);
    if (!main || main->entry != entry)
        return;
    if (!main->vector || !main->strings)
        throw std::logic_error("main environment objects were not prepared");
    auto count = utils->getRangeLimitFromType(main->argc->getType());
    count.meetWith(SVF::Interval(SVF::Bound::finite(SVF::Rational(0)),
                                 SVF::Bound::plusInfinity()));
    updateInterval(main->argc, count, node);
    updateAddressSet(main->argv,
                     SVF::AddressSet::singleton(adapter_.location(*main->vector)), node);
    auto contents = SVF::AddressSet::singleton(adapter_.location(*main->strings));
    contents.joinWith(SVF::AddressSet::singleton(SVF::Location::null()));
    updateValue(main->vector, SVF::Interval::bottom(), contents, node);
    updateValue(main->strings, utils->getRangeLimitFromType(main->strings->getType()),
                SVF::AddressSet::bottom(), node);
    State& initial = ensureState(node);
    initial.assignNumeric(adapter_.sizeVariable(*main->vector),
                          SVF::LinearExpression(adapter_.variable(*main->argc)) +
                          SVF::LinearExpression(SVF::Rational(1)));
    assignInterval(initial, adapter_.sizeVariable(*main->strings),
                   SVF::Interval(SVF::Bound::finite(SVF::Rational(1)),
                                 SVF::Bound::plusInfinity()));
    if (intervalPreanalysis_)
    {
        const auto zero = SVF::Interval::singleton(SVF::Rational(0));
        initial.setInterval(intervalOffsetVariable(main->argv), zero);
        initial.setInterval(intervalOffsetVariable(main->vector), zero);
        // Sparrow's library prefix supplies prediction facts, not main facts.
        for (auto it = svfir->begin(); it != svfir->end(); ++it)
            if (const auto* object = SVFUtil::dyn_cast<GlobalObjVar>(it->second);
                    object && ImpactRelationPacking::isExternalObject(object->getId()))
            {
                if (object->getName() == "optarg" && object->isPointer())
                {
                    updateValue(object, SVF::Interval::bottom(),
                                SVF::AddressSet::singleton(adapter_.location(*main->strings)), node);
                    initial.setInterval(intervalOffsetVariable(object), zero);
                }
                else if (object->getName() == "optind" &&
                         SVFUtil::isa<SVFIntegerType>(object->getType()))
                    updateInterval(object,
                                   SVF::Interval(SVF::Bound::finite(SVF::Rational(0)),
                                                 SVF::Bound::plusInfinity()), node);
            }
    }
}

/// Analyze the entry functions selected by collectProgEntryFuns().
/// Abstract state is shared across entry points so that functions analyzed from
/// earlier entries are not re-analyzed from scratch.
void AbstractInterpretation::analyzeFromAllProgEntries()
{
    // Collect all entry point functions
    FIFOWorkList<const FunObjVar*> entryFunctions = collectProgEntryFuns();

    if (entryFunctions.empty())
    {
        assert(false && "No entry functions found for analysis");
        return;
    }
    // handle Global ICFGNode of SVFModule
    handleGlobalNode();
    const ICFGNode* globalNode = icfg->getGlobalICFGNode();
    while (!entryFunctions.empty())
    {
        const FunObjVar* entryFun = entryFunctions.pop();
        const FunEntryICFGNode* funEntry = icfg->getFunEntryICFGNode(entryFun);
        // Selected roots have no caller transfer to define their arguments.
        // Inputs are unknown values, unlike uninitialized object contents.
        // Match upstream's type-directed policy for external pointer inputs.
        initializeRootArguments(funEntry, globalNode);
        copyAbstractState(globalNode, funEntry);
        // A later call site can enlarge a context-insensitive callee summary.
        // Revisit the root until every caller and its downstream states cover
        // that enlarged summary.  Loop/recursion WTO handling remains
        // responsible for convergence; an arbitrary iteration cap would not
        // establish a post-fixpoint.
        summaryIteration_ = 0;
        while (handleFunction(funEntry, nullptr))
            ++summaryIteration_;
    }
}

/// Given a cmp operand, walk its SSA def edge to find the LoadStmt that
/// produced it. This lets us trace back to the ObjVar in memory so that
/// branch narrowing can refine the stored value.
///
/// Example: for `%cmp = icmp sgt %a, 5` where `%a = load i32, ptr %p`,
/// calling findBackingLoad(%a) returns the LoadStmt, and we can then
/// narrow the ObjVar behind %p.
///
/// Follows an identity copy or signed extension, whose interval inverse
/// is intersection with the original memory interval. Other casts are excluded.
static const LoadStmt* findBackingLoad(const SVFVar* var)
{
    if (var->getInEdges().size() != 1)
        return nullptr;
    SVFStmt* inStmt = *var->getInEdges().begin();
    if (const LoadStmt* ls = SVFUtil::dyn_cast<LoadStmt>(inStmt))
        return ls;
    if (const CopyStmt* cs = SVFUtil::dyn_cast<CopyStmt>(inStmt))
    {
        const bool identity = cs->getCopyKind() == CopyStmt::COPYVAL &&
                              cs->getLHSVar()->getType() == cs->getRHSVar()->getType();
        const bool signedExtension = cs->getCopyKind() == CopyStmt::SEXT &&
                                     SVFUtil::isa<SVFIntegerType>(cs->getRHSVar()->getType()) &&
                                     cs->getLHSVar()->getType()->getByteSize() >= cs->getRHSVar()->getType()->getByteSize();
        if (!identity && !signedExtension)
            return nullptr;
        const SVFVar* src = cs->getRHSVar();
        if (src->getInEdges().size() == 1)
            return SVFUtil::dyn_cast<LoadStmt>(*src->getInEdges().begin());
    }
    return nullptr;
}

/// Compute the interval constraint on one cmp operand given the predicate,
/// branch direction (succ), which side it is on, and the other operand's
/// interval. Returns top if no useful narrowing is possible.
///
/// Called from collectBranchRefinement for each non-constant operand that has a
/// backing load. Given a branch condition like:
///
///   %cmp = icmp sgt %a, 5       ;  a > 5
///   br i1 %cmp, label %T, %F
///
/// On the true branch (succ=1), operand %a (isLHS=true) is constrained to
/// [6, +inf). On the false branch (succ=0), %a is constrained to (-inf, 5].
/// The result is used to narrow the ObjVar behind %a's load.
static SVF::Interval computeCmpConstraint(s32_t predicate, s64_t succ,
        bool isLHS, const SVF::Interval& self,
        const SVF::Interval& other)
{
    // Normalize: always reason from the LHS perspective.
    // If we are the RHS operand, swap the predicate direction.
    if (!isLHS)
    {
        // a > b from b's perspective: b < a
        static const Map<s32_t, s32_t> swapPred =
        {
            {CmpStmt::ICMP_EQ, CmpStmt::ICMP_EQ},
            {CmpStmt::ICMP_NE, CmpStmt::ICMP_NE},
            {CmpStmt::ICMP_SGT, CmpStmt::ICMP_SLT},
            {CmpStmt::ICMP_SGE, CmpStmt::ICMP_SLE},
            {CmpStmt::ICMP_SLT, CmpStmt::ICMP_SGT},
            {CmpStmt::ICMP_SLE, CmpStmt::ICMP_SGE},
            {CmpStmt::ICMP_UGT, CmpStmt::ICMP_ULT},
            {CmpStmt::ICMP_UGE, CmpStmt::ICMP_ULE},
            {CmpStmt::ICMP_ULT, CmpStmt::ICMP_UGT},
            {CmpStmt::ICMP_ULE, CmpStmt::ICMP_UGE},
            {CmpStmt::FCMP_OEQ, CmpStmt::FCMP_OEQ},
            {CmpStmt::FCMP_UEQ, CmpStmt::FCMP_UEQ},
            {CmpStmt::FCMP_OGT, CmpStmt::FCMP_OLT},
            {CmpStmt::FCMP_OGE, CmpStmt::FCMP_OLE},
            {CmpStmt::FCMP_OLT, CmpStmt::FCMP_OGT},
            {CmpStmt::FCMP_OLE, CmpStmt::FCMP_OGE},
            {CmpStmt::FCMP_UGT, CmpStmt::FCMP_ULT},
            {CmpStmt::FCMP_UGE, CmpStmt::FCMP_ULE},
            {CmpStmt::FCMP_ULT, CmpStmt::FCMP_UGT},
            {CmpStmt::FCMP_ULE, CmpStmt::FCMP_UGE},
            {CmpStmt::FCMP_ONE, CmpStmt::FCMP_ONE},
            {CmpStmt::FCMP_UNE, CmpStmt::FCMP_UNE},
        };
        auto it = swapPred.find(predicate);
        if (it == swapPred.end())
            return SVF::Interval::top();
        predicate = it->second;
    }

    // If false branch, negate the predicate.
    if (succ == 0)
    {
        static const Map<s32_t, s32_t> negPred =
        {
            {CmpStmt::ICMP_EQ, CmpStmt::ICMP_NE},
            {CmpStmt::ICMP_NE, CmpStmt::ICMP_EQ},
            {CmpStmt::ICMP_SGT, CmpStmt::ICMP_SLE},
            {CmpStmt::ICMP_SGE, CmpStmt::ICMP_SLT},
            {CmpStmt::ICMP_SLT, CmpStmt::ICMP_SGE},
            {CmpStmt::ICMP_SLE, CmpStmt::ICMP_SGT},
            {CmpStmt::ICMP_UGT, CmpStmt::ICMP_ULE},
            {CmpStmt::ICMP_UGE, CmpStmt::ICMP_ULT},
            {CmpStmt::ICMP_ULT, CmpStmt::ICMP_UGE},
            {CmpStmt::ICMP_ULE, CmpStmt::ICMP_UGT},
            {CmpStmt::FCMP_OEQ, CmpStmt::FCMP_ONE},
            {CmpStmt::FCMP_UEQ, CmpStmt::FCMP_UNE},
            {CmpStmt::FCMP_OGT, CmpStmt::FCMP_OLE},
            {CmpStmt::FCMP_OGE, CmpStmt::FCMP_OLT},
            {CmpStmt::FCMP_OLT, CmpStmt::FCMP_OGE},
            {CmpStmt::FCMP_OLE, CmpStmt::FCMP_OGT},
            {CmpStmt::FCMP_UGT, CmpStmt::FCMP_ULE},
            {CmpStmt::FCMP_UGE, CmpStmt::FCMP_ULT},
            {CmpStmt::FCMP_ULT, CmpStmt::FCMP_UGE},
            {CmpStmt::FCMP_ULE, CmpStmt::FCMP_UGT},
            {CmpStmt::FCMP_ONE, CmpStmt::FCMP_OEQ},
            {CmpStmt::FCMP_UNE, CmpStmt::FCMP_UEQ},
        };
        auto it = negPred.find(predicate);
        if (it == negPred.end())
            return SVF::Interval::top();
        predicate = it->second;
    }

    // Now compute the constraint on LHS given: LHS <predicate> other
    SVF::Interval result = self;
    switch (predicate)
    {
    case CmpStmt::ICMP_EQ:
    case CmpStmt::FCMP_OEQ:
    case CmpStmt::FCMP_UEQ:
        result.meetWith(other);
        break;
    case CmpStmt::ICMP_NE:
    case CmpStmt::FCMP_ONE:
    case CmpStmt::FCMP_UNE:
    case CmpStmt::FCMP_FALSE:
    case CmpStmt::FCMP_TRUE:
        // Original does not narrow memory on disequality, even when Box
        // could remove an interval endpoint. Keep that policy in the AE layer.
        return SVF::Interval::top();
    case CmpStmt::ICMP_UGT:
    case CmpStmt::ICMP_SGT:
    case CmpStmt::FCMP_OGT:
    case CmpStmt::FCMP_UGT:
        if (!other.lower().isFinite())
            return result;
        result.meetWith(
            SVF::Interval(SVF::Bound::finite(other.lower().value(), true),
                          SVF::Bound::plusInfinity()));
        break;
    case CmpStmt::ICMP_UGE:
    case CmpStmt::ICMP_SGE:
    case CmpStmt::FCMP_OGE:
    case CmpStmt::FCMP_UGE:
        if (!other.lower().isFinite())
            return result;
        result.meetWith(
            SVF::Interval(SVF::Bound::finite(other.lower().value(),
                                             other.lower().isStrict()),
                          SVF::Bound::plusInfinity()));
        break;
    case CmpStmt::ICMP_ULT:
    case CmpStmt::ICMP_SLT:
    case CmpStmt::FCMP_OLT:
    case CmpStmt::FCMP_ULT:
        if (!other.upper().isFinite())
            return result;
        result.meetWith(
            SVF::Interval(SVF::Bound::minusInfinity(),
                          SVF::Bound::finite(other.upper().value(), true)));
        break;
    case CmpStmt::ICMP_ULE:
    case CmpStmt::ICMP_SLE:
    case CmpStmt::FCMP_OLE:
    case CmpStmt::FCMP_ULE:
        if (!other.upper().isFinite())
            return result;
        result.meetWith(
            SVF::Interval(SVF::Bound::minusInfinity(),
                          SVF::Bound::finite(other.upper().value(),
                                             other.upper().isStrict())));
        break;
    default:
        return SVF::Interval::top();
    }
    return result;
}

bool AbstractInterpretation::isSwitchDefaultEdge(const IntraCFGEdge* edge) const
{
    const auto* branch = SVFUtil::cast<BranchStmt>(
                             edge->getSrcNode()->getSVFStmts().back());
    return branch->getSuccessor(0) == edge->getDstNode();
}

bool AbstractInterpretation::isSwitchBranchEdgeFeasible(
    const IntraCFGEdge* edge, const SVF::Interval& input) const
{
    if (input.isBottom())
        return false;
    if (edge->getCondition()->getType()->getByteSize() > sizeof(s64_t))
        return true;
    const auto* branch = SVFUtil::cast<BranchStmt>(
                             edge->getSrcNode()->getSVFStmts().back());
    u64_t matchedCases = 0;
    for (u32_t i = 1; i < branch->getNumSuccessors(); ++i)
    {
        const SVF::Rational value(branch->getSuccessorCondValue(i));
        if (input.contains(value))
        {
            if (branch->getSuccessor(i) == edge->getDstNode())
                return true;
            ++matchedCases;
        }
    }
    if (!isSwitchDefaultEdge(edge))
        return false;
    if (!input.lower().isFinite() || !input.upper().isFinite())
        return true;
    const SVF::Rational span = input.upper().value() - input.lower().value();
    return span >= SVF::Rational(static_cast<s64_t>(matchedCases));
}

void AbstractInterpretation::collectSwitchRefinement(
    const IntraCFGEdge* edge, SVF::AbstractDomain& state)
{
    if (isSwitchDefaultEdge(edge))
        return;
    const auto* branch = SVFUtil::cast<BranchStmt>(
                             edge->getSrcNode()->getSVFStmts().back());
    u32_t caseCount = 0;
    s64_t caseValue = 0;
    for (u32_t i = 1; i < branch->getNumSuccessors(); ++i)
        if (branch->getSuccessor(i) == edge->getDstNode())
        {
            ++caseCount;
            caseValue = branch->getSuccessorCondValue(i);
        }
    if (caseCount != 1)
        return;
    const LoadStmt* load = findBackingLoad(edge->getCondition());
    if (!load)
        return;
    const SVF::AddressSet targets = getAddressSet(load->getRHSVar(), load->getICFGNode());
    if (!targets.isSingleton() || targets.hasUnknownObject())
        return;
    const ObjVar* object = objectAt(*targets.begin());
    if (object && object->getId() != IRGraph::NullPtr && object->getId() != IRGraph::BlackHole)
        recordBranchRefinement(object->getId(),
                               SVF::Interval::singleton(SVF::Rational(caseValue)), state,
                               load->getICFGNode(), edge->getDstNode());
}

std::set<SVF::Variable> AbstractInterpretation::branchWrites(const IntraCFGEdge* edge) const
{
    std::set<SVF::Variable> writes;
    const SVFVar* condition = edge->getCondition();
    if (!condition)
        return writes;
    if (!edge->isSwitchEdge())
        collectConditionWrites(condition, edge->getSuccessorCondValue() != 0,
                               edge->getSrcNode(), writes);
    else if ((intervalPreanalysis_ || numericalDomain() != AENumericalDomain::Box) &&
             edge->getSwitchWidth() >= 32 && edge->getSwitchWidth() <= 64)
    {
        const auto* value = SVFUtil::dyn_cast<ValVar>(condition);
        if (value && adapter_.contains(*value))
            writes.insert(adapter_.variable(*value));
    }

    if (condition->getInEdges().empty())
        return writes;
    const auto* comparison = edge->isSwitchEdge() ? nullptr
        : SVFUtil::dyn_cast<CmpStmt>(*condition->getInEdges().begin());
    std::vector<const LoadStmt*> loads;
    if (comparison)
    {
        const s32_t predicate = comparison->getPredicate();
        if (predicate != CmpStmt::ICMP_EQ && predicate != CmpStmt::ICMP_NE &&
                predicate != CmpStmt::ICMP_SLT && predicate != CmpStmt::ICMP_SLE &&
                predicate != CmpStmt::ICMP_SGT && predicate != CmpStmt::ICMP_SGE)
            return writes;
        if (comparison->getOpVarID(0) == IRGraph::NullPtr ||
                comparison->getOpVarID(1) == IRGraph::NullPtr)
            return writes;
        for (const auto* operand : comparison->getOpndVars())
            if (const auto* load = findBackingLoad(operand))
                loads.push_back(load);
    }
    else
    {
        if (edge->isSwitchEdge() && (edge->includesSwitchDefault() ||
                edge->getSwitchWidth() < 32 || edge->getSwitchWidth() > 64 ||
                edge->getSwitchCases().empty()))
            return writes;
        for (const auto* definition : condition->getInEdges())
            if (const auto* load = SVFUtil::dyn_cast<LoadStmt>(definition))
                loads.push_back(load);
    }
    for (const auto* load : loads)
    {
        if (!SVFIRAdapter::loadedMemoryStillCurrent(load, edge->getSrcNode()))
            continue;
        const auto& targets = preAnalysis->getPointerAnalysis()->getPts(load->getRHSVarID());
        bool unknown = targets.empty();
        for (NodeID id : targets)
        {
            const auto* object = SVFUtil::dyn_cast<ObjVar>(svfir->getGNode(id));
            unknown |= !object || id == IRGraph::BlackHole;
            if (object && !object->isPointer())
                writes.insert(adapter_.contentVariable(*object));
        }
        // Runtime addresses may be more precise than an unknown static target.
        // Cover numerical object owners without redefining unrelated scalars.
        if (unknown)
            for (const auto& pack : *relationalPacking_)
                for (const auto variable : pack)
                    if (const auto* object = adapter_.contentObject(variable))
                        if (!object->isPointer())
                            writes.insert(variable);
    }
    return writes;
}

void AbstractInterpretation::collectBranchRefinement(
    const IntraCFGEdge* edge, SVF::AbstractDomain& state)
{
    const SVFVar* cond = edge->getCondition();
    const ICFGNode* pred = edge->getSrcNode();
    const ICFGNode* succNode = edge->getDstNode();
    s64_t succ = edge->getSuccessorCondValue();

    // Some frontends leave synthetic branch conditions without a defining
    // SVF statement. Assertions are disabled in benchmark builds, so do not
    // dereference the empty edge set; there is simply no sound refinement to
    // collect in this case.
    if (cond->getInEdges().empty())
        return;
    const SVFStmt* condDef = *cond->getInEdges().begin();

    const CmpStmt* cmpStmt = edge->isSwitchEdge() ? nullptr : SVFUtil::dyn_cast<CmpStmt>(condDef);
    if (!cmpStmt && numericalDomain() == AENumericalDomain::Box)
    {
        collectSwitchRefinement(edge, state);
        return;
    }
    if (cmpStmt)
    {
        s32_t predicate = cmpStmt->getPredicate();
        const bool unsignedPredicate = predicate == CmpStmt::ICMP_ULT ||
                                       predicate == CmpStmt::ICMP_ULE ||
                                       predicate == CmpStmt::ICMP_UGT ||
                                       predicate == CmpStmt::ICMP_UGE;
        if (!(numericalDomain() == Box && unsignedPredicate) &&
                predicate!=CmpStmt::ICMP_EQ && predicate!=CmpStmt::ICMP_NE &&
                predicate!=CmpStmt::ICMP_SLT && predicate!=CmpStmt::ICMP_SLE &&
                predicate!=CmpStmt::ICMP_SGT && predicate!=CmpStmt::ICMP_SGE)
            return;

        if (cmpStmt->getOpVarID(0) == IRGraph::NullPtr ||
                cmpStmt->getOpVarID(1) == IRGraph::NullPtr)
        {
            // p == NULL / p != NULL: no interval obj to refine.
        }
        else
        {
            SVF::Interval opVal[2] = {getInterval(cmpStmt->getOpVar(0), pred),
                                      getInterval(cmpStmt->getOpVar(1), pred)
                                     };
            // Unsigned and mathematical order agree on non-negative operands.
            if (unsignedPredicate)
                for (const auto& interval : opVal)
                    if (interval.isBottom() || !interval.lower().isFinite() ||
                            interval.lower().value() < SVF::Rational(0))
                        return;
            SVF::AddressSet opAddr[2] =
            {
                getAddressSet(cmpStmt->getOpVar(0), pred),
                getAddressSet(cmpStmt->getOpVar(1), pred)
            };

            if ((opVal[0].isBottom() || opVal[1].isBottom()) &&
                    (!opAddr[0].isBottom() || !opAddr[1].isBottom()))
            {
                // Pointer-valued cmp: branch feasibility only.
            }
            else
            {
                for (int i = 0; i < 2; i++)
                {
                    const int other = 1 - i;
                    const LoadStmt* load =
                        findBackingLoad(cmpStmt->getOpVar(i));

                    if (opVal[i].isSingleton())
                    {
                        // Example: in x < 5, operand 5 is not refined.
                    }
                    else if (!opVal[other].isSingleton())
                    {
                        // Match Original: refine a loaded value only against
                        // a fixed numerical bound, not another interval.
                    }
                    else if (!load || !SVFIRAdapter::loadedMemoryStillCurrent(load,pred))
                    {
                        // Example: cmp uses a computed temporary, not load p.
                    }
                    else
                    {
                        SVF::Interval narrowed = computeCmpConstraint(
                                                     predicate, succ, i == 0, opVal[i], opVal[other]);

                        if (narrowed.isTop())
                        {
                            // != and unsupported predicates reach here.
                        }
                        else
                        {
                            const ICFGNode* loadIcfg = load->getICFGNode();
                            const SVF::AddressSet ptrVal =
                                getAddressSet(load->getRHSVar(), loadIcfg);
                            if (!ptrVal.isSingleton() ||
                                    ptrVal.hasUnknownObject())
                            {
                                // Cannot map load p back to concrete ObjVars.
                            }
                            else
                            {
                                for (const SVF::Location location : ptrVal)
                                {
                                    if (const ObjVar* object = objectAt(location))
                                        if (canRefineMemory(ptrVal,*object,static_cast<State&>(state)))
                                            recordBranchRefinement(
                                                object->getId(), narrowed, state,
                                                loadIcfg, succNode);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    else
    {
        const SVFVar* var = cond;

        SVF::Interval switch_cond = getInterval(var, pred);
        if (edge->isSwitchEdge())
        {
            const auto& cases = edge->getSwitchCases();
            if (edge->includesSwitchDefault() || edge->getSwitchWidth() < 32 ||
                    edge->getSwitchWidth() > 64 || cases.empty())
                return;
            const auto limits = std::minmax_element(cases.begin(), cases.end());
            switch_cond.meetWith(SVF::Interval(SVF::Bound::finite(SVF::Rational(*limits.first)),
                                               SVF::Bound::finite(SVF::Rational(*limits.second))));
        }
        else
            switch_cond.meetWith(SVF::Interval::singleton(SVF::Rational(succ)));
        if (switch_cond.isBottom())
        {
            // This case label is not reachable from cond's interval.
        }
        else
        {
            FIFOWorkList<const SVFStmt*> stmtList;
            for (SVFStmt* stmt : var->getInEdges())
                stmtList.push(stmt);
            while (!stmtList.empty())
            {
                const SVFStmt* stmt = stmtList.pop();
                const LoadStmt* load = SVFUtil::dyn_cast<LoadStmt>(stmt);
                if (!load || !SVFIRAdapter::loadedMemoryStillCurrent(load,pred))
                {
                    // Skip non-load definitions of the switch condition.
                }
                else
                {
                    const ICFGNode* loadIcfg = load->getICFGNode();
                    const SVF::AddressSet ptrVal =
                        getAddressSet(load->getRHSVar(), loadIcfg);
                    if (!ptrVal.isSingleton() || ptrVal.hasUnknownObject())
                    {
                        // Cannot map load p back to concrete ObjVars.
                    }
                    else
                    {
                        for (const SVF::Location location : ptrVal)
                        {
                            if (const ObjVar* object = objectAt(location))
                                if (canRefineMemory(ptrVal,*object,static_cast<State&>(state)))
                                    recordBranchRefinement(object->getId(),
                                                           switch_cond, state,
                                                           loadIcfg, succNode);
                        }
                    }
                }
            }
        }
    }
}

void AbstractInterpretation::recordBranchRefinement(
    NodeID objectId, const SVF::Interval& narrowed,
    SVF::AbstractDomain& abstractState, const ICFGNode*, const ICFGNode*)
{
    const auto* object = SVFUtil::dyn_cast<ObjVar>(svfir->getGNode(objectId));
    if (!object || object->isPointer())
        return;

    State& denseState = static_cast<State&>(abstractState);
    const SVF::Variable content = adapter_.contentVariable(*object);
    // A guard intersects the current content, preserving every relation and
    // initialization facet. Assignment would forget those relations.
    if (narrowed.isBottom())
        denseState.numerical().assume(SVF::equal(SVF::LinearExpression(SVF::Rational(0)),
                SVF::LinearExpression(SVF::Rational(1))));
    else
    {
        if (narrowed.lower().isFinite())
            denseState.numerical().assume(SVF::LinearConstraint(
                                              SVF::LinearExpression(content)-SVF::LinearExpression(narrowed.lower().value()),
                                              narrowed.lower().isStrict()?SVF::ConstraintKind::GreaterThan:SVF::ConstraintKind::GreaterEqual));
        if (narrowed.upper().isFinite())
            denseState.numerical().assume(SVF::LinearConstraint(
                                              SVF::LinearExpression(content)-SVF::LinearExpression(narrowed.upper().value()),
                                              narrowed.upper().isStrict()?SVF::ConstraintKind::LessThan:SVF::ConstraintKind::LessEqual));
    }
}

/**
 * Handle an ICFG node: execute statements on the current abstract state.
 * The node's pre-state must already be installed by
 * mergeStatesFromPredecessors, or by handleGlobalNode for the global node.
 */
void AbstractInterpretation::handleICFGNode(const ICFGNode* node)
{
    // Check reachability: pre-state must have been propagated by predecessors
    bool isFunEntry = SVFUtil::isa<FunEntryICFGNode>(node);
    if (!hasAbsState(node))
    {
        if (isFunEntry)
        {
            // Entry point with no callers: inherit from global node
            const ICFGNode* globalNode = icfg->getGlobalICFGNode();
            if (hasAbsState(globalNode))
            {
                copyAbstractState(globalNode, node);
            }
            else
            {
                resetAbstractState(node);
            }
        }
        else
        {
            return; // unreachable node
        }
    }

    beginAbstractState(node);
    if (intervalPreanalysis_)
        intervalInputs_.insert_or_assign(node, state(node));

    stat->getBlockTrace()++;
    stat->getICFGNodeTrace()++;

    // A RetPE is owned by one RetCFGEdge and was executed before incoming
    // alternatives were joined. Executing every RetPE here would turn
    // alternative callees into sequential strong assignments.
    const bool returnBindingsApplied =
        SVFUtil::isa<RetICFGNode>(node) &&
        std::any_of(node->getInEdges().begin(), node->getInEdges().end(),
                    [](const ICFGEdge* edge)
    {
        const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge);
        return ret && ret->getRetPE();
    });

    // Handle SVF statements.  Individual phi transfers establish each
    // target's product facets.  The grouped transfer below additionally
    // preserves relations between targets selected by the same predecessor.
    for (const SVFStmt* stmt : node->getSVFStmts())
    {
        if (returnBindingsApplied && SVFUtil::isa<RetPE>(stmt))
            continue;
        handleSVFStatement(stmt);
    }
    updateStateOnPhiGroupAtNode(node);
    if (returnBindingsApplied)
        recordMergedReturnSummary(SVFUtil::cast<RetICFGNode>(node));

    // Handle call sites
    if (const CallICFGNode* callNode = SVFUtil::dyn_cast<CallICFGNode>(node))
    {
        recordReachedAssertion(callNode);
        handleCallSite(callNode);
    }

    // Run detectors
    for (auto& detector : detectors)
        detector->detect(node);

    finalizeAbstractState(node);
    // Track this node as analyzed (for coverage statistics across all entry
    // points)
    allAnalyzedNodes.insert(node);
}

/**
 * Handle a function using worklist algorithm guided by WTO order.
 * All top-level WTO components are pushed into the worklist upfront,
 * so the traversal order is exactly the WTO order — each node is
 * visited once, and cycles are handled as whole components.
 */
bool AbstractInterpretation::handleFunction(const ICFGNode* funEntry,
        const CallICFGNode* caller)
{
    auto it = preAnalysis->getFuncToWTO().find(funEntry->getFun());
    assert(it != preAnalysis->getFuncToWTO().end() &&
           "Missing WTO for function");

    Map<const ICFGNode*, State> before;
    for (auto nodeIterator = icfg->begin(); nodeIterator != icfg->end();
            ++nodeIterator)
    {
        const ICFGNode* node = nodeIterator->second;
        if (node->getFun() == funEntry->getFun() && hasAbsState(node))
            before.emplace(node, state(node));
    }

    const bool sparseBox = numericalDomain() == AENumericalDomain::Box &&
                           sparsity() != Dense;
    auto scalarSummary = caller ? nullptr : cloneScalarSummary();
    std::optional<State> previousEntry;
    if (sparseBox && caller && hasAbsState(funEntry))
    {
        previousEntry = state(funEntry);
        for (const SVFVar* formal :
                SVFUtil::cast<FunEntryICFGNode>(funEntry)->getFormalParms())
            materializeValue(*previousEntry,
                             SVFUtil::cast<ValVar>(formal), funEntry);
    }

    // Push all top-level WTO components into the worklist in WTO order
    FIFOWorkList<const ICFGWTOComp*> worklist(it->second->getWTOComponents());

    while (!worklist.empty())
    {
        const ICFGWTOComp* comp = worklist.pop();

        if (const ICFGSingletonWTO* singleton =
                    SVFUtil::dyn_cast<ICFGSingletonWTO>(comp))
        {
            const ICFGNode* node = singleton->getICFGNode();
            if (mergeStatesFromPredecessors(node))
            {
                handleICFGNode(node);
                const auto previous = before.find(node);
                if (node == funEntry && caller && previous != before.end() &&
                        (sparsity() == Dense || packSSAEnabled() || sparseBox) &&
                        summaryIteration_ >= Options::WidenDelay())
                {
                    // Shared summaries can create cycles even without a
                    // recursive source call. Widen their entry equations.
                    State current = state(node);
                    const auto& formals =
                        SVFUtil::cast<FunEntryICFGNode>(node)->getFormalParms();
                    if (sparseBox)
                        for (const SVFVar* formal : formals)
                            materializeValue(current,
                                             SVFUtil::cast<ValVar>(formal), node);
                    State widened = previousEntry ? *previousEntry
                                    : previous->second;
                    widened.widenWith(current);
                    ensureState(node) = widened;
                    if (sparseBox)
                        for (const SVFVar* parameter : formals)
                        {
                            const auto* formal = SVFUtil::cast<ValVar>(parameter);
                            if (adapter_.contains(*formal))
                            {
                                const auto variable = adapter_.variable(*formal);
                                updateValue(formal, widened.interval(variable),
                                            widened.addressSet(variable), node);
                            }
                        }
                    finalizeAbstractState(node);
                }
            }
        }
        else if (const ICFGCycleWTO* cycle =
                     SVFUtil::dyn_cast<ICFGCycleWTO>(comp))
        {
            if (mergeStatesFromPredecessors(cycle->head()->getICFGNode()))
                handleLoopOrRecursion(cycle, caller);
        }
    }
    for (auto nodeIterator = icfg->begin(); nodeIterator != icfg->end();
            ++nodeIterator)
    {
        const ICFGNode* node = nodeIterator->second;
        if (node->getFun() != funEntry->getFun() || !hasAbsState(node))
            continue;
        const auto previous = before.find(node);
        if (previous == before.end() ||
                state(node).isEquivalentTo(previous->second) !=
                SVF::CheckResult::True)
            return true;
    }
    if (scalarSummary)
    {
        const auto current = cloneScalarSummary();
        if (!current || current->isEquivalentTo(*scalarSummary) !=
                SVF::CheckResult::True)
            return true;
    }
    return false;
}

void AbstractInterpretation::refreshSiblingReturnSites(
    const FunObjVar* callee, const RetICFGNode* currentReturn)
{
    if (!callee)
        return;
    const ICFGNode* entry = icfg->getFunEntryICFGNode(callee);
    std::vector<const CallICFGNode*> callers;
    for (const ICFGEdge* incoming : entry->getInEdges())
    {
        const auto* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(incoming);
        if (callEdge)
            callers.push_back(callEdge->getCallSite());
    }
    if (callers.size() <= 1)
        return;
    std::sort(callers.begin(), callers.end(),
              [](const CallICFGNode* left, const CallICFGNode* right)
    {
        return left->getId() < right->getId();
    });
    callers.erase(std::unique(callers.begin(), callers.end()), callers.end());
    for (const CallICFGNode* call : callers)
    {
        const RetICFGNode* returnSite = call->getRetICFGNode();
        if (!returnSite || returnSite == currentReturn || !hasAbsState(call))
            continue;
        copyAbstractState(call, returnSite);
        if (mergeStatesFromPredecessors(returnSite))
            handleICFGNode(returnSite);
        else
            abstractTrace_.erase(returnSite);
    }
}

void AbstractInterpretation::handleCallSite(const ICFGNode* node)
{
    if (const CallICFGNode* callNode = SVFUtil::dyn_cast<CallICFGNode>(node))
    {
        if (isExtCall(callNode))
        {
            handleExtCall(callNode);
        }
        else
        {
            // Handle both direct and indirect calls uniformly
            handleFunCall(callNode);
        }
    }
    else
        assert(false && "it is not call node");
}

bool AbstractInterpretation::isExtCall(const CallICFGNode* callNode)
{
    return SVFUtil::isExtCall(callNode->getCalledFunction());
}

void AbstractInterpretation::handleExtCall(const CallICFGNode* callNode)
{
    utils->handleExtAPI(callNode);
    if (intervalPreanalysis_)
    {
        const auto* returnSite = callNode->getRetICFGNode();
        const auto* result = returnSite ? returnSite->getActualRet() : nullptr;
        if (result && result->isPointer())
        {
            SVF::Interval offset = SVF::Interval::top();
            for (const auto& size : allocationSizeModel().all())
                if (size.site && AllocationSizeModel::allocationCall(size.site) == callNode)
                    offset = SVF::Interval::singleton(SVF::Rational(0));
            const auto* function = callNode->getCalledFunction();
            const std::string name = function ? function->getName() : "";
            if (callNode->arg_size() && (name == "memcpy" || name == "memmove" ||
                    name == "memset" || name == "strcpy" || name == "strncpy" ||
                    name == "strcat" || name == "strncat"))
                offset = intervalPointerOffset(callNode->getArgument(0), state(callNode));
            ensureState(callNode).setInterval(intervalOffsetVariable(result), offset);
        }
    }
    // Keep the external model's result, including an initialized Top. The
    // initialization guard carries that definition without an artificial range.
    for (auto& detector : detectors)
    {
        detector->handleStubFunctions(callNode);
    }
}

/// Get callee function: directly for direct calls, via pointer analysis for
/// indirect calls
const FunObjVar* AbstractInterpretation::getCallee(const CallICFGNode* callNode)
{
    // Direct call: get callee directly from call node
    if (const FunObjVar* callee = callNode->getCalledFunction())
        return callee;

    // Indirect call: resolve callee through pointer analysis
    const auto callsiteMaps = svfir->getIndirectCallsites();
    auto it = callsiteMaps.find(callNode);
    if (it == callsiteMaps.end())
        return nullptr;

    NodeID call_id = it->second;
    if (!hasAbsState(callNode))
        return nullptr;

    const SVF::AddressSet addresses =
        getAddressSet(svfir->getSVFVar(call_id), callNode);
    if (!addresses.isFinite() || addresses.empty())
        return nullptr;

    const ObjVar* object = objectAt(*addresses.begin());
    return object ? SVFUtil::dyn_cast<FunObjVar>(object) : nullptr;
}

/// Process each callee and join its return state. Indirect targets come from
/// Andersen's call graph because AE address values may be incomplete.
void AbstractInterpretation::handleFunCall(const CallICFGNode* callNode)
{
    // The configured TOP summary has one synthetic call->return equation.
    // A mixed indirect target set needs a per-target summary/return join;
    // until that is implemented, do not silently use the direct-call rule.
    if (!callNode->getCalledFunction() && recursiveTopSummary(callNode))
    {
        assert(false && "AE_RECURSIVE_TOP_FAIL_CLOSED: indirect recursive target");
        std::abort();
    }
    if (skipRecursiveCall(callNode))
        return;

    // Direct call: callee is known
    if (const FunObjVar* callee = callNode->getCalledFunction())
    {
        const ICFGNode* calleeEntry = icfg->getFunEntryICFGNode(callee);
        handleFunction(calleeEntry, callNode);
        const RetICFGNode* retNode = callNode->getRetICFGNode();
        copyAbstractState(callNode, retNode);
        // The caller WTO can place a continuation before this return node.
        // Propagate the freshly enlarged context-insensitive callee summary
        // immediately; otherwise the continuation may retain a transiently
        // stronger state even though the return state changes later in the
        // same whole-function pass.
        if (mergeStatesFromPredecessors(retNode))
            handleICFGNode(retNode);
        else
            abstractTrace_.erase(retNode);
        refreshSiblingReturnSites(callee, retNode);
        return;
    }

    // Indirect call: use Andersen's call graph to get all resolved callees.
    const RetICFGNode* retNode = callNode->getRetICFGNode();
    bool analyzedCallee = false;
    std::vector<const FunObjVar*> analyzedCallees;
    if (callGraph->hasIndCSCallees(callNode))
    {
        const auto& callees = callGraph->getIndCSCallees(callNode);
        std::vector<const FunObjVar*> orderedCallees(callees.begin(),
                callees.end());
        std::sort(orderedCallees.begin(), orderedCallees.end(),
                  [](const FunObjVar* lhs, const FunObjVar* rhs)
        {
            return lhs->getId() < rhs->getId();
        });
        for (const FunObjVar* callee : orderedCallees)
        {
            if (callee->isDeclaration())
                continue;
            analyzedCallee = true;
            analyzedCallees.push_back(callee);
            const ICFGNode* calleeEntry = icfg->getFunEntryICFGNode(callee);
            handleFunction(calleeEntry, callNode);
        }
    }
    if (!analyzedCallee)
    {
        // Original's missing SSA result reads as numerical Top. This is an
        // unresolved call, not an uninitialized object load (which stays Bottom).
        const SVFVar* result = retNode->getActualRet();
        if (result && getInterval(result, callNode).isBottom() &&
                getAddressSet(result, callNode).isBottom())
            updateInterval(result, unknownInterval(result), callNode);
    }
    // Resume return node from caller's state (context-insensitive)
    copyAbstractState(callNode, retNode);
    if (analyzedCallee)
    {
        if (mergeStatesFromPredecessors(retNode))
            handleICFGNode(retNode);
        else
            abstractTrace_.erase(retNode);
    }
    for (const FunObjVar* callee : analyzedCallees)
        refreshSiblingReturnSites(callee, retNode);
}

bool AbstractInterpretation::mergeStatesFromPredecessors(
    const ICFGNode* node)
{
    std::optional<State> previous;
    if (objectRoutes_ && hasAbsState(node))
        previous = state(node);
    State merged = bottomState();
    bool hasFeasiblePredecessor = false;

    for (const ICFGEdge* edge : orderedIncomingEdges(node))
    {
        const ICFGNode* predecessor = edge->getSrcNode();
        if (abstractTrace_.count(predecessor) == 0)
            continue;

        bool shouldMerge = false;
        const IntraCFGEdge* conditional = SVFUtil::dyn_cast<IntraCFGEdge>(edge);
        if (conditional)
            shouldMerge = true;
        else if (SVFUtil::isa<CallCFGEdge>(edge))
        {
            shouldMerge = true;
        }
        else if (SVFUtil::isa<RetCFGEdge>(edge))
        {
            const auto* returnSite = SVFUtil::dyn_cast<RetICFGNode>(node);
            // A shared callee exit can be reachable through another caller.
            // Preserve call/return matching even when recursive calls use a
            // TOP summary; the summary resumes through copyAbstractState().
            shouldMerge =
                returnSite &&
                abstractTrace_.count(returnSite->getCallICFGNode()) != 0;
        }
        if (!shouldMerge)
            continue;

        State source = state(predecessor);
        applyRelationalCallBoundary(source, edge, node);
        if (const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge))
            applyReturnEdgeTransfer(source, ret);
        if (conditional && conditional->getCondition())
        {
            assumeBranch(conditional, source);
            collectBranchRefinement(conditional, source);
        }
        applyPhiEdgeTransfer(source, edge, node);
        if (source.isBottom())
            continue;

        recordIncomingAbstractState(edge, source);
        if (objectRoutes_)
            source = sparseObjectPredecessor(source);
        merged.joinWith(source);
        hasFeasiblePredecessor = true;
    }

    if (!hasFeasiblePredecessor)
        return false;
    abstractTrace_.insert_or_assign(node, std::move(merged));
    if (objectRoutes_)
        pullSparseObjectRoutes(node, previous ? &*previous : nullptr);
    return true;
}

void AbstractInterpretation::applyRelationalCallBoundary(
    State& source, const ICFGEdge* edge, const ICFGNode* target) const
{
    if (numericalDomain() == AENumericalDomain::Box ||
            Options::AERelationalCallPolicy() != IntraproceduralCalls ||
            (!SVFUtil::isa<CallCFGEdge>(edge) &&
             !SVFUtil::isa<RetCFGEdge>(edge)) || source.isBottom())
        return;

    // Eva's intraprocedural mode keeps unary values and memory effects across
    // a call boundary, but not relations inferred in the other function.
    // Snapshot every unary hull before forgetting support so the operation is
    // independent of the concrete numerical-domain representation.
    SVF::NumericalDomain& numerical = source.numerical();
    std::vector<std::pair<SVF::Variable, SVF::Interval>> unary;
    for (SVF::Variable variable : numerical.supportVariables())
        unary.emplace_back(variable, numerical.bound(variable));
    for (const auto& [variable, value] : unary)
    {
        (void)value;
        numerical.forget(variable);
    }
    for (const auto& [variable, value] : unary)
        if (!value.isTop())
            numerical.assignBound(variable, value);

    if (!SVFUtil::isa<RetCFGEdge>(edge))
        return;
    const auto* returnSite = SVFUtil::dyn_cast<RetICFGNode>(target);
    if (!returnSite)
        return;
    const CallICFGNode* call = returnSite->getCallICFGNode();
    if (!call || abstractTrace_.count(call) == 0)
        return;

    // Caller SSA values are immutable across the call. Restore their
    // caller-local relations after importing the callee's unary/effect state;
    // object-content coordinates remain excluded because the callee may have
    // modified them.
    State caller = state(call);
    const SVF::Variable contentBegin = adapter_.firstObjectContentVariable();
    std::vector<SVF::Variable> callerScalars;
    for (SVF::Variable variable : caller.numerical().supportVariables())
        if (variable < contentBegin)
            callerScalars.push_back(variable);
    caller.numerical().project(callerScalars);
    numerical.meetWith(caller.numerical());
}

void AbstractInterpretation::applyReturnEdgeTransfer(
    State& source, const RetCFGEdge* edge) const
{
    if (!edge || !edge->getRetPE() || source.isBottom())
        return;
    const RetPE* binding = edge->getRetPE();
    const auto* target = SVFUtil::dyn_cast<ValVar>(binding->getLHSVar());
    const auto* value = SVFUtil::dyn_cast<ValVar>(binding->getRHSVar());
    if (!target || !value || !adapter_.contains(*target) ||
            !adapter_.contains(*value))
        return;

    const SVF::Variable targetVariable = adapter_.variable(*target);
    const SVF::Variable sourceVariable = adapter_.variable(*value);
    const bool numericalMayBeUninitialized =
        source.numericalMayBeUninitialized(sourceVariable);
    source.assignValueFrom(targetVariable, source, sourceVariable);
    if (intervalPreanalysis_ && target->isPointer())
        source.setInterval(intervalOffsetVariable(target), intervalPointerOffset(value, source));
    if (!numericalMayBeUninitialized)
        source.numerical().assign(
                  targetVariable, SVF::LinearExpression(sourceVariable));
    const CallICFGNode* call = edge->getCallSite();
    const FunObjVar* callee = edge->getSrcNode()->getFun();
    if ((sparsity() != Dense && !packSSAEnabled()) ||
            numericalDomain() == AENumericalDomain::Box ||
            Options::AERelationalCallPolicy() != ThroughCalls || !call ||
            !callee || !call->getCaller() || !hasAbsState(call) || target->isPointer() ||
            numericalMayBeUninitialized ||
            preAnalysis->getPointerAnalysis()->isInRecursion(callee))
        return;

    // Instantiate a relation over formal inputs and the return value with
    // this call's actual inputs. No caller is equated to a shared formal.
    const auto& formals = icfg->getFunEntryICFGNode(callee)->getFormalParms();
    std::map<SVF::Variable, SVF::LinearExpression> replacements;
    std::vector<SVF::Variable> retained{sourceVariable};
    replacements.emplace(sourceVariable, SVF::LinearExpression(targetVariable));
    for (std::size_t i = 0; i < formals.size() && i < call->arg_size(); ++i)
    {
        const auto* formal = SVFUtil::dyn_cast<ValVar>(formals[i]);
        const auto* actual = SVFUtil::dyn_cast<ValVar>(call->getArgument(i));
        if (!formal || formal->isPointer() || !adapter_.contains(*formal) || !actual)
            continue;
        const auto symbol = adapter_.variable(*formal);
        if (const auto* constant = SVFUtil::dyn_cast<ConstIntValVar>(actual))
        {
            const auto* type = SVFUtil::dyn_cast<SVFIntegerType>(actual->getType());
            const s64_t literal = type && type->isBoolean() ? (constant->getSExtValue() != 0 ? 1 : 0)
                                  : constant->getSExtValue();
            replacements.emplace(symbol, SVF::LinearExpression(SVF::Rational(literal)));
        }
        else if (adapter_.contains(*actual) &&
                 !state(call).numericalMayBeUninitialized(adapter_.variable(*actual)))
            replacements.emplace(symbol, SVF::LinearExpression(adapter_.variable(*actual)));
        else
            continue;
        retained.push_back(symbol);
    }
    State summary = source;
    summary.numerical().project(retained);

    // Caller SSA values cannot be modified by a non-recursive callee. Keep
    // their call-site values and relations rather than joining other callers.
    State caller = state(call);
    std::vector<SVF::Variable> callerValues;
    for (auto it = svfir->begin(); it != svfir->end(); ++it)
        if (const auto* v = SVFUtil::dyn_cast<ValVar>(it->second))
            if (v != target && v->getFunction() == call->getCaller() && adapter_.contains(*v))
            {
                const auto symbol = adapter_.variable(*v);
                callerValues.push_back(symbol);
                source.assignValueFrom(symbol, caller, symbol);
            }
    caller.numerical().project(callerValues);
    source.numerical().meetWith(caller.numerical());
    source.numerical().forget(targetVariable);
    for (const auto& constraint : summary.numerical().toConstraints())
        source.assume(SVF::LinearConstraint(
                          constraint.expression().substituted(replacements), constraint.kind()));

}

void AbstractInterpretation::recordMergedReturnSummary(
    const RetICFGNode*)
{
}

// Loop / recursion handling (handleLoopOrRecursion + cycle helpers +
// recursion utilities) lives in AELoopRecursion.cpp.

void AbstractInterpretation::handleSVFStatement(const SVFStmt* stmt)
{
    if (intervalPreanalysis_)
        intervalStatementInputs_.insert_or_assign(stmt, state(stmt->getICFGNode()));
    // Memory-copy annotations synthesize pointer-analysis loads/stores. The
    // byte-aware external model owns their numerical effects; applying both
    // models can havoc memory even for a zero-length copy.
    if (SVFUtil::isa<LoadStmt>(stmt) || SVFUtil::isa<StoreStmt>(stmt))
    {
        const auto* call = SVFUtil::dyn_cast<CallICFGNode>(stmt->getICFGNode());
        const FunObjVar* callee = call ? call->getCalledFunction() : nullptr;
        if (callee && SVFUtil::isExtCall(callee) &&
                ExtAPI::getExtAPI()->hasExtFuncAnnotation(callee, "MEMCPY"))
            return;
    }
    if (const AddrStmt* addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
    {
        updateStateOnAddr(addr);
    }
    else if (const BinaryOPStmt* binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
    {
        updateStateOnBinary(binary);
    }
    else if (const CmpStmt* cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
    {
        updateStateOnCmp(cmp);
    }
    else if (SVFUtil::isa<UnaryOPStmt>(stmt))
    {
    }
    else if (SVFUtil::isa<BranchStmt>(stmt))
    {
        // branch stmt is handled in hasBranchES
    }
    else if (const LoadStmt* load = SVFUtil::dyn_cast<LoadStmt>(stmt))
    {
        updateStateOnLoad(load);
    }
    else if (const StoreStmt* store = SVFUtil::dyn_cast<StoreStmt>(stmt))
    {
        updateStateOnStore(store);
    }
    else if (const CopyStmt* copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
    {
        updateStateOnCopy(copy);
    }
    else if (const GepStmt* gep = SVFUtil::dyn_cast<GepStmt>(stmt))
    {
        updateStateOnGep(gep);
    }
    else if (const SelectStmt* select = SVFUtil::dyn_cast<SelectStmt>(stmt))
    {
        updateStateOnSelect(select);
    }
    else if (const PhiStmt* phi = SVFUtil::dyn_cast<PhiStmt>(stmt))
    {
        updateStateOnPhi(phi);
    }
    else if (const CallPE* callPE = SVFUtil::dyn_cast<CallPE>(stmt))
    {
        // To handle Call Edge
        updateStateOnCall(callPE);
    }
    else if (const RetPE* retPE = SVFUtil::dyn_cast<RetPE>(stmt))
    {
        updateStateOnRet(retPE);
    }
    else
        assert(false && "implement this part");
    if (intervalPreanalysis_)
        updateIntervalPointerOffsets(stmt, intervalStatementInputs_.at(stmt));
    // NullPtr should not be changed by any statement. If the entry is missing
    // (not yet auto-inserted) we treat that as "unchanged" — only check the
    // entry if it actually exists.
}

void AbstractInterpretation::updateStateOnGep(const GepStmt* gep)
{
    const ICFGNode* node = gep->getICFGNode();
    const SVF::Interval offset = getGepElementIndex(gep);
    updateAddressSet(
        gep->getLHSVar(),
        getGepObjAddrs(SVFUtil::cast<ValVar>(gep->getRHSVar()), offset, node),
        node);
}

void AbstractInterpretation::updateStateOnSelect(const SelectStmt* select)
{
    const ICFGNode* node = select->getICFGNode();
    const SVF::Interval condition = getInterval(select->getCondition(), node);
    SVF::Interval interval;
    SVF::AddressSet addresses;
    std::vector<const SVFVar*> selectedValues;
    if (condition.isSingleton())
    {
        const SVFVar* selected = condition.isZero() ? select->getFalseValue()
                                 : select->getTrueValue();
        selectedValues.push_back(selected);
        interval = getInterval(selected, node);
        addresses = getAddressSet(selected, node);
    }
    else
    {
        selectedValues.push_back(select->getTrueValue());
        selectedValues.push_back(select->getFalseValue());
        interval = getInterval(select->getTrueValue(), node);
        interval.joinWith(getInterval(select->getFalseValue(), node));
        addresses = getAddressSet(select->getTrueValue(), node);
        addresses.joinWith(getAddressSet(select->getFalseValue(), node));
    }
    updateValue(select->getRes(), interval, addresses, node);

    if (numericalDomain() == AENumericalDomain::Box)
        return;
    const auto* target = SVFUtil::dyn_cast<ValVar>(select->getRes());
    if (!target || !adapter_.contains(*target))
        return;
    const SVF::Variable targetVariable = adapter_.variable(*target);
    std::optional<State> relationalSelect;
    for (const SVFVar* selected : selectedValues)
    {
        const auto* source = SVFUtil::dyn_cast<ValVar>(selected);
        if (!source || !adapter_.contains(*source))
        {
            relationalSelect.reset();
            break;
        }
        State alternative = phiAlternativeState(node);
        const SVF::Variable sourceVariable = adapter_.variable(*source);
        if (alternative.numericalMayBeUninitialized(sourceVariable))
        {
            relationalSelect.reset();
            break;
        }
        alternative.assignNumeric(targetVariable,
                                  SVF::LinearExpression(sourceVariable));
        recordRelationalDependency(targetVariable, sourceVariable);
        alternative.setAddressSet(targetVariable,
                                  alternative.addressSet(sourceVariable));
        if (!relationalSelect)
            relationalSelect = std::move(alternative);
        else
            relationalSelect->joinWith(alternative);
    }
    if (relationalSelect)
    {
        relationalSelect->numerical().project(
            relationalSelect->numerical().relationalClosure({targetVariable}));
        scalarTransferState(node).numerical().meetWith(
            relationalSelect->numerical());
        recordRelationalSummary(targetVariable, *relationalSelect, node);
    }
}

/// Phis of one basic block, possibly split across sequential ICFG nodes.
static std::vector<const PhiStmt*> blockPhiStatements(const SVFBasicBlock* block)
{
    std::vector<const PhiStmt*> phis;
    for (const ICFGNode* node : block->getICFGNodeList())
        for (const SVFStmt* statement : node->getSVFStmts())
            if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(statement))
                phis.push_back(phi);
    return phis;
}

/// Integer constants have no adapter coordinate (SVFIRAdapter skips constant
/// data); as phi operands they contribute their value.
static bool isNumericConstantOperand(const ValVar* value)
{
    return value && !value->isPointer() &&
           value->isConstDataOrAggDataButNotNullPtr();
}

bool AbstractInterpretation::phiEdgeBlock(const SVFBasicBlock* block)
{
    // SVF_AE_PHI_LEGACY=1 keeps the pre-D-009 per-phi transfer (ablation).
    static const bool legacy = std::getenv("SVF_AE_PHI_LEGACY") != nullptr;
    if (!block || legacy ||
            (sparsity() != Dense && !packSSAEnabled()))
        return false;
    const auto cached = phiEdgeBlocks_.find(block);
    if (cached != phiEdgeBlocks_.end())
        return cached->second;
    const std::vector<const PhiStmt*> phis = blockPhiStatements(block);
    bool edgeTransfer = !phis.empty() && !block->getICFGNodeList().empty();
    const ICFGNode* first =
        edgeTransfer ? block->getICFGNodeList().front() : nullptr;
    std::set<const ICFGNode*> predecessors;
    if (edgeTransfer)
        for (const ICFGEdge* edge : first->getInEdges())
        {
            edgeTransfer = edgeTransfer && SVFUtil::isa<IntraCFGEdge>(edge);
            predecessors.insert(edge->getSrcNode());
        }
    for (const PhiStmt* phi : phis)
    {
        if (!edgeTransfer)
            break;
        // The function-exit return phi keeps its undefined-return handling.
        const auto* target = SVFUtil::dyn_cast<ValVar>(phi->getRes());
        edgeTransfer = target && adapter_.contains(*target) &&
                       !phi->isFunctionRetPhi();
        for (u32_t i = 0; edgeTransfer && i < phi->getOpVarNum(); ++i)
        {
            const auto* source = SVFUtil::dyn_cast<ValVar>(phi->getOpVar(i));
            edgeTransfer = source && predecessors.count(phi->getOpICFGNode(i)) &&
                           (adapter_.contains(*source) ||
                            isNumericConstantOperand(source));
        }
        for (const ICFGNode* predecessor : predecessors)
        {
            unsigned matches = 0;
            for (u32_t i = 0; i < phi->getOpVarNum(); ++i)
                matches += phi->getOpICFGNode(i) == predecessor;
            edgeTransfer = edgeTransfer && matches == 1;
        }
    }
    if (!phis.empty() && !edgeTransfer)
        ++phiEdgeFallbackBlocks_;
    phiEdgeBlocks_.emplace(block, edgeTransfer);
    return edgeTransfer;
}

void AbstractInterpretation::applyPhiEdgeTransfer(
    State& state, const ICFGEdge* edge, const ICFGNode* target)
{
    const SVFBasicBlock* block = target ? target->getBB() : nullptr;
    if (!block || block->getICFGNodeList().empty() ||
            block->getICFGNodeList().front() != target || state.isBottom() ||
            !phiEdgeBlock(block))
        return;
    const ICFGNode* predecessor = edge->getSrcNode();
    // Every operand is read from the pre-edge state, so a phi that uses
    // another phi of the same block sees its previous value (a, b = b, a).
    const State before = state;
    SVF::LinearAssignmentList assignments;
    std::vector<std::pair<SVF::Variable, SVF::Interval>> unary;
    std::vector<SVF::Variable> mayBeUninitialized;
    std::vector<std::pair<SVF::Variable, SVF::Variable>> copies;
    for (const PhiStmt* phi : blockPhiStatements(block))
    {
        const ValVar* source = nullptr;
        for (u32_t i = 0; i < phi->getOpVarNum(); ++i)
            if (phi->getOpICFGNode(i) == predecessor)
                source = SVFUtil::dyn_cast<ValVar>(phi->getOpVar(i));
        const SVF::Variable targetVariable =
            adapter_.variable(*SVFUtil::cast<ValVar>(phi->getRes()));
        if (!adapter_.contains(*source))
        {
            const SVF::Interval value = getInterval(source, predecessor);
            if (value.isSingleton())
                assignments.push_back(
            {targetVariable, SVF::LinearExpression(value.singletonValue())});
            else
                unary.emplace_back(targetVariable, value);
            continue;
        }
        const SVF::Variable sourceVariable = adapter_.variable(*source);
        // Addresses, absent payloads and uninitialized-only values are copied
        // as whole coordinates; numerical values take part in the parallel
        // relational assignment.
        if (phi->getRes()->isPointer() || source->isPointer() ||
                before.interval(sourceVariable).isBottom() ||
                !before.addressSet(sourceVariable).isBottom())
        {
            copies.emplace_back(targetVariable, sourceVariable);
            continue;
        }
        assignments.push_back({targetVariable, SVF::LinearExpression(sourceVariable)});
        if (before.numericalMayBeUninitialized(sourceVariable))
            mayBeUninitialized.push_back(targetVariable);
    }
    if (!assignments.empty())
        state.assignNumericParallel(assignments);
    for (const auto& [variable, value] : unary)
        state.setInterval(variable, value);
    for (SVF::Variable variable : mayBeUninitialized)
        state.addUninitializedNumericalAlternative(variable);
    for (const auto& [variable, source] : copies)
    {
        state.assignValueFrom(variable, before, source);
        if (intervalPreanalysis_)
        {
            const auto* target = adapter_.value(variable);
            const auto* value = adapter_.value(source);
            if (target && target->isPointer() && value)
                state.setInterval(intervalOffsetVariable(target), intervalPointerOffset(value, before));
        }
    }
}

void AbstractInterpretation::updateStateOnPhi(const PhiStmt* phi)
{
    const ICFGNode* icfgNode = phi->getICFGNode();
    // D-009: the incoming edges already executed this block's phis.
    if (phiEdgeBlock(icfgNode->getBB()))
        return;
    const FunExitICFGNode* exit = icfgNode->getFun()
                                  ? icfg->getFunExitICFGNode(icfgNode->getFun())
                                  : nullptr;
    const bool isFormalReturn = exit && exit->getFormalRet() == phi->getRes();
    SVF::Interval interval = SVF::Interval::bottom();
    SVF::AddressSet addresses = SVF::AddressSet::bottom();
    std::optional<State> relationalPhi;
    bool relationalPhiComplete = true;
    for (u32_t i = 0; i < phi->getOpVarNum(); i++)
    {
        const ICFGNode* opICFGNode = phi->getOpICFGNode(i);
        if (hasAbsState(opICFGNode))
        {
            bool feasible = true;
            const ICFGEdge* edge =
                icfg->getICFGEdge(opICFGNode, icfgNode, ICFGEdge::IntraCF);
            if (edge)
            {
                const IntraCFGEdge* intraEdge =
                    SVFUtil::cast<IntraCFGEdge>(edge);
                if (intraEdge->getCondition())
                {
                    feasible = isBranchEdgeFeasibleAt(intraEdge, opICFGNode);
                }
            }
            if (feasible)
            {
                // A non-void source function that falls through has undefined
                // behavior. Clang lowers that path to an uninitialized return
                // slot; retain its guard for ordinary reads, but do not merge
                // the undefined alternative into the function's defined
                // return values.
                const SVF::Interval operandInterval =
                    isFormalReturn
                    ? getDefinedInterval(phi->getOpVar(i), opICFGNode)
                    : getInterval(phi->getOpVar(i), opICFGNode);
                interval.joinWith(operandInterval);
                if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
                    SVFUtil::outs()
                            << "AE_PHI_OPERAND target=" << phi->getRes()->getId()
                            << " source=" << phi->getOpVar(i)->getId()
                            << " node=" << opICFGNode->getId()
                            << " interval=" << operandInterval.toString() << '\n';
                addresses.joinWith(getAddressSet(phi->getOpVar(i),
                                                 opICFGNode));

                if (numericalDomain() != AENumericalDomain::Box)
                {
                    const auto* target =
                        SVFUtil::dyn_cast<ValVar>(phi->getRes());
                    const auto* source =
                        SVFUtil::dyn_cast<ValVar>(phi->getOpVar(i));
                    if (!target || !source || !adapter_.contains(*target) ||
                            !adapter_.contains(*source))
                    {
                        // A phi is a union of every feasible predecessor.  A
                        // relational summary built from only the representable
                        // operands would under-approximate that union when it
                        // is met back into the flow state.
                        relationalPhiComplete = false;
                        relationalPhi.reset();
                    }
                    else if (relationalPhiComplete)
                    {
                        State alternative = phiAlternativeState(opICFGNode);
                        const SVF::Variable sourceVariable =
                            adapter_.variable(*source);
                        if (alternative.numericalMayBeUninitialized(
                                    sourceVariable))
                        {
                            relationalPhiComplete = false;
                            relationalPhi.reset();
                        }
                        else
                        {
                            const SVF::Variable targetVariable =
                                adapter_.variable(*target);
                            alternative.assignNumeric(
                                targetVariable,
                                SVF::LinearExpression(sourceVariable));
                            recordRelationalDependency(targetVariable,
                                                       sourceVariable);
                            alternative.setAddressSet(
                                targetVariable,
                                alternative.addressSet(sourceVariable));
                            // Keep the selected source until the joined phi
                            // summary is projected.  For a root SSA value
                            // there is no earlier dependency through which
                            // target==source can be reconstructed; forgetting
                            // it here erases max/min relations after the two
                            // guarded alternatives are joined.
                            if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
                                SVFUtil::outs()
                                        << "AE_PHI_ALTERNATIVE target="
                                        << targetVariable.id() << " source="
                                        << sourceVariable.id() << " state="
                                        << alternative.numerical().toString()
                                        << '\n';
                            if (!relationalPhi)
                                relationalPhi = std::move(alternative);
                            else
                                relationalPhi->joinWith(alternative);
                            if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
                                SVFUtil::outs()
                                        << "AE_PHI_JOIN target="
                                        << targetVariable.id() << " state="
                                        << relationalPhi->numerical().toString()
                                        << '\n';
                        }
                    }
                }
            }
        }
    }
    if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
        SVFUtil::outs()
                << "AE_PHI_INTERVAL target="
                << adapter_.variable(*SVFUtil::cast<ValVar>(phi->getRes())).id()
                << " interval=" << interval.toString() << '\n';
    // Phi operands are read from their predecessor program points rather than
    // solely from the immediate incoming state. Preserve the preceding
    // iterate when a later predecessor has grown; otherwise a phi split across
    // sequential ICFG nodes can remain one iteration behind the backedge and
    // violate its transfer equation. Widening here treats every split phi as
    // part of the enclosing loop header and guarantees termination even when
    // it is not the WTO component's first ICFG node.
    if (const auto* result = SVFUtil::dyn_cast<ValVar>(phi->getRes());
            numericalDomain() != Box && result)
    {
        const auto history = phiIntervalHistory_.find(phi);
        SVF::Interval previous = history == phiIntervalHistory_.end()
                                 ? SVF::Interval::bottom() : history->second;
        const auto previousBeforeWiden = previous;
        // A non-recursive return joins observations from distinct callers;
        // it is not a loop header. Widening 2 with 3 here spuriously gives
        // [2,+inf]. Keep widening for cyclic/recursive phi propagation.
        if (isFormalReturn && !isRecursiveFun(icfgNode->getFun()))
            previous.joinWith(interval);
        else
            previous.widenWith(interval);
        if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
            SVFUtil::outs() << "AE_PHI_WIDEN target=" << adapter_.variable(*result).id()
                            << " previous=" << previousBeforeWiden.toString()
                            << " incoming=" << interval.toString()
                            << " next=" << previous.toString() << '\n';
        interval = std::move(previous);
        phiIntervalHistory_.insert_or_assign(phi, interval);
        SVF::AddressSet previousAddresses = getAddressSet(result, icfgNode);
        previousAddresses.joinWith(addresses);
        addresses = std::move(previousAddresses);
    }
    updateValue(phi->getRes(), interval, addresses, icfgNode);
    if (relationalPhiComplete && relationalPhi)
    {
        const auto* target = SVFUtil::dyn_cast<ValVar>(phi->getRes());
        if (target && adapter_.contains(*target))
        {
            const SVF::Variable targetVariable = adapter_.variable(*target);
            relationalPhi->numerical().project(
                relationalPhi->numerical().relationalClosure({targetVariable}));
            scalarTransferState(icfgNode).numerical().meetWith(
                relationalPhi->numerical());
            recordRelationalSummary(targetVariable, *relationalPhi, icfgNode);
        }
    }
}

void AbstractInterpretation::updateStateOnPhiGroupAtNode(
    const ICFGNode* node)
{
    if (!node || !node->getBB())
        return;
    const bool containsPhi =
        std::any_of(node->getSVFStmts().begin(), node->getSVFStmts().end(),
                    [](const SVFStmt* statement)
    {
        return SVFUtil::isa<PhiStmt>(statement);
    });
    if (!containsPhi || phiEdgeBlock(node->getBB()))
        return;

    // SVF may split one LLVM phi tuple across several sequential ICFG nodes.
    // Reconstruct the complete basic-block group and apply it once, after the
    // last split phi's independent product transfer.
    std::vector<const PhiStmt*> blockPhis;
    const ICFGNode* lastPhiNode = nullptr;
    for (const ICFGNode* blockNode : node->getBB()->getICFGNodeList())
        for (const SVFStmt* statement : blockNode->getSVFStmts())
            if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(statement))
            {
                blockPhis.push_back(phi);
                lastPhiNode = blockNode;
            }
    if (lastPhiNode == node)
        updateStateOnPhiGroup(blockPhis);
}

void AbstractInterpretation::updateStateOnPhiGroup(
    const std::vector<const PhiStmt*>& phis)
{
    if (numericalDomain() == AENumericalDomain::Box || phis.size() < 2)
        return;

    // Ignore non-numerical members without disabling a valid numerical tuple.
    // Pointer phis keep their ordinary address-set transfer.
    std::vector<const PhiStmt*> numericalPhis;
    for (const PhiStmt* phi : phis)
    {
        const auto* target = phi ? SVFUtil::dyn_cast<ValVar>(phi->getRes())
                             : nullptr;
        bool numerical = target && adapter_.contains(*target) &&
                         !target->isPointer();
        for (u32_t i = 0; numerical && i < phi->getOpVarNum(); ++i)
        {
            const auto* source =
                SVFUtil::dyn_cast<ValVar>(phi->getOpVar(i));
            numerical = source && adapter_.contains(*source) &&
                        !source->isPointer();
        }
        if (numerical)
            numericalPhis.push_back(phi);
    }
    if (numericalPhis.size() < 2)
        return;

    const ICFGNode* node = numericalPhis.back()->getICFGNode();
    const SVFBasicBlock* block = node ? node->getBB() : nullptr;
    if (!node || !block)
        return;

    std::vector<SVF::Variable> targets;
    targets.reserve(numericalPhis.size());
    std::set<SVF::Variable> uniqueTargets;
    for (const PhiStmt* phi : numericalPhis)
    {
        const auto* target = phi && phi->getICFGNode()->getBB() == block
                             ? SVFUtil::dyn_cast<ValVar>(phi->getRes())
                             : nullptr;
        if (!target || !adapter_.contains(*target))
            return;
        const SVF::Variable variable = adapter_.variable(*target);
        if (!uniqueTargets.insert(variable).second)
            return;
        targets.push_back(variable);
    }

    // Every phi in one SSA group must map exactly one operand to each of the
    // same predecessor program points.  If the frontend presents an
    // incomplete/non-canonical group, retain the already-applied independent
    // transfers rather than guessing a correlation.
    std::vector<const ICFGNode*> predecessors;
    for (u32_t i = 0; i < numericalPhis.front()->getOpVarNum(); ++i)
    {
        const ICFGNode* predecessor =
            numericalPhis.front()->getOpICFGNode(i);
        if (!predecessor ||
                std::find(predecessors.begin(), predecessors.end(),
                          predecessor) != predecessors.end())
            return;
        predecessors.push_back(predecessor);
    }
    for (const PhiStmt* phi : numericalPhis)
    {
        if (phi->getOpVarNum() != predecessors.size())
            return;
        for (const ICFGNode* predecessor : predecessors)
        {
            unsigned matches = 0;
            for (u32_t i = 0; i < phi->getOpVarNum(); ++i)
                matches += phi->getOpICFGNode(i) == predecessor;
            if (matches != 1)
                return;
        }
    }

    std::optional<State> joined;
    for (const ICFGNode* predecessor : predecessors)
    {
        if (!hasAbsState(predecessor))
            continue;

        const ICFGEdge* edge = nullptr;
        for (const PhiStmt* phi : numericalPhis)
            if ((edge = icfg->getICFGEdge(
                            predecessor, phi->getICFGNode(), ICFGEdge::IntraCF)))
                break;
        if (edge)
        {
            const auto* intra = SVFUtil::cast<IntraCFGEdge>(edge);
            if (intra->getCondition() &&
                    !isBranchEdgeFeasibleAt(intra, predecessor))
                continue;
        }

        State alternative = phiAlternativeState(predecessor);
        SVF::LinearAssignmentList assignments;
        std::vector<SVF::AddressSet> addresses;
        assignments.reserve(numericalPhis.size());
        addresses.reserve(numericalPhis.size());
        for (std::size_t phiIndex = 0;
                phiIndex < numericalPhis.size(); ++phiIndex)
        {
            const PhiStmt* phi = numericalPhis[phiIndex];
            const ValVar* source = nullptr;
            for (u32_t i = 0; i < phi->getOpVarNum(); ++i)
                if (phi->getOpICFGNode(i) == predecessor)
                {
                    source = SVFUtil::dyn_cast<ValVar>(phi->getOpVar(i));
                    break;
                }
            if (!source || !adapter_.contains(*source))
                return;
            const SVF::Variable sourceVariable = adapter_.variable(*source);
            if (alternative.numericalMayBeUninitialized(sourceVariable))
                return;
            assignments.push_back(
            {targets[phiIndex], SVF::LinearExpression(sourceVariable)});
            addresses.push_back(alternative.addressSet(sourceVariable));
            recordRelationalDependency(targets[phiIndex], sourceVariable);
        }

        alternative.assignNumericParallel(assignments);
        for (std::size_t i = 0; i < targets.size(); ++i)
            alternative.setAddressSet(targets[i], addresses[i]);
        if (!joined)
            joined = std::move(alternative);
        else
            joined->joinWith(alternative);
    }
    if (!joined)
        return;

    const std::vector<SVF::Variable> retained =
        joined->numerical().relationalClosure(targets);
    joined->numerical().project(retained);
    scalarTransferState(node).numerical().meetWith(joined->numerical());

    // Make a grouped relation reconstructible in Semi-Sparse mode.  All
    // targets form one simultaneous SSA definition tuple.  Keeping the tuple
    // together is conservative even when the backend ultimately represents
    // no relation between a particular pair; its projection will simply be
    // Top for that pair.
    for (SVF::Variable target : targets)
    {
        for (SVF::Variable peer : targets)
            if (peer != target)
                recordRelationalTupleDependency(target, peer);
        recordRelationalSummary(target, *joined, node);
    }

    if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
        SVFUtil::outs() << "AE_PHI_GROUP node=" << node->getId()
                        << " targets=" << targets.size() << " state="
                        << joined->numerical().toString() << '\n';
}

/// Handle CallPE: phi-like merging of actual parameters from all call sites
/// into the formal parameter at FunEntryICFGNode (e.g., formal =
/// join(actual1@cs1, actual2@cs2, ...))
void AbstractInterpretation::updateStateOnCall(const CallPE* callPE)
{
    const ICFGNode* node = callPE->getICFGNode();
    const SVFVar* res = callPE->getRes();
    const std::size_t callerCount = std::count_if(
                                        node->getInEdges().begin(), node->getInEdges().end(),
                                        [](const ICFGEdge* incoming)
    {
        return SVFUtil::isa<CallCFGEdge>(incoming);
    });
    const bool sharedContextInsensitiveFormal = callerCount > 1;
    SVF::Interval interval = SVF::Interval::bottom();
    SVF::AddressSet addresses = SVF::AddressSet::bottom();
    std::optional<State> relationalCall;
    for (u32_t i = 0; i < callPE->getOpVarNum(); i++)
    {
        const ICFGNode* opICFGNode = callPE->getOpCallICFGNode(i);
        if (hasAbsState(opICFGNode) && !state(opICFGNode).isBottom())
        {
            interval.joinWith(getInterval(callPE->getOpVar(i), opICFGNode));
            addresses.joinWith(getAddressSet(callPE->getOpVar(i),
                                             opICFGNode));
            if (numericalDomain() != AENumericalDomain::Box &&
                    Options::AERelationalCallPolicy() == ThroughCalls &&
                    !sharedContextInsensitiveFormal)
            {
                // A single formal shared by multiple call sites denotes the
                // join of distinct calling contexts. Caller-local SSA
                // coordinates do not identify which alternative supplied the
                // current invocation, so retaining formal--caller relations
                // would correlate different calls. Keep only the joined
                // unary value until the analysis has explicit contexts.
                const auto* target = SVFUtil::dyn_cast<ValVar>(res);
                const auto* source =
                    SVFUtil::dyn_cast<ValVar>(callPE->getOpVar(i));
                if (target && source && adapter_.contains(*target) &&
                        adapter_.contains(*source))
                {
                    State alternative = phiAlternativeState(opICFGNode);
                    const SVF::Variable sourceVariable =
                        adapter_.variable(*source);
                    if (!alternative.numericalMayBeUninitialized(
                                sourceVariable))
                    {
                        const SVF::Variable targetVariable =
                            adapter_.variable(*target);
                        alternative.assignNumeric(
                            targetVariable,
                            SVF::LinearExpression(sourceVariable));
                        recordRelationalDependency(targetVariable,
                                                   sourceVariable);
                        alternative.setAddressSet(
                            targetVariable,
                            alternative.addressSet(sourceVariable));
                        if (!relationalCall)
                            relationalCall = std::move(alternative);
                        else
                            relationalCall->joinWith(alternative);
                    }
                }
            }
        }
    }
    updateValue(res, interval, addresses, node);
    if (relationalCall)
    {
        const auto* target = SVFUtil::dyn_cast<ValVar>(res);
        if (target && adapter_.contains(*target))
        {
            const SVF::Variable targetVariable = adapter_.variable(*target);
            relationalCall->numerical().project(
                relationalCall->numerical().relationalClosure({targetVariable}));
            scalarTransferState(node).numerical().meetWith(
                relationalCall->numerical());
            recordRelationalSummary(targetVariable, *relationalCall, node);
        }
    }
}

void AbstractInterpretation::updateStateOnRet(const RetPE* retPE)
{
    const ICFGNode* node = retPE->getICFGNode();
    // Return edges already bind the result and instantiate the summary.
    if ((sparsity() == Dense || packSSAEnabled()) &&
            numericalDomain() != AENumericalDomain::Box)
        return;

    updateValue(retPE->getLHSVar(),
                getDefinedInterval(retPE->getRHSVar(), node),
                getAddressSet(retPE->getRHSVar(), node), node);
    if (numericalDomain() == AENumericalDomain::Box ||
            Options::AERelationalCallPolicy() == IntraproceduralCalls)
        return;
    // A context-insensitive callee summary shared by multiple call sites has
    // one formal-return ghost. Relating every actual return to that same ghost
    // would spuriously relate distinct calls (for example, r1 == r2). Keep the
    // joined interval/address result, but do not export an affine equality
    // unless the callee has a single call site.
    bool sharedCallee = false;
    if (const auto* returnSite = SVFUtil::dyn_cast<RetICFGNode>(node))
    {
        for (const ICFGEdge* edge : returnSite->getInEdges())
        {
            if (!SVFUtil::isa<RetCFGEdge>(edge) ||
                    !edge->getSrcNode()->getFun())
                continue;
            const ICFGNode* entry = icfg->getFunEntryICFGNode(
                                        edge->getSrcNode()->getFun());
            const std::size_t callers = std::count_if(
                                            entry->getInEdges().begin(),
                                            entry->getInEdges().end(),
                                            [](const ICFGEdge* incoming)
            {
                return SVFUtil::isa<CallCFGEdge>(incoming);
            });
            sharedCallee |= callers > 1;
        }
    }
    if (sharedCallee)
        return;
    const auto* target = SVFUtil::dyn_cast<ValVar>(retPE->getLHSVar());
    const auto* source = SVFUtil::dyn_cast<ValVar>(retPE->getRHSVar());
    if (!target || !source || !adapter_.contains(*target) ||
            !adapter_.contains(*source))
        return;
    const SVF::Variable sourceVariable = adapter_.variable(*source);
    const SVF::Interval sourceInterval = getDefinedInterval(source, node);
    if (!sourceInterval.isBottom())
        assignRelationalValue(target, SVF::LinearExpression(sourceVariable),
                              sourceInterval, getAddressSet(source, node), node);
}

void AbstractInterpretation::updateStateOnAddr(const AddrStmt* addr)
{
    const ICFGNode* node = addr->getICFGNode();
    const auto* object = SVFUtil::cast<ObjVar>(addr->getRHSVar());
    SVF::Interval interval = SVF::Interval::bottom();
    SVF::AddressSet addresses = SVF::AddressSet::bottom();
    initializeObjectValue(object, interval, addresses, node);
    if (addr->getRHSVar()->getType()->getKind() == SVFType::SVFIntegerTy)
        interval.meetWith(
            utils->getRangeLimitFromType(addr->getRHSVar()->getType()));
    updateValue(addr->getLHSVar(), interval, addresses, node);
    assignAllocationSize(addr);
}

void AbstractInterpretation::updateStateOnBinary(const BinaryOPStmt* binary)
{
    const ICFGNode* node = binary->getICFGNode();
    // Treat any unexpected bottom operand as unconstrained for soundness.
    SVF::Interval lhs = getInterval(binary->getOpVar(0), node);
    SVF::Interval rhs = getInterval(binary->getOpVar(1), node);
    if (lhs.isBottom())
        lhs = SVF::Interval::top();
    if (rhs.isBottom())
        rhs = SVF::Interval::top();
    SVF::Interval result;
    switch (binary->getOpcode())
    {
    case BinaryOPStmt::Add:
    case BinaryOPStmt::FAdd:
        result = SVF::add(lhs, rhs);
        break;
    case BinaryOPStmt::Sub:
    case BinaryOPStmt::FSub:
        result = SVF::subtract(lhs, rhs);
        break;
    case BinaryOPStmt::Mul:
    case BinaryOPStmt::FMul:
        result = SVF::multiply(lhs, rhs);
        break;
    case BinaryOPStmt::SDiv:
    case BinaryOPStmt::FDiv:
    case BinaryOPStmt::UDiv:
        result = SVF::divide(lhs, rhs);
        break;
    case BinaryOPStmt::SRem:
    case BinaryOPStmt::FRem:
    case BinaryOPStmt::URem:
        result = SVF::remainder(lhs, rhs);
        break;
    case BinaryOPStmt::Xor:
        result = SVF::bitwiseXor(lhs, rhs);
        break;
    case BinaryOPStmt::And:
        result = SVF::bitwiseAnd(lhs, rhs);
        break;
    case BinaryOPStmt::Or:
        result = SVF::bitwiseOr(lhs, rhs);
        break;
    case BinaryOPStmt::AShr:
        result = SVF::shiftRight(lhs, rhs);
        break;
    case BinaryOPStmt::Shl:
        result = SVF::shiftLeft(lhs, rhs);
        break;
    case BinaryOPStmt::LShr:
        result = SVF::shiftRight(lhs, rhs);
        break;
    default:
        assert(false && "undefined binary: ");
    }
    const auto* integerType =
        SVFUtil::dyn_cast<SVFIntegerType>(binary->getRes()->getType());
    const SVF::Interval typeRange =
        integerType && integerType->isBoolean() && numericalDomain() != AENumericalDomain::Box
        ? SVF::Interval::closed(SVF::Rational(0), SVF::Rational(1))
        : integerType ? utils->getRangeLimitFromType(binary->getRes()->getType())
        : SVF::Interval::top();
    const bool intervalProvesNoIntegerWrap =
        integerType && !result.isBottom() && result.isSubsetOf(typeRange);
    std::optional<SVF::LinearExpression> affine;
    SVF::Interval relationalResult = SVF::Interval::top();

    // Build the affine expression before deciding whether the operation can
    // wrap.  A relational domain can bound x-y exactly even when the unary
    // intervals of x and y are both Top.  Requiring operand-wise interval
    // arithmetic to prove no-wrap first would prevent Octagon/Polyhedra from
    // answering precisely the expressions they are designed to represent.
    if (numericalDomain() != AENumericalDomain::Box && integerType)
    {
        const auto expressionFor = [&](const SVFVar* operand)
                                   -> std::optional<SVF::LinearExpression>
        {
            if (const auto* value = SVFUtil::dyn_cast<ValVar>(operand))
            {
                if (adapter_.contains(*value))
                {
                    const SVF::Variable variable = adapter_.variable(*value);
                    if (getDefinedInterval(value, node).isBottom())
                        return std::nullopt;
                    return SVF::LinearExpression(variable);
                }
            }
            const SVF::Interval constant = getInterval(operand, node);
            if (constant.isSingleton())
                return SVF::LinearExpression(constant.singletonValue());
            return std::nullopt;
        };

        const auto lhsExpression = expressionFor(binary->getOpVar(0));
        const auto rhsExpression = expressionFor(binary->getOpVar(1));
        if (lhsExpression && rhsExpression)
        {
            if (binary->getOpcode() == BinaryOPStmt::Add)
                affine = *lhsExpression + *rhsExpression;
            else if (binary->getOpcode() == BinaryOPStmt::Sub)
                affine = *lhsExpression - *rhsExpression;
            else if (binary->getOpcode() == BinaryOPStmt::Mul)
            {
                if (lhs.isSingleton())
                    affine = lhs.singletonValue() * *rhsExpression;
                else if (rhs.isSingleton())
                    affine = rhs.singletonValue() * *lhsExpression;
            }
        }

        // Relational evaluation is normally a precision fallback.  A genuine
        // two-variable octagonal expression is also queried when intervals
        // already prove no-wrap so dense Post replay and semi-sparse transfer
        // agree on exact singleton folding (for example, x-a == 2).
        const bool exactOctagonalCandidate =
            affine && affine->terms().size() == 2;
        if (affine &&
                (!intervalProvesNoIntegerWrap || exactOctagonalCandidate))
        {
            State relationalState = ensureState(node);
            std::vector<SVF::Variable> variables;
            variables.reserve(affine->terms().size());
            for (const auto& [variable, coefficient] : affine->terms())
            {
                (void)coefficient;
                variables.push_back(variable);
            }
            materializeRelations(relationalState, variables, node);
            relationalResult = relationalState.numerical().bound(*affine);
        }
    }

    const bool relationProvesNoIntegerWrap =
        integerType && relationalResult.isSingleton() &&
        relationalResult.isSubsetOf(typeRange);
    const bool noIntegerWrap =
        intervalProvesNoIntegerWrap || relationProvesNoIntegerWrap;
    if (std::getenv("SVF_AE_TRACE_AFFINE_TRANSFER"))
        std::cerr << "AE affine candidate node=" << node->getId()
                  << " lhs=" << lhs.toString() << " rhs=" << rhs.toString()
                  << " result=" << result.toString()
                  << " relational=" << relationalResult.toString()
                  << " range="
                  << utils->getRangeLimitFromType(binary->getRes()->getType())
                  .toString()
                  << '\n';

    // Keep an affine equality when either interval arithmetic or the active
    // relational domain proves that the LLVM integer operation cannot wrap.
    // Floating-point operations retain interval semantics because rounding and
    // NaN behavior are not affine over rationals.
    if (numericalDomain() != AENumericalDomain::Box && noIntegerWrap)
    {
        const auto* resultValue =
            SVFUtil::dyn_cast<ValVar>(binary->getRes());
        if (affine && resultValue && adapter_.contains(*resultValue))
        {
            // Octagon cannot directly encode target = x-y because that
            // equality contains three variables.  If the pre-state proves the
            // right-hand side is a singleton, fold it before assignment so the
            // exact result survives in the target coordinate.
            const SVF::LinearExpression assignment =
                relationalResult.isSingleton()
                ? SVF::LinearExpression(relationalResult.singletonValue())
                : *affine;
            const SVF::Interval assignmentInterval =
                relationalResult.isSingleton() ? relationalResult : result;
            assignRelationalValue(resultValue, assignment, assignmentInterval,
                                  SVF::AddressSet::bottom(), node);
            return;
        }
    }
    if (numericalDomain() != AENumericalDomain::Box &&
            integerType && !noIntegerWrap)
        result = SVF::wrapIntegerInterval(
                     result, integerType->isBoolean() ? 1 : binary->getRes()->getType()->getByteSize() * 8,
                     integerType->isBoolean() ? false : integerType->isSigned());
    updateInterval(binary->getRes(), result, node);
}

void AbstractInterpretation::updateStateOnCmp(const CmpStmt* cmp)
{
    const ICFGNode* node = cmp->getICFGNode();
    SVF::Interval lhsInterval = getInterval(cmp->getOpVar(0), node);
    SVF::Interval rhsInterval = getInterval(cmp->getOpVar(1), node);
    const SVF::AddressSet lhsAddresses = getAddressSet(cmp->getOpVar(0), node);
    const SVF::AddressSet rhsAddresses = getAddressSet(cmp->getOpVar(1), node);
    const bool addressComparison = cmp->getOpVar(0)->isPointer();
    SVF::Interval result =
        SVF::Interval::closed(SVF::Rational(0), SVF::Rational(1));
    const auto boolean = [](bool value)
    {
        return SVF::Interval::singleton(SVF::Rational(value ? 1 : 0));
    };

    const auto predicate = cmp->getPredicate();
    const auto* operandType = SVFUtil::dyn_cast<SVFIntegerType>(cmp->getOpVar(0)->getType());
    const bool signedBoolean = numericalDomain() != AENumericalDomain::Box &&
                               operandType && operandType->isBoolean() &&
                               (predicate == CmpStmt::ICMP_SLT || predicate == CmpStmt::ICMP_SLE ||
                                predicate == CmpStmt::ICMP_SGT || predicate == CmpStmt::ICMP_SGE);
    if (signedBoolean)
    {
        const auto zero = SVF::Interval::singleton(SVF::Rational(0));
        lhsInterval = SVF::subtract(zero, lhsInterval);
        rhsInterval = SVF::subtract(zero, rhsInterval);
    }
    if (!addressComparison &&
            (lhsInterval.isBottom() || rhsInterval.isBottom()))
    {
        // Original skips this transfer, then reads a never-defined SSA result
        // as Top. Preserve any existing result on subsequent loop iterations.
        if (getInterval(cmp->getRes(), node).isBottom())
            updateInterval(cmp->getRes(), SVF::Interval::top(), node);
        return;
    }
    if (predicate == CmpStmt::FCMP_FALSE)
        result = boolean(false);
    else if (predicate == CmpStmt::FCMP_TRUE)
        result = boolean(true);
    else if (predicate == CmpStmt::FCMP_ORD || predicate == CmpStmt::FCMP_UNO)
    {
        // NaN is not tracked, so either outcome is possible.
    }
    else if (addressComparison)
    {
        const auto containsBlackHole = [&](const SVF::AddressSet& addresses)
        {
            if (!addresses.isFinite())
                return true;
            return std::any_of(addresses.begin(), addresses.end(),
                               [&](SVF::Location location)
            {
                const ObjVar* object = objectAt(location);
                const BaseObjVar* base = object
                                         ? svfir->getBaseObject(object->getId()) : nullptr;
                return base && base->isBlackHoleObj();
            });
        };
        const bool unknownAddress = containsBlackHole(lhsAddresses) ||
                                    containsBlackHole(rhsAddresses);
        const bool exact = lhsAddresses.isSingleton() &&
                           rhsAddresses.isSingleton() && !unknownAddress;
        const bool disjoint = lhsAddresses.isFinite() &&
                              rhsAddresses.isFinite() &&
                              !lhsAddresses.isBottom() &&
                              !rhsAddresses.isBottom() &&
                              !unknownAddress &&
                              !lhsAddresses.hasIntersection(rhsAddresses);
        switch (predicate)
        {
        case CmpStmt::ICMP_EQ:
        case CmpStmt::FCMP_OEQ:
        case CmpStmt::FCMP_UEQ:
            if (exact)
                result =
                    boolean(*lhsAddresses.begin() == *rhsAddresses.begin());
            else if (disjoint)
                result = boolean(false);
            break;
        case CmpStmt::ICMP_NE:
        case CmpStmt::FCMP_ONE:
        case CmpStmt::FCMP_UNE:
            if (exact)
                result =
                    boolean(*lhsAddresses.begin() != *rhsAddresses.begin());
            else if (disjoint)
                result = boolean(true);
            break;
        case CmpStmt::ICMP_UGT:
        case CmpStmt::ICMP_SGT:
        case CmpStmt::FCMP_OGT:
        case CmpStmt::FCMP_UGT:
        case CmpStmt::ICMP_UGE:
        case CmpStmt::ICMP_SGE:
        case CmpStmt::FCMP_OGE:
        case CmpStmt::FCMP_UGE:
        case CmpStmt::ICMP_ULT:
        case CmpStmt::ICMP_SLT:
        case CmpStmt::FCMP_OLT:
        case CmpStmt::FCMP_ULT:
        case CmpStmt::ICMP_ULE:
        case CmpStmt::ICMP_SLE:
        case CmpStmt::FCMP_OLE:
        case CmpStmt::FCMP_ULE:
            // Match Original's deliberate lack of pointer-order modelling,
            // including the same-known-singleton case. Equality is separate.
            break;
        default:
            assert(false && "undefined pointer compare");
        }
    }
    else
    {
        // Even when an operand is unconstrained, an LLVM comparison result is
        // still a Boolean.  Keeping [0, 1] here is both sound and important to
        // dense-equation replay: mathematical Top must not leak into the i1
        // result merely because a sparse operand summary is unavailable.
        switch (predicate)
        {
        case CmpStmt::ICMP_EQ:
        case CmpStmt::FCMP_OEQ:
        case CmpStmt::FCMP_UEQ:
            result = SVF::equalTo(lhsInterval, rhsInterval);
            break;
        case CmpStmt::ICMP_NE:
        case CmpStmt::FCMP_ONE:
        case CmpStmt::FCMP_UNE:
            result = SVF::notEqualTo(lhsInterval, rhsInterval);
            break;
        case CmpStmt::ICMP_UGT:
        case CmpStmt::ICMP_SGT:
        case CmpStmt::FCMP_OGT:
        case CmpStmt::FCMP_UGT:
            result = SVF::greaterThan(lhsInterval, rhsInterval);
            break;
        case CmpStmt::ICMP_UGE:
        case CmpStmt::ICMP_SGE:
        case CmpStmt::FCMP_OGE:
        case CmpStmt::FCMP_UGE:
            result = SVF::greaterEqual(lhsInterval, rhsInterval);
            break;
        case CmpStmt::ICMP_ULT:
        case CmpStmt::ICMP_SLT:
        case CmpStmt::FCMP_OLT:
        case CmpStmt::FCMP_ULT:
            result = SVF::lessThan(lhsInterval, rhsInterval);
            break;
        case CmpStmt::ICMP_ULE:
        case CmpStmt::ICMP_SLE:
        case CmpStmt::FCMP_OLE:
        case CmpStmt::FCMP_ULE:
            result = SVF::lessEqual(lhsInterval, rhsInterval);
            break;
        default:
            assert(false && "undefined numerical compare");
        }

        // Interval projection cannot prove comparisons such as x - y <= c
        // even when the selected relational domain entails them.  Ask the
        // numerical state directly before leaving a Boolean result at [0, 1].
        // Unsigned order predicates are excluded because their modular order
        // is not mathematical integer order.
        if (!signedBoolean && result == SVF::Interval::closed(SVF::Rational(0), SVF::Rational(1)))
        {
            const State pointLocal = ensureState(node);
            const bool separateScalarCarrier =
                getScalarAbstractState() != nullptr;
            State relationalQuery =
                separateScalarCarrier ? topState() : pointLocal;
            std::vector<SVF::Variable> relationVariables;
            std::set<NodeID> visiting;
            const auto lhs = reconstructLinearExpression(
                                 cmp->getOpVar(0), relationalQuery, node,
                                 relationVariables, kComparisonUnfoldDepth, visiting);
            const auto rhs = reconstructLinearExpression(
                                 cmp->getOpVar(1), relationalQuery, node,
                                 relationVariables, kComparisonUnfoldDepth, visiting);
            if (lhs && rhs)
            {
                materializeRelations(relationalQuery, relationVariables,
                                     node);
                // Semi-sparse coordinate materialization assigns each leaf
                // and would forget a relation already held in the same state.
                // Build definitions on a neutral carrier, then conjoin the
                // point-local branch refinement after materialization.
                if (separateScalarCarrier)
                    relationalQuery.numerical().meetWith(
                                       pointLocal.numerical());
                std::optional<SVF::LinearConstraint> truth;
                std::optional<SVF::LinearConstraint> falsity;
                switch (predicate)
                {
                case CmpStmt::ICMP_EQ:
                    truth = SVF::equal(*lhs, *rhs);
                    falsity = SVF::notEqual(*lhs, *rhs);
                    break;
                case CmpStmt::ICMP_NE:
                    truth = SVF::notEqual(*lhs, *rhs);
                    falsity = SVF::equal(*lhs, *rhs);
                    break;
                case CmpStmt::ICMP_SGT:
                    truth = SVF::greaterThan(*lhs, *rhs);
                    falsity = SVF::lessEqual(*lhs, *rhs);
                    break;
                case CmpStmt::ICMP_SGE:
                    truth = SVF::greaterEqual(*lhs, *rhs);
                    falsity = SVF::lessThan(*lhs, *rhs);
                    break;
                case CmpStmt::ICMP_SLT:
                    truth = SVF::lessThan(*lhs, *rhs);
                    falsity = SVF::greaterEqual(*lhs, *rhs);
                    break;
                case CmpStmt::ICMP_SLE:
                    truth = SVF::lessEqual(*lhs, *rhs);
                    falsity = SVF::greaterThan(*lhs, *rhs);
                    break;
                default:
                    break;
                }
                if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
                    SVFUtil::outs()
                            << "AE_CMP_QUERY node=" << node->getId()
                            << " lhs=" << lhs->toString()
                            << " rhs=" << rhs->toString()
                            << " state="
                            << relationalQuery.numerical().toString() << '\n';
                if (truth && relationalQuery.numerical().entails(*truth) ==
                        SVF::CheckResult::True)
                    result = boolean(true);
                else if (falsity &&
                         relationalQuery.numerical().entails(*falsity) ==
                         SVF::CheckResult::True)
                    result = boolean(false);
            }
        }
    }
    if (std::getenv("SVF_AE_TRACE_ADDRESS_TRANSFER") && addressComparison)
        SVFUtil::outs()
                << "AE_ADDRESS_CMP node=" << node->getId()
                << " function="
                << (node->getFun() ? node->getFun()->getName() : "<global>")
                << " predicate=" << predicate
                << " lhs_var=" << cmp->getOpVar(0)->getId()
                << " lhs=" << lhsAddresses.toString()
                << " rhs_var=" << cmp->getOpVar(1)->getId()
                << " rhs=" << rhsAddresses.toString()
                << " result=" << result.toString() << '\n';
    updateInterval(cmp->getRes(), result, node);
}

void AbstractInterpretation::updateStateOnLoad(const LoadStmt* load)
{
    const ICFGNode* node = load->getICFGNode();
    SVF::Interval interval;
    SVF::AddressSet addresses;
    bool numericalMayBeUninitialized = false;
    loadValue(SVFUtil::cast<ValVar>(load->getRHSVar()), interval, addresses,
              numericalMayBeUninitialized, node);
    if (std::getenv("SVF_AE_TRACE_ADDRESS_TRANSFER") &&
            load->getLHSVar()->isPointer())
        SVFUtil::outs()
                << "AE_ADDRESS_LOAD node=" << node->getId()
                << " function="
                << (node->getFun() ? node->getFun()->getName() : "<global>")
                << " target=" << load->getLHSVar()->getId()
                << " pointer=" << load->getRHSVar()->getId()
                << " pointees="
                << getAddressSet(load->getRHSVar(), node).toString()
                << " result=" << addresses.toString() << '\n';
    const SVF::AddressSet loadPointees = numericalDomain() == AENumericalDomain::Box
        ? SVF::AddressSet::bottom() : getAddressSet(load->getRHSVar(), node);
    std::optional<State> relationalBefore;
    if (numericalDomain() != AENumericalDomain::Box &&
            sparsity() != AESparsity::VersionedSparse && !loadPointees.isSingleton() && !loadPointees.hasUnknownObject())
        relationalBefore = ensureState(node);
    updateValue(load->getLHSVar(), interval, addresses, node);
    if (numericalMayBeUninitialized)
        addUninitializedNumericalAlternative(load->getLHSVar(), node);
    if (relationalBefore && !numericalMayBeUninitialized)
        joinRelationalMemory(SVFUtil::dyn_cast<ValVar>(load->getLHSVar()),
                             loadPointees, *relationalBefore, node, false);
    if (numericalDomain() != AENumericalDomain::Box)
    {
        const SVF::AddressSet& pointees = loadPointees;
        if (pointees.isSingleton())
        {
            const SVF::Location location = *pointees.begin();
            const ObjVar* object = location.isNull() ? nullptr
                                   : objectAt(location);
            if (object && canStrongStore(pointees, *object, state(node)))
                assignRelationalLoad(
                    SVFUtil::dyn_cast<ValVar>(load->getLHSVar()),
                    memoryVariable(*object, ensureState(node)), node);
        }
    }
}

void AbstractInterpretation::updateStateOnStore(const StoreStmt* store)
{
    const ICFGNode* node = store->getICFGNode();
    if (std::getenv("SVF_AE_TRACE_ADDRESS_TRANSFER") &&
            store->getRHSVar()->isPointer())
        SVFUtil::outs()
                << "AE_ADDRESS_STORE node=" << node->getId()
                << " function="
                << (node->getFun() ? node->getFun()->getName() : "<global>")
                << " pointer=" << store->getLHSVar()->getId()
                << " pointees="
                << getAddressSet(store->getLHSVar(), node).toString()
                << " source=" << store->getRHSVar()->getId()
                << " value="
                << getAddressSet(store->getRHSVar(), node).toString() << '\n';
    const SVF::AddressSet storePointees = numericalDomain() == AENumericalDomain::Box
        ? SVF::AddressSet::bottom() : getAddressSet(store->getLHSVar(), node);
    const auto* source = SVFUtil::dyn_cast<ValVar>(store->getRHSVar());
    std::optional<State> relationalBefore;
    if (numericalDomain() != AENumericalDomain::Box &&
            sparsity() != AESparsity::VersionedSparse && source &&
            (adapter_.contains(*source) || SVFUtil::isa<ConstIntValVar>(source) ||
             SVFUtil::isa<ConstFPValVar>(source)) && !storePointees.isSingleton() &&
            !storePointees.hasUnknownObject())
    {
        State& current = ensureState(node);
        for (SVF::Location location : storePointees.locations())
            if (!location.isNull())
                if (const ObjVar* object = objectAt(location))
                    memoryVariable(*object, current);
        relationalBefore = current;
        if (adapter_.contains(*source))
            materializeRelations(*relationalBefore, {adapter_.variable(*source)}, node);
    }
    storeValue(SVFUtil::cast<ValVar>(store->getLHSVar()),
               getInterval(store->getRHSVar(), node),
               getAddressSet(store->getRHSVar(), node), node);
    if (relationalBefore)
        joinRelationalMemory(source, storePointees, *relationalBefore, node, true);
    if (numericalDomain() != AENumericalDomain::Box)
    {
        const SVF::AddressSet& pointees = storePointees;
        if (pointees.isSingleton())
        {
            const SVF::Location location = *pointees.begin();
            const ObjVar* object = location.isNull() ? nullptr
                                   : objectAt(location);
            if (object && canStrongStore(pointees, *object, state(node)))
                assignRelationalStore(
                    SVFUtil::dyn_cast<ValVar>(store->getRHSVar()),
                    memoryVariable(*object, ensureState(node)), node);
        }
    }
}

void AbstractInterpretation::updateStateOnCopy(const CopyStmt* copy)
{
    const ICFGNode* node = copy->getICFGNode();
    const SVFVar* lhsVar = copy->getLHSVar();
    const SVFVar* rhsVar = copy->getRHSVar();

    const SVF::Interval rhsInterval = getInterval(rhsVar, node);
    const SVF::AddressSet rhsAddresses = getAddressSet(rhsVar, node);

    const auto* booleanType = SVFUtil::dyn_cast<SVFIntegerType>(rhsVar->getType());
    if (numericalDomain() != AENumericalDomain::Box && booleanType &&
            booleanType->isBoolean() && copy->getCopyKind() == CopyStmt::SEXT)
    {
        const SVF::Interval extended = SVF::subtract(SVF::Interval::singleton(SVF::Rational(0)), rhsInterval);
        const auto* value = SVFUtil::dyn_cast<ValVar>(rhsVar);
        const auto* target = SVFUtil::dyn_cast<ValVar>(lhsVar);
        if (value && target && adapter_.contains(*value) && adapter_.contains(*target))
            assignRelationalValue(target, SVF::LinearExpression(adapter_.variable(*value)) * SVF::Rational(-1),
                                  extended, rhsAddresses, node);
        else
            updateInterval(lhsVar, extended, node);
        return;
    }

    // D-005: the source is a machine value of its own type, so clip it to
    // that range before deciding whether sign extension is value-preserving.
    SVF::Interval rhsMachine = rhsInterval;
    if (!rhsMachine.isBottom() && SVFUtil::isa<SVFIntegerType>(rhsVar->getType()))
        rhsMachine.meetWith(utils->getRangeLimitFromType(rhsVar->getType()));
    const bool exactAffineCopy =
        numericalDomain() != AENumericalDomain::Box &&
        (copy->getCopyKind() == CopyStmt::COPYVAL ||
         copy->getCopyKind() == CopyStmt::SEXT ||
         (copy->getCopyKind() == CopyStmt::ZEXT && rhsInterval.lower().isFinite() &&
          rhsInterval.lower().value() >= SVF::Rational(0))) &&
        SVFUtil::isa<SVFIntegerType>(lhsVar->getType()) &&
        SVFUtil::isa<SVFIntegerType>(rhsVar->getType()) &&
        !rhsMachine.isBottom() &&
        rhsMachine.isSubsetOf(utils->getRangeLimitFromType(lhsVar->getType()));
    if (exactAffineCopy)
    {
        const auto* lhsValue = SVFUtil::dyn_cast<ValVar>(lhsVar);
        const auto* rhsValue = SVFUtil::dyn_cast<ValVar>(rhsVar);
        if (lhsValue && rhsValue && adapter_.contains(*lhsValue) &&
                adapter_.contains(*rhsValue))
        {
            const SVF::Variable source = adapter_.variable(*rhsValue);
            if (!getDefinedInterval(rhsValue, node).isBottom())
            {
                assignRelationalValue(lhsValue, SVF::LinearExpression(source),
                                      rhsInterval,
                                      rhsAddresses, node);
                return;
            }
        }
    }

    if (copy->getCopyKind() == CopyStmt::COPYVAL)
    {
        updateValue(lhsVar, rhsInterval, rhsAddresses, node);
    }
    else if (copy->getCopyKind() == CopyStmt::ZEXT)
    {
        const auto* sourceType =
            SVFUtil::dyn_cast<SVFIntegerType>(rhsVar->getType());
        updateInterval(lhsVar,
                       sourceType ? SVF::zeroExtendIntegerInterval(
                           rhsInterval,
                           rhsVar->getType()->getByteSize() * 8,
                           sourceType->isSigned())
                       : SVF::Interval::top(),
                       node);
    }
    else if (copy->getCopyKind() == CopyStmt::SEXT)
    {
        updateInterval(lhsVar, rhsInterval, node);
    }
    else if (copy->getCopyKind() == CopyStmt::FPTOSI)
    {
        updateInterval(
            lhsVar,
            SVF::floatToInteger(rhsInterval,
                                lhsVar->getType()->getByteSize() * 8, true),
            node);
    }
    else if (copy->getCopyKind() == CopyStmt::FPTOUI)
    {
        updateInterval(
            lhsVar,
            SVF::floatToInteger(rhsInterval,
                                lhsVar->getType()->getByteSize() * 8, false),
            node);
    }
    else if (copy->getCopyKind() == CopyStmt::SITOFP)
    {
        updateInterval(lhsVar, rhsInterval, node);
    }
    else if (copy->getCopyKind() == CopyStmt::UITOFP)
    {
        updateInterval(lhsVar, rhsInterval, node);
    }
    else if (copy->getCopyKind() == CopyStmt::TRUNC)
    {
        const auto* destinationType =
            SVFUtil::dyn_cast<SVFIntegerType>(lhsVar->getType());
        updateInterval(
            lhsVar,
            destinationType
            ? SVF::wrapIntegerInterval(rhsInterval,
                                       numericalDomain() != AENumericalDomain::Box && destinationType->isBoolean()
                                       ? 1 : lhsVar->getType()->getByteSize() * 8,
                                       numericalDomain() != AENumericalDomain::Box && destinationType->isBoolean()
                                       ? false : destinationType->isSigned())
            : SVF::Interval::top(),
            node);
    }
    else if (copy->getCopyKind() == CopyStmt::FPTRUNC)
    {
        updateInterval(lhsVar, rhsInterval, node);
    }
    else if (copy->getCopyKind() == CopyStmt::INTTOPTR)
    {
        // Without a provenance-preserving integer/pointer representation,
        // the cast can designate any modeled object (including a pointer
        // round trip). Empty would silently discard a subsequent store.
        updateValue(lhsVar, SVF::Interval::top(),
                    rhsInterval.isZero()
                    ? SVF::AddressSet::singleton(SVF::Location::null())
                    : SVF::AddressSet::top(), node);
    }
    else if (copy->getCopyKind() == CopyStmt::PTRTOINT)
    {
        updateInterval(lhsVar, SVF::Interval::top(), node);
    }
    else if (copy->getCopyKind() == CopyStmt::BITCAST)
    {
        if (!rhsAddresses.isBottom())
            updateValue(lhsVar, rhsInterval, rhsAddresses, node);
    }
    else
        assert(false && "undefined copy kind");
}
