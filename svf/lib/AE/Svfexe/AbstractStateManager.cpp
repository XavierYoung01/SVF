//===- AbstractStateManager.cpp -- AE state-access implementations ---//
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
// State-access bodies factored out of AbstractInterpretation.cpp /
// SparseAbstractInterpretation.cpp.  Class declarations stay in their
// respective headers; this file just hosts the implementations of the
// methods that used to live on the (now-folded) AbstractStateManager —
// trace lookup, value get/has/update, GEP / load / store helpers, and
// def/use queries — for dense and semi-sparse.  Full-sparse stubs and
// SVFG-backed overrides live in SparseAbstractInterpretation.cpp.
//

#include "AE/Svfexe/AllocationSize.h"
#include "AE/Svfexe/AbstractInterpretation.h"
#include "AE/Core/NumericalDomain.h"
#include "AE/Core/PartialRelationalDomain.h"
#include "AE/Core/PackedRelationalDomain.h"

#include "SVFIR/SVFIR.h"
#include "Util/Options.h"

#include <cassert>
#include <algorithm>
#include <cstdlib>
#include <iostream>

namespace SVF
{


namespace
{

bool isSignedNumericComparison(const CmpStmt* comparison)
{
    if (comparison->getOpVar(0)->isPointer())
        return false;
    const s32_t predicate = comparison->getPredicate();
    const auto* type = SVFUtil::dyn_cast<SVFIntegerType>(comparison->getOpVar(0)->getType());
    if (type && type->isBoolean() && predicate != CmpStmt::ICMP_EQ && predicate != CmpStmt::ICMP_NE)
        return false;
    return predicate == CmpStmt::ICMP_EQ || predicate == CmpStmt::ICMP_NE ||
           predicate == CmpStmt::ICMP_SLT || predicate == CmpStmt::ICMP_SLE ||
           predicate == CmpStmt::ICMP_SGT || predicate == CmpStmt::ICMP_SGE;
}

s64_t finiteEndpoint(const SVF::Bound& bound, s64_t fallback)
{
    if (!bound.isFinite())
        return fallback;
    std::int64_t result = 0;
    return bound.value().tryToInt64(result) ? result : fallback;
}

SVF::Interval finiteInterval(s64_t lower, s64_t upper)
{
    return SVF::Interval::closed(SVF::Rational(lower), SVF::Rational(upper));
}

bool constantInterval(const ValVar* value, SVF::Interval& interval,
                      AbstractInterpretation::AENumericalDomain domain)
{
    if (const auto* integer = SVFUtil::dyn_cast<ConstIntValVar>(value))
    {
        const auto* type = SVFUtil::dyn_cast<SVFIntegerType>(integer->getType());
        const bool boolean = domain != AbstractInterpretation::Box && type && type->isBoolean();
        interval = SVF::Interval::singleton(SVF::Rational(
                                                boolean ? (integer->getSExtValue() != 0 ? 1 : 0) : integer->getSExtValue()));
        return true;
    }
    if (const auto* floating = SVFUtil::dyn_cast<ConstFPValVar>(value))
    {
        interval = SVFIRAdapter::floatingConstant(floating->getFPValue());
        return true;
    }
    return false;
}

} // namespace

const SVF::AbstractDomain* AbstractInterpretation::getScalarAbstractState() const
{
    return nullptr;
}

void AbstractInterpretation::finalizeAbstractState(const ICFGNode*) {}

void AbstractInterpretation::updateInterval(const SVFVar* variable,
        const SVF::Interval& interval,
        const ICFGNode* node)
{
    updateValue(variable, interval, SVF::AddressSet::bottom(), node);
}

void AbstractInterpretation::updateAddressSet(const SVFVar* variable,
        const SVF::AddressSet& addresses,
        const ICFGNode* node)
{
    updateValue(variable, SVF::Interval::bottom(), addresses, node);
}

SVF::Interval AbstractInterpretation::getGepElementIndex(const GepStmt* gep)
{
    const ICFGNode* node = gep->getICFGNode();
    if (gep->isConstantOffset())
        return SVF::Interval::singleton(
                   SVF::Rational(static_cast<s64_t>(gep->accumulateConstantOffset())));

    SVF::Interval result = SVF::Interval::singleton(SVF::Rational());
    for (int index =
                static_cast<int>(gep->getOffsetVarAndGepTypePairVec().size()) - 1;
            index >= 0; --index)
    {
        const ValVar* variable =
            gep->getOffsetVarAndGepTypePairVec()[index].first;
        const SVFType* type =
            gep->getOffsetVarAndGepTypePairVec()[index].second;

        s64_t lower = 0;
        s64_t upper = 0;
        if (const auto* integer = SVFUtil::dyn_cast<ConstIntValVar>(variable))
        {
            lower = upper = integer->getSExtValue();
        }
        else
        {
            const SVF::Interval value = getInterval(variable, node);
            // Original treats an uninitialized index as zero, not as an
            // unknown range spanning every field. Keep this AE policy apart
            // from the domain's Top/Bottom and finite-endpoint semantics.
            if (!value.isBottom())
            {
                lower = finiteEndpoint(value.lower(), 0);
                upper = finiteEndpoint(value.upper(), Options::MaxFieldLimit());
            }
        }

        if (SVFUtil::isa<SVFPointerType>(type))
        {
            const u32_t elements = gep->getAccessPath().getElementNum(
                                       gep->getAccessPath().gepSrcPointeeType());
            lower = (double)Options::MaxFieldLimit() / elements < lower
                    ? Options::MaxFieldLimit()
                    : lower * elements;
            upper = (double)Options::MaxFieldLimit() / elements < upper
                    ? Options::MaxFieldLimit()
                    : upper * elements;
        }
        else if (Options::ModelArrays())
        {
            const std::vector<u32_t>& flattened =
                PAG::getPAG()->getTypeInfo(type)->getFlattenedElemIdxVec();
            if (flattened.empty() ||
                    upper >= static_cast<APOffset>(flattened.size()) || lower < 0)
            {
                lower = upper = 0;
            }
            else
            {
                lower = PAG::getPAG()->getFlattenedElemIdx(type, lower);
                upper = PAG::getPAG()->getFlattenedElemIdx(type, upper);
            }
        }
        else
        {
            lower = upper = 0;
        }
        result = SVF::add(result, finiteInterval(lower, upper));
    }
    result.meetWith(
        finiteInterval(0, static_cast<s64_t>(Options::MaxFieldLimit())));
    return result.isBottom() ? SVF::Interval::singleton(SVF::Rational()) : result;
}

SVF::Interval AbstractInterpretation::getGepByteOffset(const GepStmt* gep)
{
    const ICFGNode* node = gep->getICFGNode();
    if (gep->isConstantOffset())
        return SVF::Interval::singleton(SVF::Rational(
                                            static_cast<s64_t>(gep->accumulateConstantByteOffset())));

    SVF::Interval result = SVF::Interval::singleton(SVF::Rational());
    for (int index =
                static_cast<int>(gep->getOffsetVarAndGepTypePairVec().size()) - 1;
            index >= 0; --index)
    {
        const ValVar* variable =
            gep->getOffsetVarAndGepTypePairVec()[index].first;
        const SVFType* type =
            gep->getOffsetVarAndGepTypePairVec()[index].second;

        if (SVFUtil::isa<SVFArrayType>(type) ||
                SVFUtil::isa<SVFPointerType>(type))
        {
            u32_t elementSize = 1;
            if (const auto* array = SVFUtil::dyn_cast<SVFArrayType>(type))
                elementSize = array->getTypeOfElement()->getByteSize();
            else
                elementSize =
                    gep->getAccessPath().gepSrcPointeeType()->getByteSize();

            s64_t lower = 0;
            s64_t upper = 0;
            if (const auto* integer =
                        SVFUtil::dyn_cast<ConstIntValVar>(variable))
            {
                lower = upper = integer->getSExtValue();
            }
            else
            {
                const SVF::Interval value = getInterval(variable, node);
                lower = finiteEndpoint(value.lower(), 0);
                upper = finiteEndpoint(value.upper(),
                                       Options::MaxFieldLimit());
            }
            lower = std::max<s64_t>(0, lower);
            upper = std::max<s64_t>(0, upper);
            lower = (double)Options::MaxFieldLimit() / elementSize >= lower
                    ? lower * elementSize
                    : Options::MaxFieldLimit();
            upper = (double)Options::MaxFieldLimit() / elementSize >= upper
                    ? upper * elementSize
                    : Options::MaxFieldLimit();
            result = SVF::add(result, finiteInterval(lower, upper));
        }
        else if (const auto* structure = SVFUtil::dyn_cast<SVFStructType>(type))
        {
            const s64_t offset =
                gep->getAccessPath().getStructFieldOffset(variable, structure);
            result =
                SVF::add(result, SVF::Interval::singleton(SVF::Rational(offset)));
        }
        else
        {
            assert(false && "GEP type pair must be array, pointer, or structure");
            std::abort();
        }
    }
    return result;
}

SVF::AddressSet AbstractInterpretation::getGepObjAddrs(
    const ValVar* pointer, const SVF::Interval& offset, const ICFGNode* node)
{
    const SVF::AddressSet bases = getAddressSet(pointer, node);
    if (offset.isBottom())
        return SVF::AddressSet::bottom();

    // Empty is AE's no-target policy, not an unknown pointer. Flow-insensitive
    // points-to information must not resurrect targets killed by a later write.
    if (bases.isBottom())
        return SVF::AddressSet::bottom();

    SVF::AddressSet result = bases.hasUnknownObject()
                             ? SVF::AddressSet::objectTop()
                             : SVF::AddressSet::bottom();
    if (bases.mayContainRawAddress())
        result.joinWith(SVF::AddressSet::rawTop());
    if (bases.hasUnknownObject())
        return result;

    auto integerEndpoint = [](const SVF::Bound& bound,
                              bool lower) -> std::optional<APOffset>
    {
        if (!bound.isFinite())
        return std::nullopt;
        const SVF::Rational integer =
        lower ? (bound.isStrict() ? bound.value().floor() + SVF::Rational(1)
        : bound.value().ceil())
        : (bound.isStrict() ? bound.value().ceil() - SVF::Rational(1)
        : bound.value().floor());
        std::int64_t result = 0;
        if (!integer.tryToInt64(result))
            return std::nullopt;
        return result;
    };

    std::optional<APOffset> lower = integerEndpoint(offset.lower(), true);
    std::optional<APOffset> upper = integerEndpoint(offset.upper(), false);
    if (lower && upper && *lower > *upper)
        return SVF::AddressSet::bottom();

    // A finite narrow range must retain its signed offsets: negative GEPs are
    // common in C++ vtable and subobject adjustment. SVFIR canonicalizes each
    // signed offset modulo the base object's field limit. For an unbounded or
    // wider range, enumerating one complete global field window covers every
    // possible canonical field without an unbounded loop.
    bool enumerateFieldUniverse = !lower || !upper;
    if (!enumerateFieldUniverse)
    {
        enumerateFieldUniverse =
            SVF::Rational(*upper) - SVF::Rational(*lower) >
            SVF::Rational(static_cast<s64_t>(Options::MaxFieldLimit()));
    }
    if (enumerateFieldUniverse)
    {
        lower = 0;
        upper = static_cast<APOffset>(Options::MaxFieldLimit());
    }

    for (APOffset index = *lower;; ++index)
    {
        for (SVF::Location base : bases)
        {
            if (base.isNull())
                continue;
            const ObjVar* object = objectAt(base);
            if (!object)
                continue;
            const NodeID gepObject =
                svfir->getGepObjVar(object->getId(), index);
            const auto* gepVariable =
                SVFUtil::dyn_cast<ObjVar>(svfir->getSVFVar(gepObject));
            if (gepVariable)
                result.insert(locationOf(gepVariable));
        }
        if (index == *upper)
            break;
    }
    return result;
}

AbstractInterpretation::AllocationSizeBounds
AbstractInterpretation::getAllocaInstByteSize(const AddrStmt* address)
{
    const ICFGNode* node = address->getICFGNode();
    const auto* object = SVFUtil::dyn_cast<ObjVar>(address->getRHSVar());
    if (!object)
    {
        assert(false && "Addr rhs value is not ObjVar");
        std::abort();
    }
    const BaseObjVar* base = svfir->getBaseObject(object->getId());
    if (!base)
        return {0, Options::MaxFieldLimit()};
    if (base->isConstantByteSize())
    {
        const u32_t size = base->getByteSizeOfObj();
        return {size, size};
    }

    u64_t lower = address->getArrSize().empty() ? 0 : 1;
    u64_t upper = 1;
    const auto multiply = [](u64_t product, u64_t factor)
    {
        return factor != 0 && product > Options::MaxFieldLimit() / factor
               ? Options::MaxFieldLimit() : product * factor;
    };
    for (const SVFVar* value : address->getArrSize())
    {
        const SVF::Interval size = getInterval(value, node);
        const u64_t lb = size.isBottom() ? 0 : static_cast<u64_t>(std::clamp<s64_t>(
                finiteEndpoint(size.lower(), 0), 0, Options::MaxFieldLimit()));
        const u64_t ub = size.isBottom() ? Options::MaxFieldLimit() :
                         static_cast<u64_t>(std::clamp<s64_t>(
                                                finiteEndpoint(size.upper(), Options::MaxFieldLimit()),
                                                0, Options::MaxFieldLimit()));
        lower = multiply(lower, lb);
        upper = multiply(upper, ub);
    }
    return {static_cast<u32_t>(std::min(lower, upper)), static_cast<u32_t>(upper)};
}

const AllocationSizeModel& AbstractInterpretation::allocationSizeModel()
{
    if (!allocationSizeModel_)
    {
        allocationSizeModel_ = std::make_shared<AllocationSizeModel>(*svfir);
        if (std::getenv("SVF_AE_TRACE_SIZE"))
            for (const auto& size : allocationSizeModel_->all())
                std::cerr << "AE_SIZE_MODEL object=" << size.object->getId()
                          << " site_node=" << size.site->getICFGNode()->getId()
                          << " known=" << size.known
                          << " operand=" << (size.operand ? int(size.operand->getId()) : -1)
                          << " constant=" << size.constant
                          << " element_bytes=" << size.elementBytes
                          << " coefficient=" << size.strippedCoefficient << '\n';
    }
    return *allocationSizeModel_;
}

std::optional<s64_t> AbstractInterpretation::allocationByteLowerBound(
    const BaseObjVar* base)
{
    if (!base)
        return std::nullopt;
    const AllocationSize* size = allocationSizeModel().find(base);
    if (size && size->known && !size->sizeValue && size->elementBytes > 0)
        return size->constant * static_cast<s64_t>(size->elementBytes);
    if (size && size->known && size->sizeValue && size->elementBytes > 0 &&
            size->elementBytes % size->strippedCoefficient == 0)
    {
        // Every allocation at this site happens at its node, so the fixpoint
        // interval of the size value covers all of them. Use its lower
        // bound: an upper bound would accept accesses past smaller objects.
        const ICFGNode* node = size->site->getICFGNode();
        if (!hasAbsState(node))
            return std::nullopt;
        const SVF::Interval count = getInterval(size->sizeValue, node);
        if (count.isBottom())
            return std::nullopt;
        SVF::Rational lower(0);
        if (count.lower().isFinite() && count.lower().value() > lower)
            lower = count.lower().value().floor();
        const s64_t unit = size->elementBytes / size->strippedCoefficient;
        return std::stoll(((lower + SVF::Rational(size->elementOffset)) *
                          SVF::Rational(unit)).toString());
    }
    if (size)
        return std::nullopt;
    if (base->isConstantByteSize())
        return base->getByteSizeOfObj();
    return std::nullopt;
}

SVF::Interval AbstractInterpretation::unknownInterval(const SVFVar* var) const
{
    // The upstream Box interpreter uses mathematical intervals for unknown
    // numerical inputs. Machine-range guards belong to relational execution.
    if (numericalDomain() == AENumericalDomain::Box)
        return SVF::Interval::top();
    // An LLVM integer value lies in its type range whatever produced it.
    // Without this bound, x+1 on an unknown i32 looks able to wrap and the
    // executor drops every relation of the result (T-011 CASE3).
    if (var && SVFUtil::isa<SVFIntegerType>(var->getType()))
        return utils->getRangeLimitFromType(var->getType());
    return SVF::Interval::top();
}

void AbstractInterpretation::assignAllocationSize(const AddrStmt* addr)
{
    // Dense and pack-location storage carry synthetic size coordinates.
    if (sparsity() != AbstractInterpretation::Dense &&
            !packSSAEnabled())
        return;
    const AllocationSize* size = allocationSizeModel().find(addr);
    if (!size)
        return;
    const ICFGNode* node = addr->getICFGNode();
    State& denseState = ensureState(node);
    if (denseState.isBottom())
        return;
    const SVF::Variable target = adapter_.sizeVariable(*size->object);
    const bool weak = std::getenv("SVF_AE_SIZE_WEAK") != nullptr;
    State written(denseState);
    State& output = weak ? written : denseState;
    SVF::Interval value = SVF::Interval::top();
    std::optional<SVF::LinearExpression> expression;
    if (size->known && !size->sizeValue)
        value = SVF::Interval::singleton(SVF::Rational(size->constant));
    else if (size->known && size->sizeValue)
    {
        // Size(o) = sizeValue / strippedCoefficient (element units). It is
        // the stripped operand only if no stripped cast or multiplication
        // can wrap: the operand must be non-negative and coefficient *
        // operand must fit every integer type on the stripped chain.
        const SVF::Rational coefficient(size->strippedCoefficient);
        const SVF::Interval count = getInterval(size->sizeValue, node);
        if (!count.isBottom())
            value = SVF::Interval(
                        count.lower().isFinite()
                        ? SVF::Bound::finite((count.lower().value() / coefficient).floor())
                        : SVF::Bound::minusInfinity(),
                        count.upper().isFinite()
                        ? SVF::Bound::finite((count.upper().value() / coefficient).ceil())
                        : SVF::Bound::plusInfinity());
        if (const auto* operand = size->operand)
        {
            s64_t stripped = 1;
            std::vector<const SVFVar*> chain;
            AllocationSizeModel::stripCoefficient(size->sizeValue, stripped, &chain);
            // A machine value lies in its own type's range even when the
            // mathematical interval has not been clipped to it.
            SVF::Interval source = getDefinedInterval(operand, node);
            if (!source.isBottom() && operand->getType())
                source.meetWith(utils->getRangeLimitFromType(operand->getType()));
            bool exact = adapter_.contains(*operand) && !source.isBottom() &&
                         source.lower().isFinite() &&
                         source.lower().value() >= SVF::Rational(0);
            const SVF::Interval scaled = exact
                                         ? SVF::multiply(source, SVF::Interval::singleton(coefficient))
                                         : SVF::Interval::top();
            for (const SVFVar* step : chain)
                exact = exact && step->getType() &&
                        scaled.isSubsetOf(utils->getRangeLimitFromType(step->getType()));
            if (std::getenv("SVF_AE_TRACE_SIZE"))
                std::cerr << "AE_SIZE_OPERAND object=" << size->object->getId()
                          << " operand=" << operand->getId() << " source=" << source.toString()
                          << " count=" << count.toString() << " chain=" << chain.size()
                          << " exact=" << exact << '\n';
            if (exact)
                expression = SVF::LinearExpression(adapter_.variable(*operand));
        }
    }
    if (size->elementOffset)
    {
        const SVF::LinearExpression offset(SVF::Rational(size->elementOffset));
        value = SVF::add(value, SVF::Interval::singleton(SVF::Rational(size->elementOffset)));
        if (expression)
            *expression = *expression + offset;
    }
    if (std::getenv("SVF_AE_TRACE_SIZE"))
        std::cerr << "AE_SIZE_ASSIGN object=" << size->object->getId()
                  << " node=" << node->getId() << " known=" << size->known
                  << " relational=" << bool(expression) << " value=" << value.toString()
                  << " element_bytes=" << size->elementBytes << '\n';
    if (expression)
        output.assignNumeric(target, *expression);
    else
        assignInterval(output, target, value);
    if (weak)
        denseState.joinWith(written);
}

const SVF::AbstractDomain& AbstractInterpretation::
getAbstractState(const ICFGNode* node) const
{
    return state(node);
}

bool AbstractInterpretation::hasAbsState(const ICFGNode* node) const
{
    return abstractTrace_.count(node) != 0;
}

SVF::Location AbstractInterpretation::locationOf(const ObjVar* object) const
{
    return object ? adapter_.location(*object) : SVF::Location::null();
}

const ObjVar* AbstractInterpretation::objectAt(SVF::Location location) const
{
    return location.isNull() ? nullptr : &adapter_.object(location);
}

AbstractInterpretation::State AbstractInterpretation::topState()
const
{
    return State(makeNumericalDomain(false), adapter_.memoryLayout(), true);
}

AbstractInterpretation::State AbstractInterpretation::
bottomState() const
{
    return State(makeNumericalDomain(true), adapter_.memoryLayout(), true);
}

std::unique_ptr<SVF::NumericalDomain>
AbstractInterpretation::makeNumericalDomain(bool bottom) const
{
    if (relationalPolicy() == SyntaxPackedRelational ||
            relationalPolicy() == ClosurePackedRelational ||
            relationalPolicy() == ImpactPackedRelational ||
            relationalPolicy() == LearnedPackedRelational ||
            relationalPolicy() == DuetPackedRelational ||
            relationalPolicy() == SpePackedRelational)
    {
        if (!relationalPacking_ || numericalDomain() != Octagon)
        {
            assert(false && "packed policies require initialized native Octagon packing");
            std::abort();
        }
        return std::make_unique<SVF::PackedRelationalDomain>(relationalPacking_, bottom);
    }
    if (relationalPolicy() != WholeRelational &&
            numericalDomain() != AENumericalDomain::Box)
    {
        if (!relationalVocabulary_)
        {
            assert(false && "partial relational vocabulary was not initialized");
            std::abort();
        }
        const SVF::DomainKind kind =
            numericalDomain() == AENumericalDomain::Octagon
            ? SVF::DomainKind::Octagon
            : SVF::DomainKind::ConvexPolyhedra;
        return std::make_unique<SVF::PartialRelationalDomain>(
                   bottom
                   ? SVF::PartialRelationalDomain::bottom(
                       kind, relationalVocabulary_)
                   : SVF::PartialRelationalDomain::top(
                       kind, relationalVocabulary_));
    }
    SVF::DomainKind kind = SVF::DomainKind::Box;
    switch (numericalDomain())
    {
    case AENumericalDomain::Octagon:
        kind = SVF::DomainKind::Octagon;
        break;
    case AENumericalDomain::Polyhedra:
        kind = SVF::DomainKind::ConvexPolyhedra;
        break;
    case AENumericalDomain::Box:
    default:
        break;
    }
    SVF::OctagonConfig config;
    config.storage = SVF::OctagonStorageKind::ComponentDense;
    return SVF::makeNumericalDomain(kind, bottom, config);
}

AbstractInterpretation::State& AbstractInterpretation::
ensureState(const ICFGNode* node)
{
    if (recheckStates_)
    {
        auto final = recheckStates_->find(node);
        if (final != recheckStates_->end())
            return final->second;
    }
    auto iterator = abstractTrace_.find(node);
    if (iterator == abstractTrace_.end())
        iterator = abstractTrace_.emplace(node, topState()).first;
    return iterator->second;
}

const AbstractInterpretation::State& AbstractInterpretation::
state(const ICFGNode* node) const
{
    if (recheckStates_)
    {
        auto final = recheckStates_->find(node);
        if (final != recheckStates_->end())
            return final->second;
    }
    const auto iterator = abstractTrace_.find(node);
    if (iterator == abstractTrace_.end())
    {
        assert(false && "no dense abstract state for ICFG node");
        std::abort();
    }
    return iterator->second;
}

AbstractInterpretation::State& AbstractInterpretation::
scalarTransferState(const ICFGNode* node)
{
    return ensureState(node);
}

AbstractInterpretation::State AbstractInterpretation::
phiAlternativeState(const ICFGNode* predecessor)
{
    return state(predecessor);
}

void AbstractInterpretation::assignRelationalValue(
    const ValVar* target, const SVF::LinearExpression& expression,
    const SVF::Interval& interval, const SVF::AddressSet& addresses,
    const ICFGNode* node)
{
    if (!target || !adapter_.contains(*target))
        return;
    State& destination = ensureState(node);
    const SVF::Variable variable = adapter_.variable(*target);
    destination.assignNumeric(variable, expression);
    (void)interval;
    destination.setAddressSet(variable, addresses);
}

void AbstractInterpretation::recordRelationalDependency(SVF::Variable,
        SVF::Variable)
{
}

void AbstractInterpretation::recordRelationalTupleDependency(
    SVF::Variable target, SVF::Variable peer)
{
    recordRelationalDependency(target, peer);
}

void AbstractInterpretation::recordRelationalSummary(SVF::Variable, const State&,
        const ICFGNode*)
{
}

void AbstractInterpretation::assignRelationalStore(
    const ValVar* source, SVF::Variable content, const ICFGNode* node)
{
    if (!source || !adapter_.contains(*source))
        return;
    State& destination = ensureState(node);
    const SVF::Variable sourceVariable = adapter_.variable(*source);
    if (!destination.numericalMayBeUninitialized(sourceVariable))
        // storeValue has already installed both value facets and their
        // initialization guards.  This second assignment only records the
        // affine relation; assignNumeric would erase a pointer payload.
        destination.numerical().assign(
                       content, SVF::LinearExpression(sourceVariable));
}

void AbstractInterpretation::assignRelationalLoad(
    const ValVar* target, SVF::Variable content, const ICFGNode* node)
{
    if (!target || !adapter_.contains(*target))
        return;
    State& destination = ensureState(node);
    if (!destination.numericalMayBeUninitialized(content))
        // updateValue has already installed both value facets and their
        // initialization guards.  Preserve a loaded pointer while refining
        // only the numerical relation.
        destination.numerical().assign(adapter_.variable(*target),
                                       SVF::LinearExpression(content));
}

void AbstractInterpretation::joinRelationalMemory(
    const ValVar* value, const SVF::AddressSet& pointees,
    const State& before, const ICFGNode* node, bool store)
{
    if (!value || pointees.hasUnknownObject())
        return;
    const auto variable = adapter_.contains(*value)
        ? std::optional<SVF::Variable>(adapter_.variable(*value)) : std::nullopt;
    if (!variable && (!store || (!SVFUtil::isa<ConstIntValVar>(value) &&
                                !SVFUtil::isa<ConstFPValVar>(value))))
        return;
    if (store && variable &&
            scalarTransferState(node).numericalMayBeUninitialized(*variable))
        return;
    const SVF::Interval literal = variable ? SVF::Interval::top()
                                           : getInterval(value, node);
    std::optional<State> joined;
    std::size_t alternatives = 0;
    for (SVF::Location location : pointees.locations())
    {
        const ObjVar* object = location.isNull() ? nullptr : objectAt(location);
        if (!object || !before.memoryLayout().contains(location))
            return;
        State alternative(before);
        const SVF::Variable content = memoryVariable(*object, alternative);
        if (!store && alternative.numericalMayBeUninitialized(content))
            return;
        const bool precise = canStrongStore(
            SVF::AddressSet::singleton(location), *object, before);
        if (store)
        {
            if (variable)
                alternative.numerical().assign(content, SVF::LinearExpression(*variable));
            else
                alternative.numerical().assignBound(content, literal);
            if (!precise)
                alternative.numerical().joinWith(before.numerical());
        }
        else if (precise)
            alternative.numerical().assign(*variable, SVF::LinearExpression(content));
        else
            alternative.numerical().assignBound(*variable, before.interval(content));
        if (!joined)
            joined = std::move(alternative);
        else
            joined->numerical().joinWith(alternative.numerical());
        ++alternatives;
    }
    if (!joined)
        return;
    // Scalar transfer already set address and initialization facets. Refine
    // its numerical result with the join of mutually exclusive targets.
    ensureState(node).numerical().meetWith(joined->numerical());
    if (!store)
        publishRelationalLoad(value, node);
    if (std::getenv("SVF_AE_TRACE_MEMORY_JOINS"))
        SVFUtil::outs() << "AE_MEMORY_JOIN node=" << node->getId()
                       << " kind=" << (store ? "store" : "load")
                       << " alternatives=" << alternatives << '\n';
}

void AbstractInterpretation::publishRelationalLoad(
    const ValVar*, const ICFGNode*)
{
}

void AbstractInterpretation::resetAbstractState(const ICFGNode* node)
{
    abstractTrace_.insert_or_assign(node, topState());
}

void AbstractInterpretation::copyAbstractState(const ICFGNode* source,
        const ICFGNode* destination)
{
    abstractTrace_.insert_or_assign(destination, state(source));
}

std::unique_ptr<SVF::AbstractDomain> AbstractInterpretation::
cloneAbstractState(const ICFGNode* node) const
{
    return state(node).clone();
}

void AbstractInterpretation::assignInterval(State& denseState,
        SVF::Variable variable,
        const SVF::Interval& interval)
{
    denseState.setInterval(variable, interval);
}

void AbstractInterpretation::constrainInterval(
    State& denseState, SVF::Variable variable,
    const SVF::Interval& interval) const
{
    if (interval.isBottom())
        return;

    // Constraints refine an initialized observation. Keep Top observations
    // defined even when they need no Box payload slot.
    if (denseState.interval(variable).isBottom())
        denseState.setInterval(variable, SVF::Interval::top());

    SVF::LinearConstraintSet constraints;
    SVF::LinearExpression expression(variable);
    if (interval.lower().isFinite())
    {
        constraints.emplace_back(
            expression - SVF::LinearExpression(interval.lower().value()),
            interval.lower().isStrict() ? SVF::ConstraintKind::GreaterThan
            : SVF::ConstraintKind::GreaterEqual);
    }
    if (interval.upper().isFinite())
    {
        constraints.emplace_back(
            expression - SVF::LinearExpression(interval.upper().value()),
            interval.upper().isStrict() ? SVF::ConstraintKind::LessThan
            : SVF::ConstraintKind::LessEqual);
    }
    denseState.numerical().assumeAll(constraints);
}

void AbstractInterpretation::assignValue(State& denseState,
        SVF::Variable variable,
        const SVF::Interval& interval,
        const SVF::AddressSet& addresses)
{
    // SVF's synthetic extractvalue/extractelement edges can give even an
    // integer-typed SSA value an address facet. Preserve both facets through
    // assignment and a later store, just as for pointer-typed unknown values.
    assignInterval(denseState, variable, interval);
    denseState.setAddressSet(variable, addresses);
}

void AbstractInterpretation::assignMemoryValue(
    State& denseState, SVF::Variable content,
    const SVF::Interval& interval, const SVF::AddressSet& addresses)
{
    assignInterval(denseState, content, interval);
    denseState.setAddressSet(content, addresses);
}

SVF::Variable AbstractInterpretation::memoryVariable(
    const ObjVar& object, const State& denseState) const
{
    // Original's getIDFromAddr redirects freed-object accesses to its
    // BlackHole memory cell. This is an interpreter policy, not Address Top.
    if (denseState.lifetimes().mayBeFreed(adapter_.location(object)))
        return adapter_.contentVariable(*SVFUtil::cast<ObjVar>(
                                            svfir->getGNode(svfir->getBlackHoleNode())));
    return adapter_.contentVariable(object);
}

void AbstractInterpretation::materializeValue(State&, const ValVar*,
        const ICFGNode*)
{
}

void AbstractInterpretation::materializeRelations(
    State&, const std::vector<SVF::Variable>&, const ICFGNode*)
{
}

void AbstractInterpretation::forgetValue(State& denseState,
        SVF::Variable variable) const
{
    denseState.resetValue(variable);
}

SVF::Interval AbstractInterpretation::getInterval(const ValVar* var,
        const ICFGNode* node)
{
    const SVF::Interval result = getDefinedInterval(var, node);
    // Upstream reads the stored interval even when an uninitialized
    // alternative is present; initialization remains a separate detector fact.
    if (numericalDomain() == AENumericalDomain::Box ||
            !var || !adapter_.contains(*var))
        return result;
    const State& denseState = ensureState(node);
    return denseState.numericalMayBeUninitialized(adapter_.variable(*var))
           ? SVF::Interval::top() : result;
}

SVF::Interval AbstractInterpretation::getDefinedInterval(const ValVar* var,
        const ICFGNode* node)
{
    SVF::Interval constant;
    if (constantInterval(var, constant, numericalDomain()))
        return constant;
    // SVFIR also uses its canonical unknown pointer as the numeric source of
    // nondeterministic external-input stores (STORE_TOP annotations).
    if (var->getId() == svfir->getBlkPtr() ||
            SVFUtil::isa<BlackHoleValVar>(var))
        return SVF::Interval::top();
    if (!adapter_.contains(*var))
        return SVF::Interval::top();

    const State& denseState = ensureState(node);
    if (denseState.isBottom())
        return SVF::Interval::bottom();
    const SVF::Variable variable = adapter_.variable(*var);
    // Global initializers can refer to a function/global before its AddrStmt.
    // This is an unresolved symbolic value, not an uninitialized memory load.
    if ((SVFUtil::isa<FunValVar>(var) || SVFUtil::isa<GlobalValVar>(var)) &&
            !denseState.hasValue(variable))
        return SVF::Interval::top();
    return denseState.interval(variable);
}

SVF::Interval AbstractInterpretation::getInterval(const ObjVar* var,
        const ICFGNode* node)
{
    const State& denseState = ensureState(node);
    const SVF::Variable content = memoryVariable(*var, denseState);
    return denseState.interval(content);
}

SVF::Interval AbstractInterpretation::getInterval(const SVFVar* var,
        const ICFGNode* node)
{
    if (const auto* object = SVFUtil::dyn_cast<ObjVar>(var))
        return getInterval(object, node);
    if (const auto* value = SVFUtil::dyn_cast<ValVar>(var))
        return getInterval(value, node);
    assert(false && "unsupported SVF variable kind");
    std::abort();
}

SVF::AddressSet AbstractInterpretation::getAddressSet(const ValVar* var,
        const ICFGNode* node)
{
    if (var->getId() == IRGraph::NullPtr ||
            SVFUtil::isa<ConstNullPtrValVar>(var))
        return SVF::AddressSet::singleton(SVF::Location::null());
    if (var->getId() == svfir->getBlkPtr() ||
            SVFUtil::isa<BlackHoleValVar>(var))
        return blackHoleAddressSet();
    if (!adapter_.contains(*var))
        return SVF::AddressSet::bottom();
    const State& denseState = ensureState(node);
    const SVF::Variable variable = adapter_.variable(*var);
    return denseState.addressSet(variable);
}

SVF::AddressSet AbstractInterpretation::getAddressSet(const ObjVar* var,
        const ICFGNode* node)
{
    const State& denseState = ensureState(node);
    const SVF::Variable content = memoryVariable(*var, denseState);
    return denseState.addressSet(content);
}

SVF::AddressSet AbstractInterpretation::getAddressSet(const SVFVar* var,
        const ICFGNode* node)
{
    if (const auto* object = SVFUtil::dyn_cast<ObjVar>(var))
        return getAddressSet(object, node);
    if (const auto* value = SVFUtil::dyn_cast<ValVar>(var))
        return getAddressSet(value, node);
    assert(false && "unsupported SVF variable kind");
    std::abort();
}

bool AbstractInterpretation::hasAbsValue(const ValVar* var,
        const ICFGNode* node) const
{
    if (SVFUtil::isa<ConstIntValVar>(var) ||
            SVFUtil::isa<ConstFPValVar>(var))
        return true;
    return abstractTrace_.count(node) != 0 && adapter_.contains(*var);
}

bool AbstractInterpretation::hasAbsValue(const ObjVar* var,
        const ICFGNode* node) const
{
    const auto stateIterator = abstractTrace_.find(node);
    if (stateIterator == abstractTrace_.end())
        return false;
    // Defined Top is a real incoming definition even without a payload slot.
    // Inspect both guards because aggregate cells can carry either facet.
    const SVF::Variable content = adapter_.contentVariable(*var);
    return stateIterator->second.hasValue(content);
}

bool AbstractInterpretation::hasAbsValue(const SVFVar* var,
        const ICFGNode* node) const
{
    if (const auto* object = SVFUtil::dyn_cast<ObjVar>(var))
        return hasAbsValue(object, node);
    if (const auto* value = SVFUtil::dyn_cast<ValVar>(var))
        return hasAbsValue(value, node);
    return false;
}

bool AbstractInterpretation::numericalValueMayBeUninitialized(
    const ValVar* var, const ICFGNode* node) const
{
    if (!var || !adapter_.contains(*var))
        return true;
    const auto stateIterator = abstractTrace_.find(node);
    return stateIterator == abstractTrace_.end() ||
           stateIterator->second.numericalMayBeUninitialized(
               adapter_.variable(*var));
}

void AbstractInterpretation::updateValue(const ValVar* var,
        const SVF::Interval& interval,
        const SVF::AddressSet& addresses,
        const ICFGNode* node)
{
    if (adapter_.contains(*var))
        assignValue(ensureState(node), adapter_.variable(*var), interval,
                    addresses);
}

void AbstractInterpretation::addUninitializedNumericalAlternative(
    const ValVar* var, const ICFGNode* node)
{
    if (var && adapter_.contains(*var))
        ensureState(node).addUninitializedNumericalAlternative(
            adapter_.variable(*var));
}

void AbstractInterpretation::updateValue(const ObjVar* var,
        const SVF::Interval& interval,
        const SVF::AddressSet& addresses,
        const ICFGNode* node)
{
    State& denseState = ensureState(node);
    assignMemoryValue(denseState, memoryVariable(*var, denseState), interval,
                      addresses);
}

SVF::Interval AbstractInterpretation::getMemoryInterval(
    SVF::Location location, const ICFGNode* node)
{
    if (location.isNull())
        return SVF::Interval::bottom();
    return getInterval(&adapter_.object(location), node);
}

SVF::AddressSet AbstractInterpretation::getMemoryAddressSet(
    SVF::Location location, const ICFGNode* node)
{
    if (location.isNull())
        return SVF::AddressSet::bottom();
    return getAddressSet(&adapter_.object(location), node);
}

bool AbstractInterpretation::hasMemoryValue(SVF::Location location,
        const ICFGNode* node) const
{
    return !location.isNull() && hasAbsValue(&adapter_.object(location), node);
}

void AbstractInterpretation::updateMemoryValue(
    SVF::Location location, const SVF::Interval& interval,
    const SVF::AddressSet& addresses, const ICFGNode* node)
{
    if (!location.isNull())
    {
        if (objectRoutes_)
        {
            const auto content =
                adapter_.contentVariable(adapter_.object(location));
            objectRouteFallback_.insert(content);
            routedObjectVariables_.erase(content);
        }
        updateValue(&adapter_.object(location), interval, addresses, node);
    }
}

void AbstractInterpretation::markFreedMemory(SVF::Location location,
        const ICFGNode* node)
{
    if (!location.isNull())
        ensureState(node).lifetimes().release(location);
}

bool AbstractInterpretation::isFreedMemory(SVF::Location location,
        const ICFGNode* node) const
{
    if (abstractTrace_.count(node) == 0 || location.isNull())
        return false;
    return state(node).lifetimes().mayBeFreed(location);
}

void AbstractInterpretation::updateValue(const SVFVar* var,
        const SVF::Interval& interval,
        const SVF::AddressSet& addresses,
        const ICFGNode* node)
{
    if (const auto* object = SVFUtil::dyn_cast<ObjVar>(var))
        updateValue(object, interval, addresses, node);
    else if (const auto* scalar = SVFUtil::dyn_cast<ValVar>(var))
        updateValue(scalar, interval, addresses, node);
    else
    {
        assert(false && "unsupported SVF variable kind");
        std::abort();
    }
}


void AbstractInterpretation::loadValue(const ValVar* pointer,
                                       SVF::Interval& interval,
                                       SVF::AddressSet& addresses,
                                       bool& numericalMayBeUninitialized,
                                       const ICFGNode* node)
{
    numericalMayBeUninitialized = false;
    if (!adapter_.contains(*pointer))
    {
        interval = SVF::Interval::bottom();
        addresses = SVF::AddressSet::bottom();
        const SVF::AddressSet pointees = getAddressSet(pointer, node);
        if (pointees.hasUnknownObject())
        {
            if (unknownTargetTelemetryEnabled_)
                ++unknownTargetTelemetry_.loads;
            interval = SVF::Interval::top();
            addresses = SVF::AddressSet::top();
            return;
        }
        for (SVF::Location location : pointees)
        {
            interval.joinWith(getMemoryInterval(location, node));
            addresses.joinWith(getMemoryAddressSet(location, node));
        }
        return;
    }
    State& denseState = ensureState(node);
    materializeValue(denseState, pointer, node);
    const SVF::AddressSet pointees = getAddressSet(pointer, node);
    if (pointees.hasUnknownObject())
    {
        if (unknownTargetTelemetryEnabled_)
            ++unknownTargetTelemetry_.loads;
        interval = SVF::Interval::top();
        addresses = SVF::AddressSet::top();
        return;
    }

    interval = SVF::Interval::bottom();
    addresses = SVF::AddressSet::bottom();
    for (SVF::Location location : pointees.locations())
    {
        // getInterval/getAddressSet implement Original's freed-cell routing;
        // lifetime alone must not inject Top into value propagation.
        if (denseState.memoryLayout().contains(location))
        {
            const ObjVar* object = objectAt(location);
            if (!object)
                continue;
            const SVF::Variable content = memoryVariable(*object, denseState);
            numericalMayBeUninitialized |=
                denseState.numericalMayBeUninitialized(content);
            interval.joinWith(denseState.interval(content));
            addresses.joinWith(denseState.addressSet(content));
        }
    }
}

bool AbstractInterpretation::canStrongStore(
    const SVF::AddressSet& pointees, const ObjVar& object, const State& state)
{
    const BaseObjVar* base = svfir->getBaseObject(object.getId());
    const bool box = numericalDomain() == AENumericalDomain::Box;
    if (box)
    {
        const NodeID id = object.getId();
        const auto* pta = preAnalysis->getPointerAnalysis();
        return pointees.isSingleton() && base && base->isConstantByteSize() &&
               !adapter_.isRuntimeFieldSummary(object) && !svfir->isNullOrBlkObj(id) &&
               !pta->isHeapMemObj(id) && !base->isFieldInsensitive() &&
               !pta->isLocalVarInRecursiveFun(id) &&
               (!pta->isArrayMemObj(id) || svfir->isGepObjVar(id)) &&
               base->getType()->getTypeInfo()->getNumOfFlattenElements() <=
               base->getMaxFieldOffsetLimit() &&
               !state.lifetimes().mayBeFreed(adapter_.location(object));
    }
    const auto* field = SVFUtil::dyn_cast<GepObjVar>(&object);
    const bool preciseArray = base &&
        ((!field && object.getId() == base->getId()) ||
         (field && field->getConstantFieldIdx() >= 0 &&
          static_cast<u64_t>(field->getConstantFieldIdx()) <
              base->getType()->getTypeInfo()->getNumOfFlattenElements())) &&
        base->getType()->getTypeInfo()->getNumOfFlattenElements() <=
            base->getMaxFieldOffsetLimit();
    return pointees.isSingleton() && base && base->isConstantByteSize() &&
           !base->isHeap() && (!base->isArray() || preciseArray) &&
           !base->isBlackHoleObj() &&
           !base->isFieldInsensitive() &&
           !(base->isStack() && isRecursiveFun(base->getFunction())) &&
           !adapter_.isRuntimeFieldSummary(object) &&
           !state.lifetimes().mayBeFreed(adapter_.location(object));
}

bool AbstractInterpretation::canRefineMemory(
    const SVF::AddressSet& pointees, const ObjVar& object, const State& state)
{
    const BaseObjVar* base = svfir->getBaseObject(object.getId());
    const bool box = numericalDomain() == AENumericalDomain::Box;
    // One abstract allocation site can denote several concrete heap objects.
    // Strong updates require a non-repeating site and a unique, non-repeating
    // caller chain; a singleton points-to set alone is insufficient.
    if (base && base->isHeap())
    {
        if (!box)
            return false;
        const ICFGNode* site = base->getICFGNode();
        std::set<const FunObjVar*> visited;
        while (site)
        {
            const FunObjVar* function = site->getFun();
            if (!function || !visited.insert(function).second || isRecursiveFun(function))
                return false;
            const auto& wtos = preAnalysis->getFuncToWTO();
            const auto found = wtos.find(function);
            if (found == wtos.end() || !found->second->in_cycleDepth_table(site) ||
                    found->second->isHead(site) ||
                    found->second->cycleDepth(site).begin() != found->second->cycleDepth(site).end())
                return false;
            std::set<const CallICFGNode*> callers;
            for (const auto* edge : callGraph->getCallGraphNode(function)->getInEdges())
            {
                callers.insert(edge->getDirectCalls().begin(), edge->getDirectCalls().end());
                callers.insert(edge->getIndirectCalls().begin(), edge->getIndirectCalls().end());
            }
            if (callers.size() > 1)
                return false;
            if (callers.empty())
                break;
            site = *callers.begin();
        }
        if (!site)
            return false;
    }
    return pointees.isSingleton() && base &&
           (box || canStrongStore(pointees, object, state)) &&
           !base->isBlackHoleObj() &&
           !base->isFieldInsensitive() &&
           (box || !(base->isStack() && isRecursiveFun(base->getFunction()))) &&
           !adapter_.isRuntimeFieldSummary(object) &&
           !state.lifetimes().mayBeFreed(adapter_.location(object));
}

void AbstractInterpretation::storeValue(const ValVar* pointer,
                                        const SVF::Interval& interval,
                                        const SVF::AddressSet& addresses,
                                        const ICFGNode* node)
{
    State& denseState = ensureState(node);
    if (adapter_.contains(*pointer))
        materializeValue(denseState, pointer, node);
    const SVF::AddressSet pointees = getAddressSet(pointer, node);
    if (objectRoutes_ && pointees.hasUnknownObject())
        objectRouteFallbackAll_ = true;
    auto write = [&](SVF::Location location)
    {
        if (!denseState.memoryLayout().contains(location))
            return;
        const ObjVar* object = objectAt(location);
        if (!object)
            return;
        const SVF::Variable content = memoryVariable(*object, denseState);
        if (canStrongStore(pointees, *object, denseState))
        {
            assignMemoryValue(denseState, content, interval, addresses);
            return;
        }
        // This cell may not be written (or may summarize several concrete
        // cells). Retain the unchanged alternative, including initialization
        // and address facets. Sequential weak writes overapproximate the
        // choice of one target; they do not assert that all targets changed.
        if (numericalDomain() == AENumericalDomain::Box)
        {
            State written = topState();
            assignMemoryValue(written, content, interval, addresses);
            denseState.joinValueFrom(content, written, content);
        }
        else
        {
            State written(denseState);
            assignMemoryValue(written, content, interval, addresses);
            denseState.joinWith(written);
        }
    };

    if (pointees.hasUnknownObject())
    {
        if (unknownTargetTelemetryEnabled_)
            ++unknownTargetTelemetry_.stores;
        for (const auto& [location, content] :
                denseState.memoryLayout().cells())
        {
            if (unknownTargetTelemetryEnabled_)
                ++unknownTargetTelemetry_.storeCellsVisited;
            (void)content;
            write(location);
        }
    }
    else
    {
        for (SVF::Location location : pointees.locations())
            write(location);
    }
    if (objectRoutes_)
        recordSparseObjectStore(node, pointees);
}


std::optional<SVF::LinearExpression>
AbstractInterpretation::reconstructLinearExpression(
    const SVFVar* operand, State& denseState, const ICFGNode* node,
    std::vector<SVF::Variable>& relationVariables, unsigned depth,
    std::set<NodeID>& visiting)
{
    const auto* value = SVFUtil::dyn_cast<ValVar>(operand);
    if (!value)
    {
        const SVF::Interval constant = getInterval(operand, node);
        return constant.isSingleton()
               ? std::optional<SVF::LinearExpression>(
                   SVF::LinearExpression(constant.singletonValue()))
               : std::nullopt;
    }

    SVF::Interval literal;
    if (constantInterval(value, literal, numericalDomain()) && literal.isSingleton())
        return SVF::LinearExpression(literal.singletonValue());
    if (!adapter_.contains(*value))
        return std::nullopt;

    materializeValue(denseState, value, node);
    const SVF::Variable variable = adapter_.variable(*value);
    if (denseState.numericalMayBeUninitialized(variable))
        return std::nullopt;
    const SVF::Interval valueInterval = denseState.interval(variable);
    if (valueInterval.isSingleton())
        return SVF::LinearExpression(valueInterval.singletonValue());

    const auto retainValue = [&]() -> std::optional<SVF::LinearExpression>
    {
        relationVariables.push_back(variable);
        return SVF::LinearExpression(variable);
    };
    if (depth == 0 || value->getInEdges().size() != 1 ||
            !visiting.insert(value->getId()).second)
        return retainValue();

    const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(
                             *value->getInEdges().begin());
    const bool supported = binary &&
                           (binary->getOpcode() == BinaryOPStmt::Add ||
                            binary->getOpcode() == BinaryOPStmt::Sub ||
                            binary->getOpcode() == BinaryOPStmt::Mul);
    const auto* integerType = binary
                              ? SVFUtil::dyn_cast<SVFIntegerType>(
                                  binary->getRes()->getType())
                              : nullptr;
    if (!supported || !integerType)
    {
        visiting.erase(value->getId());
        return retainValue();
    }

    const auto intervalFor = [&](const SVFVar* input) -> SVF::Interval
    {
        if (const auto* inputValue = SVFUtil::dyn_cast<ValVar>(input))
        {
            SVF::Interval constant;
            if (constantInterval(inputValue, constant, numericalDomain()))
                return constant;
            if (adapter_.contains(*inputValue))
            {
                materializeValue(denseState, inputValue, node);
                const SVF::Variable inputVariable =
                adapter_.variable(*inputValue);
                if (denseState.numericalMayBeUninitialized(inputVariable))
                    return SVF::Interval::bottom();
                return denseState.interval(inputVariable);
            }
        }
        return getInterval(input, node);
    };

    const SVF::Interval lhsInterval = intervalFor(binary->getOpVar(0));
    const SVF::Interval rhsInterval = intervalFor(binary->getOpVar(1));
    SVF::Interval mathematical = SVF::Interval::top();
    if (!lhsInterval.isBottom() && !rhsInterval.isBottom())
    {
        if (binary->getOpcode() == BinaryOPStmt::Add)
            mathematical = SVF::add(lhsInterval, rhsInterval);
        else if (binary->getOpcode() == BinaryOPStmt::Sub)
            mathematical = SVF::subtract(lhsInterval, rhsInterval);
        else
            mathematical = SVF::multiply(lhsInterval, rhsInterval);
    }
    const SVF::Interval typeRange =
        utils->getRangeLimitFromType(binary->getRes()->getType());
    const bool noIntegerWrap = !mathematical.isBottom() &&
                               mathematical.isSubsetOf(typeRange);
    if (!noIntegerWrap)
    {
        visiting.erase(value->getId());
        return retainValue();
    }

    std::vector<SVF::Variable> expandedVariables;
    const auto lhs = reconstructLinearExpression(
                         binary->getOpVar(0), denseState, node,
                         expandedVariables, depth - 1, visiting);
    const auto rhs = reconstructLinearExpression(
                         binary->getOpVar(1), denseState, node,
                         expandedVariables, depth - 1, visiting);
    visiting.erase(value->getId());
    if (!lhs || !rhs)
        return retainValue();

    std::optional<SVF::LinearExpression> result;
    if (binary->getOpcode() == BinaryOPStmt::Add)
        result = *lhs + *rhs;
    else if (binary->getOpcode() == BinaryOPStmt::Sub)
        result = *lhs - *rhs;
    else if (lhsInterval.isSingleton())
        result = lhsInterval.singletonValue() * *rhs;
    else if (rhsInterval.isSingleton())
        result = rhsInterval.singletonValue() * *lhs;

    // Bound expansion even for Polyhedra. Octagon queries normally stop at
    // two variables, while this small slack lets constants and copies fold.
    if (!result || result->terms().size() > 8)
        return retainValue();
    relationVariables.insert(relationVariables.end(),
                             expandedVariables.begin(),
                             expandedVariables.end());
    return result;
}

void AbstractInterpretation::assumeBranch(const IntraCFGEdge* edge,
        State& denseState)
{
    const SVFVar* condition = edge->getCondition();
    if (!condition)
        return;
    if (!intervalPreanalysis_ && numericalDomain() == AENumericalDomain::Box && edge->isSwitchEdge())
    {
        if (!isSwitchBranchEdgeFeasible(edge, getInterval(condition, edge->getSrcNode())))
            denseState = bottomState();
        return;
    }
    if (edge->isSwitchEdge())
    {
        // A default destination can also contain explicit labels. Its union
        // cannot be approximated by the hull of those labels alone.
        const auto& cases = edge->getSwitchCases();
        // Narrow integer values may retain a zero-extended representation in
        // the abstract state. Do not intersect them with signed IR labels.
        if (edge->getSwitchWidth() < 32 || edge->getSwitchWidth() > 64)
            return;
        if (edge->includesSwitchDefault())
        {
            const auto* variable = SVFUtil::dyn_cast<ValVar>(condition);
            if (!variable || !adapter_.contains(*variable))
                return;
            materializeValue(denseState, variable, edge->getSrcNode());
            const auto symbol = adapter_.variable(*variable);
            SVF::Interval value = denseState.numerical().bound(symbol);
            std::set<SVF::Rational> excluded;
            for (const auto* outgoing : edge->getSrcNode()->getOutEdges())
                if (const auto* branch = SVFUtil::dyn_cast<IntraCFGEdge>(outgoing))
                    if (branch->isSwitchEdge() && branch != edge)
                        for (s64_t label : branch->getSwitchCases())
                            excluded.insert(SVF::Rational(label));
            if (!value.isBottom())
            {
                auto lower = value.lower(), upper = value.upper();
                while (lower.isFinite() && excluded.count(lower.value()))
                    lower = SVF::Bound::finite(lower.value() + SVF::Rational(1));
                while (upper.isFinite() && excluded.count(upper.value()))
                    upper = SVF::Bound::finite(upper.value() - SVF::Rational(1));
                const SVF::LinearExpression expression(symbol);
                if (lower.isFinite())
                    denseState.assume(SVF::greaterEqual(expression,
                                                        SVF::LinearExpression(lower.value())));
                if (upper.isFinite())
                    denseState.assume(SVF::lessEqual(expression,
                                                     SVF::LinearExpression(upper.value())));
            }
            return;
        }
        if (cases.empty())
            return;
        const auto* value = SVFUtil::dyn_cast<ValVar>(condition);
        if (!value || !adapter_.contains(*value)) return;
        const auto limits = std::minmax_element(cases.begin(), cases.end());
        materializeValue(denseState, value, edge->getSrcNode());
        const SVF::LinearExpression expression(adapter_.variable(*value));
        denseState.assume(SVF::LinearConstraint(expression - SVF::LinearExpression(SVF::Rational(*limits.first)),
                                                SVF::ConstraintKind::GreaterEqual));
        denseState.assume(SVF::LinearConstraint(expression - SVF::LinearExpression(SVF::Rational(*limits.second)),
                                                SVF::ConstraintKind::LessEqual));
        return;
    }
    assumeCondition(condition, edge->getSuccessorCondValue() != 0,
                    denseState, edge->getSrcNode());
}

AbstractInterpretation::ConditionAlternatives
AbstractInterpretation::conditionAlternatives(const SVFVar* condition, bool taken) const
{
    const auto* variable = SVFUtil::dyn_cast<ValVar>(condition);
    const SVFStmt* def = variable && variable->getInEdges().size() == 1
                         ? *variable->getInEdges().begin() : nullptr;
    const auto* type = SVFUtil::dyn_cast<SVFIntegerType>(condition->getType());
    if ((!intervalPreanalysis_ && numericalDomain() == AENumericalDomain::Box) ||
            !type || !type->isBoolean() || !def)
        return {};
    if (const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(def))
        if (binary->getOpcode() == BinaryOPStmt::And || binary->getOpcode() == BinaryOPStmt::Or)
        {
            const bool conjunction = binary->getOpcode() == BinaryOPStmt::And;
            if (taken == conjunction)
                return {{{binary->getOpVar(0), taken}, {binary->getOpVar(1), taken}}};
            return {{{binary->getOpVar(0), taken}}, {{binary->getOpVar(1), taken}}};
        }
    if (const auto* select = SVFUtil::dyn_cast<SelectStmt>(def))
        return {{{select->getCondition(), true}, {select->getTrueValue(), taken}},
                {{select->getCondition(), false}, {select->getFalseValue(), taken}}};
    if (const auto* phi = SVFUtil::dyn_cast<PhiStmt>(def))
    {
        const SVFBasicBlock* block = phi->getICFGNode()->getBB();
        std::set<const SVFBasicBlock*> reachable;
        std::vector<const SVFBasicBlock*> pending;
        if (block)
            pending.assign(block->succBBs.begin(), block->succBBs.end());
        while (!pending.empty())
        {
            const auto* next = pending.back();
            pending.pop_back();
            if (reachable.insert(next).second)
                for (const auto* successor : next->succBBs)
                {
                    const auto* function = phi->getICFGNode()->getFun();
                    const bool backEdge = function->isLoopHeader(successor) &&
                                          function->loopContainsBB(function->getLoopInfo(successor), next);
                    if (!backEdge)
                        pending.push_back(successor);
                }
        }
        // Loop-carried and function-return phis keep their existing fallback.
        bool acyclic = block && !phi->isFunctionRetPhi();
        for (u32_t i = 0; i < phi->getOpVarNum(); ++i)
            acyclic &= !reachable.count(phi->getOpICFGNode(i)->getBB());
        if (!acyclic)
            return {};
        ConditionAlternatives alternatives;
        for (u32_t i = 0; i < phi->getOpVarNum(); ++i)
        {
            std::vector<ConditionRefinement> alternative{{phi->getOpVar(i), taken}};
            const ICFGNode* cursor = phi->getOpICFGNode(i);
            for (const ICFGEdge* edge : cursor->getOutEdges())
                if (edge->getDstNode() == block->getICFGNodeList().front())
                    if (const auto* incoming = SVFUtil::dyn_cast<IntraCFGEdge>(edge))
                        if (incoming->getCondition() && !incoming->isSwitchEdge())
                        {
                            alternative.push_back({incoming->getCondition(),
                                                   incoming->getSuccessorCondValue() != 0});
                            cursor = nullptr;
                            break;
                        }
            std::set<const ICFGNode*> seen;
            while (cursor && seen.insert(cursor).second)
            {
                bool crossesPhi = false;
                for (const SVFStmt* stmt : cursor->getSVFStmts())
                    crossesPhi |= SVFUtil::isa<PhiStmt>(stmt);
                if (crossesPhi || cursor->getInEdges().size() != 1)
                    break;
                const auto* incoming = SVFUtil::dyn_cast<IntraCFGEdge>(*cursor->getInEdges().begin());
                if (!incoming || incoming->isSwitchEdge())
                    break;
                if (incoming->getCondition())
                {
                    alternative.push_back({incoming->getCondition(),
                                           incoming->getSuccessorCondValue() != 0});
                    break;
                }
                cursor = incoming->getSrcNode();
            }
            alternatives.push_back(std::move(alternative));
        }
        return alternatives;
    }
    return {};
}

void AbstractInterpretation::collectComparisonWrites(
    const SVFVar* operand, std::set<SVF::Variable>& writes, unsigned depth) const
{
    const auto* value = SVFUtil::dyn_cast<ValVar>(operand);
    SVF::Interval literal;
    if (!value || constantInterval(value, literal, numericalDomain()) || !adapter_.contains(*value))
        return;
    // Runtime interval/overflow guards can retain this coordinate instead of
    // expanding it. Include both possibilities in the static footprint.
    writes.insert(adapter_.variable(*value));
    if (depth == 0 || value->getInEdges().size() != 1)
        return;
    const auto* binary = SVFUtil::dyn_cast<BinaryOPStmt>(*value->getInEdges().begin());
    if (!binary || !SVFUtil::isa<SVFIntegerType>(binary->getRes()->getType()) ||
            (binary->getOpcode() != BinaryOPStmt::Add &&
             binary->getOpcode() != BinaryOPStmt::Sub && binary->getOpcode() != BinaryOPStmt::Mul))
        return;
    collectComparisonWrites(binary->getOpVar(0), writes, depth - 1);
    collectComparisonWrites(binary->getOpVar(1), writes, depth - 1);
}

void AbstractInterpretation::collectConditionWrites(
    const SVFVar* condition, bool taken, const ICFGNode* source,
    std::set<SVF::Variable>& writes, unsigned depth) const
{
    if (depth >= 16)
        return;
    const SVFVar* normalized = !intervalPreanalysis_ && numericalDomain() == AENumericalDomain::Box
                               ? condition : SVFIRAdapter::booleanCondition(condition, taken);
    if (SVFUtil::isa<ConstIntValVar>(normalized))
        return;
    const auto alternatives = conditionAlternatives(normalized, taken);
    if (!alternatives.empty())
    {
        for (const auto& branch : alternatives)
            for (const auto& refinement : branch)
                collectConditionWrites(refinement.condition, refinement.taken, source, writes, depth + 1);
        return;
    }
    if (normalized->getInEdges().empty())
        return;
    const auto* comparison = SVFUtil::dyn_cast<CmpStmt>(*normalized->getInEdges().begin());
    if (!comparison)
    {
        const auto* value = SVFUtil::dyn_cast<ValVar>(normalized);
        if (value && adapter_.contains(*value))
            writes.insert(adapter_.variable(*value));
        return;
    }
    if ((intervalPreanalysis_ || numericalDomain() != AENumericalDomain::Box) &&
            isSignedNumericComparison(comparison))
        for (const auto* operand : comparison->getOpndVars())
            collectComparisonWrites(operand, writes, kComparisonUnfoldDepth);
}

void AbstractInterpretation::assumeCondition(const SVFVar* condition, bool taken,
        State& denseState, const ICFGNode* source, unsigned depth)
{
    const bool originalTaken = taken;
    const SVFVar* normalized = !intervalPreanalysis_ && numericalDomain() == AENumericalDomain::Box
                               ? condition : SVFIRAdapter::booleanCondition(condition, taken);
    if (denseState.isBottom() || depth >= 16)
        return;
    const SVF::Interval known = getInterval(condition, source);
    if (known.isSingleton() && known.isZero() == originalTaken)
    {
        denseState = bottomState();
        return;
    }
    if (const auto* constant = SVFUtil::dyn_cast<ConstIntValVar>(normalized))
    {
        if ((constant->getSExtValue() != 0) != taken)
            denseState = bottomState();
        return;
    }
    const auto alternatives = conditionAlternatives(normalized, taken);
    if (!alternatives.empty())
    {
        if (alternatives.size() == 1)
            for (const auto& refinement : alternatives.front())
                assumeCondition(refinement.condition, refinement.taken, denseState, source, depth + 1);
        else
        {
            State joined = bottomState();
            for (const auto& branch : alternatives)
            {
                State alternative = denseState;
                for (const auto& refinement : branch)
                    assumeCondition(refinement.condition, refinement.taken, alternative, source, depth + 1);
                joined.joinWith(alternative);
            }
            denseState = std::move(joined);
        }
        return;
    }
    if (normalized->getInEdges().empty())
        return;
    const auto* comparison =
        SVFUtil::dyn_cast<CmpStmt>(*normalized->getInEdges().begin());
    if (!comparison)
    {
        const auto* value = SVFUtil::dyn_cast<ValVar>(normalized);
        if (!value || !adapter_.contains(*value))
            return;
        materializeValue(denseState, value, source);
        denseState.assume(SVF::equal(
                              SVF::LinearExpression(adapter_.variable(*value)),
                              SVF::LinearExpression(SVF::Rational(taken ? 1 : 0))));
        return;
    }

    // Preserve the established Box baseline. Relational domains additionally
    // consume the source-level comparison itself, as in a conventional
    // numerical abstract interpreter, instead of refining only its Boolean
    // SSA result. IEEE and unsigned comparisons need dedicated bit-vector/
    // NaN semantics and therefore keep the conservative legacy behavior.
    if ((intervalPreanalysis_ || numericalDomain() != AENumericalDomain::Box) &&
            !comparison->getOpVar(0)->isPointer())
    {
        const s32_t predicate = comparison->getPredicate();
        const bool supported = isSignedNumericComparison(comparison);
        if (supported)
        {
            std::vector<SVF::Variable> relationVariables;
            std::set<NodeID> visiting;
            const auto lhs = reconstructLinearExpression(
                                 comparison->getOpVar(0), denseState, source,
                                 relationVariables, kComparisonUnfoldDepth, visiting);
            const auto rhs = reconstructLinearExpression(
                                 comparison->getOpVar(1), denseState, source,
                                 relationVariables, kComparisonUnfoldDepth, visiting);
            if (lhs && rhs)
            {
                materializeRelations(denseState, relationVariables, source);
                SVF::ConstraintKind kind = SVF::ConstraintKind::Equal;
                switch (predicate)
                {
                case CmpStmt::ICMP_EQ:
                    kind = taken ? SVF::ConstraintKind::Equal
                           : SVF::ConstraintKind::NotEqual;
                    break;
                case CmpStmt::ICMP_NE:
                    kind = taken ? SVF::ConstraintKind::NotEqual
                           : SVF::ConstraintKind::Equal;
                    break;
                case CmpStmt::ICMP_SLT:
                    kind = taken ? SVF::ConstraintKind::LessThan
                           : SVF::ConstraintKind::GreaterEqual;
                    break;
                case CmpStmt::ICMP_SLE:
                    kind = taken ? SVF::ConstraintKind::LessEqual
                           : SVF::ConstraintKind::GreaterThan;
                    break;
                case CmpStmt::ICMP_SGT:
                    kind = taken ? SVF::ConstraintKind::GreaterThan
                           : SVF::ConstraintKind::LessEqual;
                    break;
                case CmpStmt::ICMP_SGE:
                    kind = taken ? SVF::ConstraintKind::GreaterEqual
                           : SVF::ConstraintKind::LessThan;
                    break;
                default:
                    break;
                }
                if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
                    SVFUtil::outs()
                            << "AE_BRANCH_BEFORE source="
                            << source->getId()
                            << " predicate=" << predicate
                            << " taken=" << taken << " state="
                            << denseState.numerical().toString() << '\n';
                if (kind == SVF::ConstraintKind::NotEqual)
                {
                    State positive = denseState;
                    denseState.assume(SVF::LinearConstraint(*lhs - *rhs,
                                                            SVF::ConstraintKind::LessThan));
                    positive.assume(SVF::LinearConstraint(*lhs - *rhs,
                                                          SVF::ConstraintKind::GreaterThan));
                    denseState.joinWith(positive);
                }
                else
                    denseState.assume(SVF::LinearConstraint(*lhs - *rhs, kind));
                if (std::getenv("SVF_AE_TRACE_PHI_RELATIONS"))
                    SVFUtil::outs()
                            << "AE_BRANCH_AFTER source="
                            << source->getId()
                            << " predicate=" << predicate
                            << " taken=" << taken << " state="
                            << denseState.numerical().toString() << '\n';
            }
        }
    }

    // Original checks only the Boolean result for feasibility. It neither
    // refines the comparison's SSA operands nor stores a branch-local Boolean
    // fact. Memory refinement is handled by collectBranchRefinement instead.
    SVF::Interval result = getInterval(condition, source);
    if (result.isBottom())
        return;
    result.meetWith(SVF::Interval::singleton(
                        SVF::Rational(originalTaken ? 1 : 0)));
    if (result.isBottom())
        denseState = bottomState();
}


bool AbstractInterpretation::isBranchEdgeFeasibleAt(
    const IntraCFGEdge* edge, const ICFGNode* predecessor)
{
    if (numericalDomain() == AENumericalDomain::Box &&
            !edge->isSwitchEdge())
    {
        const SVFVar* condition = edge->getCondition();
        const auto* comparison = condition && !condition->getInEdges().empty()
                                 ? SVFUtil::dyn_cast<CmpStmt>(
                                     *condition->getInEdges().begin())
                                 : nullptr;
        if (comparison)
        {
            if (state(predecessor).isBottom())
                return false;
            SVF::Interval result = getInterval(comparison->getRes(),
                                               edge->getSrcNode());
            if (result.isBottom())
                return true;
            result.meetWith(SVF::Interval::singleton(
                                SVF::Rational(edge->getSuccessorCondValue())));
            return !result.isBottom();
        }
    }
    State candidate = state(predecessor);
    assumeBranch(edge, candidate);
    return !candidate.isBottom();
}

} // namespace SVF
