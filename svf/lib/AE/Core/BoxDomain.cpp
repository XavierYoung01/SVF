//===- BoxDomain.cpp -- Interval box domain ---------------------*- C++ -*-===//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
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
// Contributors: Jiawei Wang, Xiao Cheng, Jiawei Yang
//
//===----------------------------------------------------------------------===//

#include "AE/Core/BoxDomain.h"

#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <map>
#include <sstream>

namespace SVF
{

namespace
{

Bound minLower(const Bound& lhs, const Bound& rhs)
{
    return Bound::compareLower(lhs, rhs) <= 0 ? lhs : rhs;
}

Bound maxLower(const Bound& lhs, const Bound& rhs)
{
    return Bound::compareLower(lhs, rhs) >= 0 ? lhs : rhs;
}

Bound scaleBound(const Bound& bound, const Rational& coefficient)
{
    if (coefficient.isZero())
        return Bound::finite(Rational());
    if (bound.isMinusInfinity())
        return coefficient.sign() > 0 ? Bound::minusInfinity()
               : Bound::plusInfinity();
    if (bound.isPlusInfinity())
        return coefficient.sign() > 0 ? Bound::plusInfinity()
               : Bound::minusInfinity();
    return Bound::finite(bound.value() * coefficient, bound.isStrict());
}

Interval scaleInterval(const Interval& interval, const Rational& coefficient)
{
    if (coefficient.isZero())
        return Interval::singleton(Rational());
    if (coefficient.sign() > 0)
        return Interval(scaleBound(interval.lower(), coefficient),
                        scaleBound(interval.upper(), coefficient));
    return Interval(scaleBound(interval.upper(), coefficient),
                    scaleBound(interval.lower(), coefficient));
}

Interval addBoxIntervals(const Interval& lhs, const Interval& rhs)
{
    return Interval(Bound::add(lhs.lower(), rhs.lower()),
                    Bound::add(lhs.upper(), rhs.upper()));
}

Interval joinIntervals(const Interval& lhs, const Interval& rhs)
{
    return Interval(minLower(lhs.lower(), rhs.lower()),
                    Bound::max(lhs.upper(), rhs.upper()));
}

Interval meetIntervals(const Interval& lhs, const Interval& rhs)
{
    return Interval(maxLower(lhs.lower(), rhs.lower()),
                    Bound::min(lhs.upper(), rhs.upper()));
}

bool intervalIncluded(const Interval& lhs, const Interval& rhs)
{
    if (lhs.isBottom())
        return true;
    if (rhs.isBottom())
        return false;
    return Bound::compareLower(lhs.lower(), rhs.lower()) >= 0 &&
           Bound::compare(lhs.upper(), rhs.upper()) <= 0;
}

Interval evaluate(const BoxDomain& state, const LinearExpression& expression,
                  std::optional<Variable> excluded = std::nullopt)
{
    Interval result = Interval::singleton(expression.constant());
    for (const auto& [variable, coefficient] : expression.terms())
    {
        if (excluded && variable == *excluded)
            continue;
        result = addBoxIntervals(
                     result, scaleInterval(state.bound(variable), coefficient));
    }
    return result;
}

Bound integerLower(Bound bound)
{
    if (!bound.isFinite())
        return bound;
    const Rational value = bound.isStrict()
                           ? bound.value().floor() + Rational(1)
                           : bound.value().ceil();
    return Bound::finite(value);
}

Bound integerUpper(Bound bound)
{
    if (!bound.isFinite())
        return bound;
    const Rational value = bound.isStrict() ? bound.value().ceil() - Rational(1)
                           : bound.value().floor();
    return Bound::finite(value);
}

LinearConstraint normalizedLessEqual(const LinearConstraint& constraint,
                                     bool& strict)
{
    strict = constraint.kind() == ConstraintKind::LessThan ||
             constraint.kind() == ConstraintKind::GreaterThan;
    if (constraint.kind() == ConstraintKind::GreaterEqual ||
            constraint.kind() == ConstraintKind::GreaterThan)
        return LinearConstraint(-constraint.expression(),
                                strict ? ConstraintKind::LessThan
                                : ConstraintKind::LessEqual);
    return LinearConstraint(constraint.expression(),
                            strict ? ConstraintKind::LessThan
                            : ConstraintKind::LessEqual);
}

} // namespace

BoxDomain::BoxDomain(BoxSemanticConfig config, bool bottom)
    : config_(std::move(config)), values_(config_.storage.values),
      objectContents_(config_.storage.objectContents), bottom_(bottom)
{
}

BoxDomain::BoxDomain(const BoxDomain& other) = default;

BoxDomain BoxDomain::top(const BoxSemanticConfig& config)
{
    BoxDomain result(config, false);
    return result;
}

BoxDomain BoxDomain::bottom(const BoxSemanticConfig& config)
{
    BoxDomain result(config, true);
    return result;
}

BoxDomain BoxDomain::fromConstraints(const LinearConstraintSet& constraints,
                                     const BoxSemanticConfig& config)
{
    BoxDomain result = top(config);
    result.assumeAll(constraints);
    return result;
}

std::unique_ptr<AbstractDomain> BoxDomain::clone() const
{
    return std::make_unique<BoxDomain>(*this);
}

void BoxDomain::assignInterval(Variable target, const Interval& value)
{
    if (bottom_)
        return;
    recordOperation(value.isTop() ? OperationKind::Forget : OperationKind::Assumption,
                    ApproximationKind::Exact, true);
    if (boundAt(target) != value)
        setBound(target, value);
}

void BoxDomain::assign(Variable target, const LinearExpression& expression)
{
    recordOperation(OperationKind::Assignment, ApproximationKind::Exact, true);
    if (bottom_)
        return;
    setBound(target, evaluate(*this, expression));
}

void BoxDomain::assign(Variable target, const TreeExpression& expression)
{
    const std::optional<LinearExpression> linear = expression.asLinear();
    if (linear)
    {
        assign(target, *linear);
        return;
    }
    const Interval value = evaluateTreeExpression(expression);
    if (!bottom_)
        setBound(target, value);
    report(OperationKind::Assignment, ApproximationKind::SoundOverApproximation,
           "nonlinear or finite IEEE assignment was interval-linearized",
           false);
}

void BoxDomain::assignParallel(const LinearAssignmentList& assignments)
{
    std::set<Variable> targets;
    for (const LinearAssignment& assignment : assignments)
    {
        if (!targets.insert(assignment.target).second)
        {
            assert(false && "parallel assignment contains a duplicate target");
            std::abort();
        }
    }
    recordOperation(OperationKind::Assignment, ApproximationKind::Exact, true);
    if (bottom_)
        return;

    std::vector<std::pair<Variable, Interval>> updates;
    updates.reserve(assignments.size());
    for (const LinearAssignment& assignment : assignments)
        updates.emplace_back(assignment.target,
                             evaluate(*this, assignment.expression));
    for (auto& [variable, value] : updates)
        setBound(variable, std::move(value));
}

void BoxDomain::substitute(Variable target, const LinearExpression& expression)
{
    substituteParallel({{target, expression}});
}

void BoxDomain::substituteParallel(const LinearAssignmentList& assignments)
{
    std::map<Variable, LinearExpression> replacements;
    for (const LinearAssignment& assignment : assignments)
    {
        if (!replacements.emplace(assignment.target, assignment.expression)
                .second)
        {
            assert(false && "parallel substitution contains a duplicate target");
            std::abort();
        }
    }
    recordOperation(OperationKind::Substitution, ApproximationKind::Exact,
                    true);
    if (assignments.empty() || bottom_)
        return;

    LinearConstraintSet preimage;
    for (const LinearConstraint& constraint : toConstraints())
        preimage.emplace_back(constraint.expression().substituted(replacements),
                              constraint.kind());
    *this = fromConstraints(preimage, config_);
}

void BoxDomain::assume(const LinearConstraint& constraint)
{
    recordOperation(OperationKind::Assumption, ApproximationKind::Exact, true);
    if (bottom_)
        return;
    if (constraint.kind() == ConstraintKind::NotEqual)
    {
        const Interval value = evaluate(*this, constraint.expression());
        if (!value.lower().isFinite() || !value.upper().isFinite() ||
                value.lower().value() != Rational() ||
                value.upper().value() != Rational() || value.lower().isStrict() ||
                value.upper().isStrict())
            return;
        makeBottom();
        return;
    }

    if (constraint.kind() == ConstraintKind::Equal)
    {
        assume(LinearConstraint(constraint.expression(),
                                ConstraintKind::LessEqual));
        assume(LinearConstraint(-constraint.expression(),
                                ConstraintKind::LessEqual));
        return;
    }

    bool strict = false;
    const LinearConstraint normalized = normalizedLessEqual(constraint, strict);
    const LinearExpression& expression = normalized.expression();

    // Repeating interval propagation lets bounds inferred for one variable
    // tighten another without introducing an unbounded worklist.
    for (std::size_t pass = 0; pass <= expression.terms().size(); ++pass)
    {
        bool changed = false;
        for (const auto& [variable, coefficient] : expression.terms())
        {
            if (coefficient.isZero())
                continue;
            const Interval rest = evaluate(*this, expression, variable);
            if (!rest.lower().isFinite())
                continue;

            const Rational rhs = -rest.lower().value() / coefficient;
            const bool resultStrict = strict || rest.lower().isStrict();
            Interval next = boundAt(variable);
            if (coefficient.sign() > 0)
            {
                next = meetIntervals(
                           next, Interval(Bound::minusInfinity(),
                                          Bound::finite(rhs, resultStrict)));
            }
            else
            {
                next = meetIntervals(next,
                                     Interval(Bound::finite(rhs, resultStrict),
                                              Bound::plusInfinity()));
            }
            const Interval previous = boundAt(variable);
            setBound(variable, next);
            if (bottom_)
                return;
            changed = changed ||
                      !intervalIncluded(previous, boundAt(variable)) ||
                      !intervalIncluded(boundAt(variable), previous);
        }
        if (!changed)
            break;
    }

    const Interval value = evaluate(*this, expression);
    if (value.lower().isFinite())
    {
        const int sign = value.lower().value().sign();
        if (sign > 0 || (sign == 0 && (strict || value.lower().isStrict())))
            makeBottom();
    }
}

void BoxDomain::assume(const TreeConstraint& constraint)
{
    const std::optional<LinearExpression> linear =
        constraint.expression().asLinear();
    if (linear)
    {
        assume(LinearConstraint(*linear, constraint.kind()));
        return;
    }
    const LinearConstraintSet consequences =
        treeConstraintConsequences(constraint);
    assumeAll(consequences);
    report(OperationKind::Assumption, ApproximationKind::SoundOverApproximation,
           consequences.empty()
           ? "nonlinear or finite IEEE guard had no affine consequence"
           : "nonlinear guard was reduced to sound affine consequences",
           false);
}

void BoxDomain::assumeAll(const LinearConstraintSet& constraints)
{
    if (constraints.empty())
    {
        NumericalDomain::assumeAll(constraints);
        return;
    }
    const bool allUnary = std::all_of(
                              constraints.begin(), constraints.end(),
                              [](const LinearConstraint& constraint)
    {
        return constraint.expression().terms().size() <= 1;
    });
    if (!allUnary)
    {
        NumericalDomain::assumeAll(constraints);
        return;
    }

    for (const LinearConstraint& constraint : constraints)
        assume(constraint);
}

void BoxDomain::forget(Variable variable)
{
    if (!bottom_)
        eraseBound(variable);
    recordOperation(OperationKind::Forget, ApproximationKind::Exact, true);
}

void BoxDomain::project(const std::vector<Variable>& retained)
{
    const std::set<Variable> keep(retained.begin(), retained.end());
    for (Variable variable : constrainedVariables())
        if (keep.count(variable) == 0)
            forget(variable);
}

std::vector<Variable> BoxDomain::constrainedVariables() const
{
    std::vector<Variable> variables;
    if (bottom_)
        return variables;
    return boundedVariables();
}

std::vector<Variable> BoxDomain::constrainedVariablesBefore(
    Variable upperBound) const
{
    if (bottom_)
        return {};
    return boundedVariablesBefore(upperBound);
}

void BoxDomain::expand(Variable source, const std::vector<Variable>& copies)
{
    std::set<Variable> seen;
    for (Variable copy : copies)
    {
        if (copy == source || !seen.insert(copy).second)
        {
            assert(false && "expanded variables must be distinct from the source");
            std::abort();
        }
        if (copy.type() != source.type())
        {
            assert(false && "expanded variables must have the source numeric type");
            std::abort();
        }
    }
    if (copies.empty())
    {
        recordOperation(OperationKind::Expand, ApproximationKind::Exact, true);
        return;
    }
    const Interval sourceValue = bound(source);
    for (Variable copy : copies)
        if (!bottom_)
            setBound(copy, sourceValue);
    recordOperation(OperationKind::Expand, ApproximationKind::Exact, true);
}

void BoxDomain::fold(Variable target, const std::vector<Variable>& folded)
{
    std::set<Variable> seen;
    std::vector<Variable> sources{target};
    for (Variable variable : folded)
    {
        if (variable == target || !seen.insert(variable).second)
        {
            assert(false && "folded variables must be distinct non-target variables");
            std::abort();
        }
        if (variable.type() != target.type())
        {
            assert(false && "folded variables must have the target numeric type");
            std::abort();
        }
        sources.push_back(variable);
    }
    if (folded.empty())
    {
        recordOperation(OperationKind::Fold, ApproximationKind::Exact, true);
        return;
    }

    BoxDomain result = bottom(config_);
    for (Variable source : sources)
    {
        BoxDomain branch = *this;
        if (source != target)
            branch.setBound(target, bound(source));
        result = result.join(branch);
    }
    for (Variable variable : folded)
        result.forget(variable);
    *this = std::move(result);
    recordOperation(OperationKind::Fold, ApproximationKind::Exact, true);
}

CheckResult BoxDomain::entails(const LinearConstraint& constraint) const
{
    if (bottom_)
        return CheckResult::True;
    const Interval value = evaluate(*this, constraint.expression());
    const auto upperAtMostZero = [&]()
    {
        if (!value.upper().isFinite())
            return false;
        return value.upper().value().sign() <= 0;
    };
    const auto upperBelowZero = [&]()
    {
        return value.upper().isFinite() &&
               (value.upper().value().sign() < 0 ||
                (value.upper().value().isZero() && value.upper().isStrict()));
    };
    const auto lowerAtLeastZero = [&]()
    {
        return value.lower().isFinite() && value.lower().value().sign() >= 0;
    };
    const auto lowerAboveZero = [&]()
    {
        return value.lower().isFinite() &&
               (value.lower().value().sign() > 0 ||
                (value.lower().value().isZero() && value.lower().isStrict()));
    };

    switch (constraint.kind())
    {
    case ConstraintKind::LessEqual:
        return upperAtMostZero() ? CheckResult::True : CheckResult::Unknown;
    case ConstraintKind::LessThan:
        return upperBelowZero() ? CheckResult::True : CheckResult::Unknown;
    case ConstraintKind::GreaterEqual:
        return lowerAtLeastZero() ? CheckResult::True : CheckResult::Unknown;
    case ConstraintKind::GreaterThan:
        return lowerAboveZero() ? CheckResult::True : CheckResult::Unknown;
    case ConstraintKind::Equal:
        return upperAtMostZero() && lowerAtLeastZero() ? CheckResult::True
               : CheckResult::Unknown;
    case ConstraintKind::NotEqual:
        return upperBelowZero() || lowerAboveZero() ? CheckResult::True
               : CheckResult::Unknown;
    }
    return CheckResult::Unknown;
}

Interval BoxDomain::bound(Variable variable) const
{
    if (bottom_)
        return Interval(Bound::plusInfinity(), Bound::minusInfinity());
    return boundAt(variable);
}

Interval BoxDomain::bound(const LinearExpression& expression) const
{
    if (bottom_)
        return Interval(Bound::plusInfinity(), Bound::minusInfinity());
    return evaluate(*this, expression);
}

LinearConstraintSet BoxDomain::toConstraints() const
{
    LinearConstraintSet result;
    if (bottom_)
    {
        result.emplace_back(LinearExpression(Rational(1)),
                            ConstraintKind::LessEqual);
        return result;
    }
    for (Variable variable : boundedVariables())
    {
        const Interval& interval = boundAt(variable);
        if (interval.lower().isFinite())
        {
            result.emplace_back(LinearExpression(variable) -
                                LinearExpression(interval.lower().value()),
                                interval.lower().isStrict()
                                ? ConstraintKind::GreaterThan
                                : ConstraintKind::GreaterEqual);
        }
        if (interval.upper().isFinite())
        {
            result.emplace_back(LinearExpression(variable) -
                                LinearExpression(interval.upper().value()),
                                interval.upper().isStrict()
                                ? ConstraintKind::LessThan
                                : ConstraintKind::LessEqual);
        }
    }
    return result;
}

void BoxDomain::close()
{
    recordOperation(OperationKind::TopologicalClosure, ApproximationKind::Exact,
                    true, "topological closure");
    if (bottom_)
        return;
    for (Variable variable : boundedVariables())
    {
        const Interval& interval = boundAt(variable);
        const Bound lower = interval.lower().isFinite()
                            ? Bound::finite(interval.lower().value())
                            : interval.lower();
        const Bound upper = interval.upper().isFinite()
                            ? Bound::finite(interval.upper().value())
                            : interval.upper();
        setBound(variable, Interval(lower, upper));
    }
}

void BoxDomain::canonicalize()
{
    for (Variable variable : boundedVariables())
        canonicalize(variable);
    recordOperation(OperationKind::Canonicalization, ApproximationKind::Exact,
                    true, "canonicalization");
}

BoxDomain BoxDomain::join(const BoxDomain& other) const
{
    BoxDomain result(*this);
    result.joinDomain(other);
    result.recordOperation(OperationKind::Join, ApproximationKind::Exact, true);
    return result;
}

BoxDomain BoxDomain::meet(const BoxDomain& other) const
{
    BoxDomain result(*this);
    result.meetDomain(other);
    result.recordOperation(OperationKind::Meet, ApproximationKind::Exact, true);
    return result;
}

BoxDomain BoxDomain::widen(const BoxDomain& next) const
{
    return widen(next, WideningPolicy{});
}

BoxDomain BoxDomain::widen(const BoxDomain& next,
                           const WideningPolicy& policy) const
{
    requireBox(next);
    if (bottom_)
    {
        BoxDomain result(*this);
        result.joinDomain(next);
        result.recordOperation(OperationKind::Widening,
                               ApproximationKind::SoundOverApproximation, true);
        return result;
    }
    if (next.bottom_)
    {
        BoxDomain result(*this);
        result.recordOperation(OperationKind::Widening,
                               ApproximationKind::SoundOverApproximation, true);
        return result;
    }
    BoxDomain result(*this);
    for (Variable variable : boundedVariables())
    {
        Bound lower = boundAt(variable).lower();
        Bound upper = boundAt(variable).upper();
        const Interval& following = next.boundAt(variable);
        if (Bound::compareLower(following.lower(), lower) < 0)
        {
            lower = Bound::minusInfinity();
            if (following.lower().isFinite())
            {
                for (const Rational& threshold : policy.thresholds)
                {
                    if (threshold <= following.lower().value() &&
                            (lower.isMinusInfinity() || lower.value() < threshold))
                        lower = Bound::finite(threshold);
                }
            }
        }
        if (Bound::compare(following.upper(), upper) > 0)
        {
            upper = Bound::plusInfinity();
            if (following.upper().isFinite())
            {
                for (const Rational& threshold : policy.thresholds)
                {
                    if (following.upper().value() <= threshold &&
                            (upper.isPlusInfinity() || threshold < upper.value()))
                        upper = Bound::finite(threshold);
                }
            }
        }
        result.setBound(variable, Interval(lower, upper));
    }
    for (const LinearConstraint& threshold : policy.linearThresholds)
    {
        if (entails(threshold) == CheckResult::True &&
                next.entails(threshold) == CheckResult::True)
            result.assume(threshold);
    }
    result.recordOperation(OperationKind::Widening,
                           ApproximationKind::SoundOverApproximation, true);
    return result;
}

BoxDomain BoxDomain::narrow(const BoxDomain& next) const
{
    requireBox(next);
    if (bottom_ || next.bottom_)
    {
        BoxDomain result = bottom(config_);
        result.recordOperation(OperationKind::Narrowing,
                               ApproximationKind::Exact, true);
        return result;
    }
    BoxDomain result(*this);
    for (Variable variable : next.boundedVariables())
    {
        Bound lower = boundAt(variable).lower();
        Bound upper = boundAt(variable).upper();
        if (lower.isMinusInfinity())
            lower = next.boundAt(variable).lower();
        if (upper.isPlusInfinity())
            upper = next.boundAt(variable).upper();
        result.setBound(variable, Interval(lower, upper));
    }
    result.recordOperation(OperationKind::Narrowing, ApproximationKind::Exact,
                           true);
    return result;
}

bool BoxDomain::hasCompatibleDomain(const AbstractDomain& other) const
{
    const auto* box = other.isDomain<BoxDomain>()
                      ? &static_cast<const BoxDomain&>(other)
                      : nullptr;
    return box && config_.operationCompatible(box->config_);
}

void BoxDomain::joinDomain(const AbstractDomain& other)
{
    const BoxDomain& box = requireBox(other);
    if (box.bottom_)
        return;
    if (bottom_)
    {
        bottom_ = false;
        const auto copy = [this](const BoundSlot& slot)
        {
            storeFor(slot.variable).assign(slot);
            return true;
        };
        if (config_.storage.values == box.config_.storage.values)
            values_ = box.values_;
        else
            box.values_.forEach(copy);
        if (config_.storage.objectContents == box.config_.storage.objectContents)
            objectContents_ = box.objectContents_;
        else
            box.objectContents_.forEach(copy);
        return;
    }

    if (this == &box)
        return;
    values_.join(box.values_);
    objectContents_.join(box.objectContents_);
}

void BoxDomain::meetDomain(const AbstractDomain& other)
{
    const BoxDomain& box = requireBox(other);
    if (bottom_ || box.bottom_)
    {
        makeBottom();
        return;
    }
    for (Variable variable : box.boundedVariables())
    {
        setBound(variable,
                 meetIntervals(boundAt(variable), box.boundAt(variable)));
        if (bottom_)
            return;
    }
}

void BoxDomain::widenDomain(const AbstractDomain& next)
{
    *this = widen(requireBox(next));
}

void BoxDomain::narrowDomain(const AbstractDomain& next)
{
    *this = narrow(requireBox(next));
}

bool BoxDomain::isBottomDomain() const
{
    return bottom_;
}

bool BoxDomain::isTopDomain() const
{
    return !bottom_ && values_.empty() && objectContents_.empty();
}

bool BoxDomain::leqDomain(const AbstractDomain& other) const
{
    const BoxDomain& box = requireBox(other);
    if (bottom_)
        return true;
    if (box.bottom_)
        return false;
    const auto included = [this](const BoundSlot& slot)
    {
        return intervalIncluded(boundAt(slot.variable), slot.interval);
    };
    return (values_.equalPages(box.values_) || box.values_.forEach(included)) &&
           (objectContents_.equalPages(box.objectContents_) ||
            box.objectContents_.forEach(included));
}

std::string BoxDomain::domainToString() const
{
    if (bottom_)
        return "bottom";
    std::ostringstream output;
    output << "{";
    bool first = true;
    for (Variable variable : boundedVariables())
    {
        if (!first)
            output << ", ";
        first = false;
        output << "v" << variable.id() << "=" << boundAt(variable).toString();
    }
    output << "}";
    return output.str();
}

const BoxDomain& BoxDomain::requireBox(const AbstractDomain& other) const
{
    requireCompatible(other);
    return static_cast<const BoxDomain&>(other);
}

void BoxDomain::canonicalize(Variable variable)
{
    if (bottom_)
        return;
    Interval interval = boundAt(variable);
    if (config_.integerTightening &&
            variable.type().kind == NumericKind::Integer)
    {
        interval = Interval(integerLower(interval.lower()),
                            integerUpper(interval.upper()));
    }
    if (interval.isBottom())
    {
        makeBottom();
        return;
    }
    if (interval.isTop())
        eraseBound(variable);
    else
        storeBound(variable, std::move(interval));
}

void BoxDomain::setBound(Variable variable, Interval interval)
{
    const Interval& previous = boundAt(variable);
    if (previous == interval)
        return;
    if (config_.integerTightening && variable.type().kind == NumericKind::Integer &&
            ((interval.lower().isFinite() && (interval.lower().isStrict() ||
                    !interval.lower().value().isInteger())) ||
             (interval.upper().isFinite() && (interval.upper().isStrict() ||
                     !interval.upper().value().isInteger()))))
        interval = Interval(integerLower(interval.lower()),
                            integerUpper(interval.upper()));
    if (interval.isBottom())
        makeBottom();
    else if (interval.isTop())
        eraseBound(variable);
    else
        storeBound(variable, std::move(interval));
}

BoxDomain::BoundStore::BoundStore(BoxStorage storage)
    : width_(static_cast<std::uint32_t>(storage))
{
    if (width_)
        storage_.emplace<Directory>();
}

BoxDomain::BoundStore::Page BoxDomain::BoundStore::newPage() const
{
    switch (width_)
    {
    case 1:
        return allocatePage<1>();
    case 2:
        return allocatePage<2>();
    case 4:
        return allocatePage<4>();
    case 8:
        return allocatePage<8>();
    case 16:
        return allocatePage<16>();
    default:
        std::abort();
    }
}

void BoxDomain::BoundStore::detach(Page& page) const
{
    if (page.use_count() == 1)
        return;
    auto copy = newPage();
    std::copy_n(page.get(), width_, copy.get());
    page = std::move(copy);
}

bool BoxDomain::BoundStore::emptyPage(const Page& page) const
{
    return std::none_of(page.get(), page.get() + width_, [](const Slot& slot)
    {
        return slot.has_value();
    });
}

const BoxDomain::BoundSlot* BoxDomain::BoundStore::find(std::uint32_t id) const
{
    if (const auto* hash = std::get_if<Hash>(&storage_))
    {
        const auto found = hash->find(id);
        return found != hash->end() ? &found->second : nullptr;
    }
    const auto& pages = std::get<Directory>(storage_);
    const auto index = id / width_;
    const auto page = findPage(pages, index);
    if (page == pages.end() || page->index != index)
        return nullptr;
    const Slot& slot = page->page.get()[id % width_];
    return slot ? &*slot : nullptr;
}

void BoxDomain::BoundStore::assign(BoundSlot slot)
{
    const auto id = slot.variable.id();
    if (auto* hash = std::get_if<Hash>(&storage_))
    {
        hash->insert_or_assign(id, std::move(slot));
        return;
    }
    auto& pages = std::get<Directory>(storage_);
    const auto index = id / width_;
    auto page = findPage(pages, index);
    if (page == pages.end() || page->index != index)
        page = pages.insert(page, {index, newPage()});
    else
        detach(page->page);
    page->page.get()[id % width_] = std::move(slot);
}

void BoxDomain::BoundStore::erase(Variable variable)
{
    const auto id = variable.id();
    const auto checkType = [variable](const BoundSlot& slot)
    {
        if (slot.variable != variable)
        {
            assert(false && "Variable ID was reused with a different numeric type");
            std::abort();
        }
    };
    if (auto* hash = std::get_if<Hash>(&storage_))
    {
        const auto found = hash->find(id);
        if (found != hash->end())
        {
            checkType(found->second);
            hash->erase(found);
        }
        return;
    }
    auto& pages = std::get<Directory>(storage_);
    const auto index = id / width_;
    auto page = findPage(pages, index);
    if (page == pages.end() || page->index != index)
        return;
    const auto offset = id % width_;
    if (const auto& slot = page->page.get()[offset])
    {
        checkType(*slot);
        detach(page->page);
        page->page.get()[offset].reset();
        if (emptyPage(page->page))
            pages.erase(page);
    }
}

void BoxDomain::BoundStore::join(const BoundStore& other)
{
    if (width_ != other.width_)
    {
        BoundStore joined(static_cast<BoxStorage>(width_));
        forEach([&](const BoundSlot& slot)
        {
            const auto* match = other.find(slot.variable.id());
            if (match && slot.variable == match->variable)
            {
                auto interval = joinIntervals(slot.interval, match->interval);
                if (!interval.isTop())
                    joined.assign({slot.variable, std::move(interval)});
            }
            return true;
        });
        *this = std::move(joined);
        return;
    }
    if (auto* hash = std::get_if<Hash>(&storage_))
    {
        const auto& rhs = std::get<Hash>(other.storage_);
        for (auto it = hash->begin(); it != hash->end();)
        {
            const auto match = rhs.find(it->first);
            if (match == rhs.end() || it->second.variable != match->second.variable)
            {
                it = hash->erase(it);
                continue;
            }
            it->second.interval = joinIntervals(it->second.interval, match->second.interval);
            if (it->second.interval.isTop())
                it = hash->erase(it);
            else
                ++it;
        }
        return;
    }
    auto& left = std::get<Directory>(storage_);
    const auto& right = std::get<Directory>(other.storage_);
    Directory joined;
    joined.reserve(std::min(left.size(), right.size()));
    auto match = right.begin();
    for (const auto& entry : left)
    {
        while (match != right.end() && match->index < entry.index)
            ++match;
        if (match == right.end() || match->index != entry.index)
            continue;
        if (entry.page == match->page)
        {
            joined.push_back(entry);
            continue;
        }

        auto page = entry.page;
        detach(page);
        for (std::size_t i = 0; i < width_; ++i)
        {
            auto& l = page.get()[i];
            const auto& r = match->page.get()[i];
            if (!l)
                continue;
            if (r && l->variable == r->variable)
                l->interval = joinIntervals(l->interval, r->interval);
            else
                l.reset();
            if (l && l->interval.isTop())
                l.reset();
        }
        if (!emptyPage(page))
            joined.push_back({entry.index, std::move(page)});
    }
    left = std::move(joined);
}

bool BoxDomain::BoundStore::equalPages(const BoundStore& other) const
{
    const auto* l = std::get_if<Directory>(&storage_);
    const auto* r = std::get_if<Directory>(&other.storage_);
    if (!l || !r || width_ != other.width_ || l->size() != r->size())
        return false;
    for (std::size_t i = 0; i < l->size(); ++i)
    {
        const auto& a = (*l)[i];
        const auto& b = (*r)[i];
        if (a.index != b.index ||
                (a.page != b.page &&
                 !std::equal(a.page.get(), a.page.get() + width_, b.page.get())))
            return false;
    }
    return true;
}

void BoxDomain::BoundStore::clear()
{
    std::visit([](auto& store)
    {
        store.clear();
    }, storage_);
}

bool BoxDomain::BoundStore::empty() const
{
    return std::visit([](const auto& store)
    {
        return store.empty();
    }, storage_);
}

BoxDomain::BoundStore BoxDomain::BoundStore::without(
    const std::set<Variable>& omitted) const
{
    BoundStore result(static_cast<BoxStorage>(width_));
    if (const auto* source = std::get_if<Hash>(&storage_))
    {
        auto& selected = std::get<Hash>(result.storage_);
        for (const auto& [id, slot] : *source)
            if (!omitted.count(slot.variable))
                selected.emplace(id, slot);
        return result;
    }
    auto& selected = std::get<Directory>(result.storage_);
    const auto& source = std::get<Directory>(storage_);
    selected.reserve(source.size());
    for (const auto& entry : source)
    {
        auto page = entry.page;
        for (std::size_t i = 0; i < width_; ++i)
        {
            const auto& slot = entry.page.get()[i];
            if (slot && omitted.count(slot->variable))
            {
                detach(page);
                page.get()[i].reset();
            }
        }
        if (page == entry.page || !emptyPage(page))
            selected.push_back({entry.index, std::move(page)});
    }
    return result;
}

BoxDomain::BoundStore& BoxDomain::storeFor(Variable variable)
{
    return variable.role() == Variable::Role::ObjectContent ? objectContents_ : values_;
}

const BoxDomain::BoundStore& BoxDomain::storeFor(Variable variable) const
{
    return variable.role() == Variable::Role::ObjectContent ? objectContents_ : values_;
}

BoxDomain BoxDomain::withoutBounds(const std::set<Variable>& omitted) const
{
    auto result = top(config_);
    result.values_ = values_.without(omitted);
    result.objectContents_ = objectContents_.without(omitted);
    return result;
}

void BoxDomain::storeBound(Variable variable, Interval interval)
{
    storeFor(variable).assign({variable, std::move(interval)});
}

const Interval& BoxDomain::boundAt(Variable variable) const
{
    static const Interval top = Interval::top();
    const auto* slot = storeFor(variable).find(variable.id());
    if (!slot)
        return top;
    if (slot->variable != variable)
    {
        assert(false && "Variable ID was reused with a different numeric type");
        std::abort();
    }
    return slot->interval;
}

void BoxDomain::eraseBound(Variable variable)
{
    storeFor(variable).erase(variable);
}

std::vector<Variable> BoxDomain::boundedVariables() const
{
    std::vector<Variable> variables;
    const auto add = [&variables](const BoundSlot& slot)
    {
        variables.push_back(slot.variable);
        return true;
    };
    values_.forEach(add);
    objectContents_.forEach(add);
    std::sort(variables.begin(), variables.end());
    return variables;
}

std::vector<Variable> BoxDomain::boundedVariablesBefore(
    Variable upperBound) const
{
    auto variables = boundedVariables();
    const auto end = std::lower_bound(variables.begin(), variables.end(), upperBound);
    variables.erase(end, variables.end());
    return variables;
}

void BoxDomain::makeBottom()
{
    bottom_ = true;
    values_.clear();
    objectContents_.clear();
}

void BoxDomain::report(OperationKind operation, ApproximationKind approximation,
                       std::string reason, bool best) const
{
    recordOperation(operation, approximation, best, reason);
    if (config_.diagnostics)
        config_.diagnostics->report(
    {operation, approximation, std::move(reason)});
}

} // namespace SVF
