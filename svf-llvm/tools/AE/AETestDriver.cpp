//===- AETestDriver.cpp -- Abstract Execution self-tests -----------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2017>  <Yulei Sui>
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
//===-----------------------------------------------------------------------===//

/*
 // Abstract Execution self-tests
 //
 // Author: Jiawei Wang, Xiao Cheng, Jiawei Yang, Jiawei Ren, Yulei Sui
 */
#include "AETestDriver.h"

#include "AE/Core/BoxAddressDomain.h"
#include "AE/Core/OctagonDomain.h"
#include "AE/Core/PolyhedraDomain.h"
#include "Util/CommandLine.h"

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>

namespace SVF
{

namespace
{

Option<bool> SYMABS(
    "symabs",
    "run the relational abstract domain tests",
    false
);

Option<bool> AETEST(
    "aetest",
    "run the basic abstract execution tests",
    false
);

void check(bool passed, const char* description)
{
    if (!passed)
    {
        std::cerr << "AE self-test failed: " << description << '\n';
        std::abort();
    }
}

Interval exact(std::int64_t value)
{
    return Interval::singleton(Rational(value));
}

void testRelationalDomains()
{
    const LinearExpression x(Variable(1));
    const LinearExpression y(Variable(2));
    const LinearExpression one(Rational(1));
    const LinearConstraintSet constraints
    {
        lessEqual(one, x),
        lessEqual(x, LinearExpression(Rational(5))),
        equal(y, x + one)
    };
    const auto octagon = OctagonDomain::fromConstraints(constraints);
    const auto polyhedra = PolyhedraDomain::fromConstraints(constraints);
    const auto difference = exact(1);
    const auto range = Interval::closed(Rational(2), Rational(6));
    check(octagon.bound(y - x) == difference, "Octagon preserves the difference y - x");
    check(polyhedra.bound(y - x) == difference, "Polyhedra preserves the difference y - x");
    check(octagon.bound(Variable(2)) == range, "Octagon projects the bounds on y");
    check(polyhedra.bound(Variable(2)) == range, "Polyhedra projects the bounds on y");
}

void testIntegerBoundaryArithmetic()
{
    const Rational smallest(std::numeric_limits<std::int64_t>::min());
    const Rational largest(std::numeric_limits<std::int64_t>::max());
    const Rational one(1);
    const Rational firstWide("9223372036854775808");

    check(-smallest == firstWide, "negating INT64_MIN");
    check(largest + one == firstWide, "adding past INT64_MAX");
    check(smallest - one == -firstWide - one, "subtracting below INT64_MIN");
    check(smallest - smallest == Rational(0), "subtracting INT64_MIN from itself");
    check(smallest * Rational(-1) == firstWide, "multiplying INT64_MIN by minus one");
    check(smallest / Rational(-1) == firstWide, "dividing INT64_MIN by minus one");
    check((firstWide - one).toInt64() == std::numeric_limits<std::int64_t>::max(),
          "converting a value back to the signed 64-bit range");
}

void testIntervalBoundaryArithmetic()
{
    const Rational smallest(std::numeric_limits<std::int64_t>::min());
    const Rational largest(std::numeric_limits<std::int64_t>::max());
    const Rational firstWide("9223372036854775808");
    const Rational one(1);
    const Interval machineRange = Interval::closed(smallest, largest);
    const Interval unit = exact(1);
    const Interval minimum = Interval::singleton(smallest);

    check(subtract(unit, machineRange) ==
          Interval::closed(smallest + Rational(2), firstWide + one),
          "interval subtraction preserves the wide upper endpoint");
    check(subtract(machineRange, unit) == Interval::closed(smallest - one, largest - one),
          "interval subtraction preserves the wide lower endpoint");
    check(multiply(unit, machineRange) == machineRange, "interval multiplication by one");
    check(divide(minimum, exact(-1)) == Interval::singleton(firstWide),
          "interval division preserves the wide result");
    check(remainder(minimum, exact(-1)).isZero(), "interval remainder at INT64_MIN");
}

void testBinaryOpStmt()
{
    check(divide(exact(4), Interval::bottom()).isBottom(), "division propagates bottom");
    check(divide(exact(-3), exact(2)) == exact(-1), "signed division rounds toward zero");
    check(remainder(exact(-3), exact(2)) == exact(-1), "remainder keeps the dividend's sign");
    check(shiftLeft(exact(2), exact(3)) == exact(16), "left shift");
    check(shiftRight(exact(-15), exact(2)) == exact(-4), "arithmetic right shift");
    check(bitwiseAnd(exact(-3), exact(2)) == exact(0), "bitwise and");
    check(bitwiseOr(exact(-3), exact(2)) == exact(-1), "bitwise or");
    check(bitwiseXor(exact(3), exact(2)) == exact(1), "bitwise xor");
}

void testLoadAndStore()
{
    const Variable sourceA(1), sourceB(2), pointerA(3), pointerB(4);
    const Variable contentA(7, NumericType::integer(), Variable::Role::ObjectContent);
    const Variable contentB(8, NumericType::integer(), Variable::Role::ObjectContent);
    const Location cellA(7), cellB(8);
    const Interval intervalA = Interval::closed(Rational(1), Rational(3));
    const Interval intervalB = Interval::closed(Rational(2), Rational(7));
    const MemoryLayout layout({{cellA, contentA}, {cellB, contentB}});
    BoxAddressDomain state(BoxDomain::top(), layout);
    state.setInterval(sourceA, intervalA);
    state.setInterval(sourceB, intervalB);
    state.setAddressSet(pointerA, AddressSet::singleton(cellA));
    state.setAddressSet(pointerB, AddressSet::singleton(cellB));
    state.assignMemory(cellA, sourceA);
    state.assignMemory(cellB, sourceB);
    state.load(Variable(5), pointerA);
    state.load(Variable(6), pointerB);
    check(state.interval(Variable(5)) == intervalA, "first load reads the first object's interval");
    check(state.interval(Variable(6)) == intervalB, "second load reads the second object's interval");
}

} // namespace

bool runAEDomainTests()
{
    if (SYMABS())
    {
        testRelationalDomains();
        return true;
    }

    if (!AETEST())
        return false;

    testIntegerBoundaryArithmetic();
    testIntervalBoundaryArithmetic();
    testBinaryOpStmt();
    testLoadAndStore();
    return true;
}

} // namespace SVF
