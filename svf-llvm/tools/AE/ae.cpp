//===- ae.cpp -- Abstract Execution -------------------------------------//
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
 // Abstract Execution
 //
 // Author: Jiawei Wang, Xiao Cheng, Jiawei Yang, Jiawei Ren, Yulei Sui
 */
#include "SVF-LLVM/PAGBuilder.h"
#include "WPA/WPAPass.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "WPA/Andersen.h"

#include "AE/Core/BoxAddressDomain.h"
#include "AE/Core/ConvexPolyhedraDomain.h"
#include "AE/Core/OctagonDomain.h"
#include "AE/Svfexe/AbstractInterpretation.h"
#include <limits>

using namespace SVF;
using namespace SVFUtil;


static Option<bool> SYMABS(
    "symabs",
    "relational abstract domain test",
    false
);

static Option<bool> AETEST(
    "aetest",
    "abstract execution basic function test",
    false
);

static void testRelationalDomains()
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
    const auto polyhedra = ConvexPolyhedraDomain::fromConstraints(constraints);
    assert(octagon.bound(y - x) == Interval::singleton(Rational(1)));
    assert(polyhedra.bound(y - x) == Interval::singleton(Rational(1)));
    assert(octagon.bound(Variable(2)) == Interval::closed(Rational(2), Rational(6)));
    assert(polyhedra.bound(Variable(2)) == Interval::closed(Rational(2), Rational(6)));
}

class AETest
{
    static Interval exact(s64_t value)
    {
        return Interval::singleton(Rational(value));
    }

public:
    void testIntegerBoundaryArithmetic()
    {
        const Rational smallest(std::numeric_limits<s64_t>::min());
        const Rational largest(std::numeric_limits<s64_t>::max());
        const Rational one(1);
        const Rational firstWide("9223372036854775808");

        assert(-smallest == firstWide);
        assert(largest + one == firstWide);
        assert(smallest - one == -firstWide - one);
        assert(smallest - smallest == Rational(0));
        assert(smallest * Rational(-1) == firstWide);
        assert(smallest / Rational(-1) == firstWide);
        assert((firstWide - one).toInt64() == std::numeric_limits<s64_t>::max());
    }

    void testIntervalBoundaryArithmetic()
    {
        const Rational smallest(std::numeric_limits<s64_t>::min());
        const Rational largest(std::numeric_limits<s64_t>::max());
        const Rational firstWide("9223372036854775808");
        const Rational one(1);
        const Interval machineRange = Interval::closed(smallest, largest);
        const Interval unit = exact(1);

        assert(subtract(unit, machineRange) ==
               Interval::closed(smallest + Rational(2), firstWide + one));
        assert(subtract(machineRange, unit) ==
               Interval::closed(smallest - one, largest - one));
        assert(multiply(unit, machineRange) == machineRange);
        assert(divide(Interval::singleton(smallest), Interval::singleton(Rational(-1))) ==
               Interval::singleton(firstWide));
        assert(remainder(Interval::singleton(smallest), Interval::singleton(Rational(-1))).isZero());
    }

    void testBinaryOpStmt()
    {
        assert(divide(exact(4), Interval::bottom()).isBottom());
        assert(divide(exact(-3), exact(2)) == exact(-1));
        assert(remainder(exact(-3), exact(2)) == exact(-1));
        assert(shiftLeft(exact(2), exact(3)) == exact(16));
        assert(shiftRight(exact(-15), exact(2)) == exact(-4));
        assert(bitwiseAnd(exact(-3), exact(2)) == exact(0));
        assert(bitwiseOr(exact(-3), exact(2)) == exact(-1));
        assert(bitwiseXor(exact(3), exact(2)) == exact(1));
    }

    void testLoadAndStore()
    {
        const Variable sourceA(1), sourceB(2), pointerA(3), pointerB(4);
        const Variable contentA(7, NumericType::integer(), Variable::Role::ObjectContent);
        const Variable contentB(8, NumericType::integer(), Variable::Role::ObjectContent);
        const Location cellA(7), cellB(8);
        const Interval intervalA = Interval::closed(Rational(1), Rational(3));
        const Interval intervalB = Interval::closed(Rational(2), Rational(7));
        BoxAddressDomain state(BoxDomain::top(), MemoryLayout({{cellA, contentA},
            {cellB, contentB}}));
        state.setInterval(sourceA, intervalA);
        state.setInterval(sourceB, intervalB);
        state.setAddressSet(pointerA, AddressSet::singleton(cellA));
        state.setAddressSet(pointerB, AddressSet::singleton(cellB));
        state.assignMemory(cellA, sourceA);
        state.assignMemory(cellB, sourceB);
        state.load(Variable(5), pointerA);
        state.load(Variable(6), pointerB);
        assert(state.interval(Variable(5)) == intervalA);
        assert(state.interval(Variable(6)) == intervalB);
    }
};


int main(int argc, char** argv)
{
    int arg_num = 0;
    int extraArgc = 3;
    char **arg_value = new char *[argc + extraArgc];
    for (; arg_num < argc; ++arg_num)
    {
        arg_value[arg_num] = argv[arg_num];
    }
    // add extra options
    arg_value[arg_num++] = (char*) "-model-consts=true";
    arg_value[arg_num++] = (char*) "-model-arrays=true";
    arg_value[arg_num++] = (char*) "-pre-field-sensitive=false";
    assert(arg_num == (argc + extraArgc) && "more extra arguments? Change the value of extraArgc");

    std::vector<std::string> moduleNameVec;
    moduleNameVec = OptionBase::parseOptions(
                        arg_num, arg_value, "Static Symbolic Execution", "[options] <input-bitcode...>"
                    );
    delete[] arg_value;
    if (SYMABS())
    {
        testRelationalDomains();
        return 0;
    }

    if (AETEST())
    {
        AETest aeTest;
        aeTest.testIntegerBoundaryArithmetic();
        aeTest.testIntervalBoundaryArithmetic();
        aeTest.testBinaryOpStmt();
        aeTest.testLoadAndStore();
        return 0;
    }

    LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);
    PAGBuilder builder;
    PAG* pag = builder.build();
    // Run Andersen's to resolve indirect calls, then update PAG with resolved targets.
    // The Andersen singleton will be reused inside AbstractInterpretation::runOnModule().
    AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);
    builder.updateCallGraph(ander->getCallGraph());
    AbstractInterpretation& ae = AbstractInterpretation::getAEInstance();
    if (Options::BufferOverflowCheck())
        ae.addDetector(std::make_unique<BufOverflowDetector>());
    if (Options::NullDerefCheck())
        ae.addDetector(std::make_unique<NullptrDerefDetector>());
    ae.runOnModule();

    AndersenWaveDiff::releaseAndersenWaveDiff();
    LLVMModuleSet::releaseLLVMModuleSet();

    return 0;
}
