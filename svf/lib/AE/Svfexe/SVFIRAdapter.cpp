//===- SVFIRAdapter.cpp -- PAG to abstract-domain symbols ------------===//
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
// Contributors: Jiawei Yang
//
//===----------------------------------------------------------------------===//

#include <cassert>
#include <cstdlib>
#include "AE/Svfexe/SVFIRAdapter.h"

#include "Graphs/PAG.h"
#include "SVFValues/SVFType.h"
#include "SVFValues/SVFVariables.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"

#include <cmath>
#include <string>

namespace SVF
{

using SVF::Location;
using SVF::MemoryLayout;
using SVF::Variable;

namespace
{

SVF::NumericType numericType(const SVFType* type, bool pointer)
{
    if (pointer)
        return SVF::NumericType::integer();

    if (!type || type->getKind() == SVFType::SVFIntegerTy)
        return SVF::NumericType::integer();
    if (type->getKind() != SVFType::SVFOtherTy)
        return SVF::NumericType::real();

    const std::string representation = type->toString();
    using SVF::FloatFormat;
    if (representation == "half")
        return SVF::NumericType::ieee(FloatFormat{5, 11});
    if (representation == "bfloat")
        return SVF::NumericType::ieee(FloatFormat{8, 8});
    if (representation == "float")
        return SVF::NumericType::ieee(FloatFormat::binary32());
    if (representation == "double")
        return SVF::NumericType::ieee(FloatFormat::binary64());
    if (representation == "x86_fp80")
        return SVF::NumericType::ieee(FloatFormat{15, 64});
    if (representation == "fp128")
        return SVF::NumericType::ieee(FloatFormat{15, 113});
    // Other scalar types have no integer semantics known to this adapter.
    // Real is conservative and, unlike Integer, cannot tighten a fractional
    // value to the empty set.
    return SVF::NumericType::real();
}

SVF::NumericType numericType(const SVFVar& variable)
{
    return numericType(variable.getType(), variable.isPointer());
}

SVF::NumericType contentNumericType(const ObjVar& object)
{
    const auto* gep = SVFUtil::dyn_cast<GepObjVar>(&object);
    if (!gep)
        return numericType(object);

    // GepObjVar::getType() asserts for overflow/summary fields and opaque
    // aggregates. Inspect the flattened layout with an explicit bounds check
    // so ordinary fields keep their precise type while such implementation
    // objects conservatively use Real.
    const SVFType* baseType = gep->getBaseObj()->getType();
    if (!baseType)
        return SVF::NumericType::real();
    const StInfo* typeInfo = baseType->getTypeInfo();
    const auto& elementTypes =
        Options::ModelArrays() ? typeInfo->getFlattenElementTypes()
        : typeInfo->getFlattenFieldTypes();
    const auto offset = static_cast<std::size_t>(gep->getConstantFieldIdx());
    if (offset >= elementTypes.size())
        return SVF::NumericType::real();
    const SVFType* elementType = elementTypes[offset];
    return numericType(elementType,
                       elementType && elementType->isPointerTy());
}

template <typename Constant>
Rational integerValue(const Constant& value)
{
    const auto& literal = value.getIntegerLiteral();
    if (literal.fitsSigned64)
        return Rational(value.getSExtValue());
    return Rational::fromIntegerBits(literal.wideWords.data(), literal.bitWidth, true);
}

} // namespace

SVF::Interval SVFIRAdapter::floatingConstant(double value)
{
    if (!std::isfinite(value))
        return SVF::Interval::top();
    return SVF::Interval::singleton(
               SVF::Rational(static_cast<s64_t>(value)));
}

Rational SVFIRAdapter::integerConstant(const ConstIntValVar& value)
{
    return integerValue(value);
}

Rational SVFIRAdapter::integerConstant(const ConstIntObjVar& value)
{
    return integerValue(value);
}

SVFIRAdapter::SVFIRAdapter(const PAG& svfir) : pag_(svfir)
{
    for (const auto& entry : pag_)
    {
        if (const auto* object = SVFUtil::dyn_cast<ObjVar>(entry.second))
            registerObject(*object);
    }
}

void SVFIRAdapter::registerObject(const ObjVar& object) const
{
    const Location key = location(object);
    if (!memoryLayout_.contains(key))
        memoryLayout_.extend(key, contentVariable(object));
}

bool SVFIRAdapter::contains(const ValVar& value) const
{
    // Directly interpreted numeric constants need no state entry. Pointer
    // constants still carry transfer results, such as initializer GEPs.
    return value.isPointer() || !value.isConstDataOrAggDataButNotNullPtr();
}

bool SVFIRAdapter::isScalar(Variable variable) const
{
    return variable.role() == Variable::Role::Value;
}

Variable SVFIRAdapter::variable(const ValVar& value) const
{
    assert(contains(value) && "ValVar is not tracked by this adapter");
    return Variable(value.getId(), numericType(value));
}

const ValVar* SVFIRAdapter::value(Variable variable) const
{
    return isScalar(variable) ? pag_.getValVar(variable.id()) : nullptr;
}

Location SVFIRAdapter::location(const ObjVar& object) const
{
    return Location(object.getId());
}

Variable SVFIRAdapter::contentVariable(const ObjVar& object) const
{
    return Variable(object.getId(), contentNumericType(object),
                    Variable::Role::ObjectContent);
}

const ObjVar& SVFIRAdapter::object(Location location) const
{
    const auto* result = pag_.getObjVar(location.id());
    assert(result && "address does not denote an object");
    return *result;
}

} // namespace SVF
