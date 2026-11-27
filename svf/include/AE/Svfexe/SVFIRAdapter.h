//===- SVFIRAdapter.h -- PAG to abstract-domain symbols ----*- C++ -*-===//
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

#ifndef SVF_AE_SVFIR_ADAPTER_H
#define SVF_AE_SVFIR_ADAPTER_H

#include "AE/Core/BoxAddressDomain.h"

#include "Util/GeneralType.h"

namespace SVF
{

class ConstIntObjVar;
class ConstIntValVar;
class ObjVar;
class PAG;
class ValVar;

/// Translate frontend types while preserving the PAG identity in each key.
class SVFIRAdapter
{
public:
    explicit SVFIRAdapter(const PAG& svfir);

    /// PAG's double projection can overflow for extended FP constants.
    /// Such values have no rational singleton; retain an unconstrained number.
    static SVF::Interval floatingConstant(double value);
    static SVF::Rational integerConstant(const ConstIntValVar& value);
    static SVF::Rational integerConstant(const ConstIntObjVar& value);

    bool contains(const ValVar& value) const;
    bool isScalar(SVF::Variable variable) const;

    SVF::Variable variable(const ValVar& value) const;
    const ValVar* value(SVF::Variable variable) const;
    SVF::Location location(const ObjVar& object) const;
    SVF::Variable contentVariable(const ObjVar& object) const;
    const ObjVar& object(SVF::Location location) const;
    void registerObject(const ObjVar& object) const;

    const SVF::MemoryLayout& memoryLayout() const
    {
        return memoryLayout_;
    }

private:
    const PAG& pag_;
    mutable SVF::MemoryLayout memoryLayout_;
};

} // namespace SVF

#endif // SVF_AE_SVFIR_ADAPTER_H
