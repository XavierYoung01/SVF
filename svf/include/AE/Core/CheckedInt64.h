//===- CheckedInt64.h -- Finite integer arithmetic -----------*- C++ -*-===//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2022>  <Yulei Sui>
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

#ifndef SVF_AE_CHECKED_INT64_H
#define SVF_AE_CHECKED_INT64_H

#include <cstdint>
#include <limits>

namespace SVF
{

struct CheckedInt64
{
    using Int = std::int64_t;
    static constexpr auto Min = std::numeric_limits<Int>::min();
    static constexpr auto Max = std::numeric_limits<Int>::max();

    static bool add(Int lhs, Int rhs, Int& result)
    {
#if defined(__clang__) || defined(__GNUC__)
        return !__builtin_add_overflow(lhs, rhs, &result);
#else
        if ((rhs > 0 && lhs > Max - rhs) || (rhs < 0 && lhs < Min - rhs))
            return false;
        result = lhs + rhs;
        return true;
#endif
    }

    static bool sub(Int lhs, Int rhs, Int& result)
    {
#if defined(__clang__) || defined(__GNUC__)
        return !__builtin_sub_overflow(lhs, rhs, &result);
#else
        if ((rhs < 0 && lhs > Max + rhs) || (rhs > 0 && lhs < Min + rhs))
            return false;
        result = lhs - rhs;
        return true;
#endif
    }

    static bool mul(Int lhs, Int rhs, Int& result)
    {
#if defined(__clang__) || defined(__GNUC__)
        return !__builtin_mul_overflow(lhs, rhs, &result);
#else
        if (lhs > 0)
        {
            if ((rhs > 0 && lhs > Max / rhs) || (rhs < 0 && rhs < Min / lhs))
                return false;
        }
        else if ((rhs > 0 && lhs < Min / rhs) || (rhs < 0 && lhs < Max / rhs))
            return false;
        result = lhs * rhs;
        return true;
#endif
    }

    static bool div(Int lhs, Int rhs, Int& result)
    {
        if (rhs == 0 || (lhs == Min && rhs == -1))
            return false;
        result = lhs / rhs;
        return true;
    }
};

} // namespace SVF

#endif // SVF_AE_CHECKED_INT64_H
