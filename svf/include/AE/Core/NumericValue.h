//===- NumericValue.h -- Exact integer and rational values -*- C++ -*-===//
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

#ifndef SVF_AE_NUMERIC_VALUE_H
#define SVF_AE_NUMERIC_VALUE_H

#include <cstdint>
#include <string>
#include <variant>

#include <gmpxx.h>

namespace SVF
{

class Integer
{
public:
    Integer();
    explicit Integer(std::int64_t value);
    explicit Integer(const std::string& value);

    const mpz_class& value() const
    {
        return value_;
    }
    std::string toString() const;

    friend bool operator==(const Integer& lhs, const Integer& rhs)
    {
        return lhs.value_ == rhs.value_;
    }

private:
    mpz_class value_;
};

/// Exact numbers with an inline signed-64-bit integer representation.
class Rational
{
public:
    Rational() = default;
    explicit Rational(std::int64_t value) : storage_(value) {}
    explicit Rational(const Integer& value);
    explicit Rational(const std::string& value);
    Rational(const Integer& numerator, const Integer& denominator);

    static Rational fromRaw(const mpq_class& value);
    static Rational fromDouble(double value);
    /// Import a little-endian sequence of words, with an optional sign bit.
    static Rational fromIntegerBits(const std::uint64_t* words,
                                    unsigned bitWidth, bool signedValue);

    mpq_class value() const;
    bool isZero() const
    {
        const auto* small = inlineInteger();
        return small ? *small == 0 : mpq_sgn(large().get_mpq_t()) == 0;
    }
    bool isInteger() const;
    bool tryToInt64(std::int64_t& result) const;
    std::int64_t toInt64() const;
    double toDouble() const;
    int sign() const
    {
        const auto* small = inlineInteger();
        return small ? (*small > 0) - (*small < 0) : mpq_sgn(large().get_mpq_t());
    }
    std::string toString() const;

    Rational floor() const;
    Rational ceil() const;
    Rational dividedByPowerOfTwo(unsigned exponent) const;
    Rational& assignSum(const Rational& lhs, const Rational& rhs);
    Rational& divideByPowerOfTwoInPlace(unsigned exponent);

    Rational& operator+=(const Rational& rhs);
    Rational& operator-=(const Rational& rhs);
    Rational& operator*=(const Rational& rhs);
    Rational& operator/=(const Rational& rhs);

    friend Rational operator+(Rational lhs, const Rational& rhs)
    {
        return lhs += rhs;
    }
    friend Rational operator-(Rational lhs, const Rational& rhs)
    {
        return lhs -= rhs;
    }
    friend Rational operator*(Rational lhs, const Rational& rhs)
    {
        return lhs *= rhs;
    }
    friend Rational operator/(Rational lhs, const Rational& rhs)
    {
        return lhs /= rhs;
    }
    friend Rational operator-(const Rational& value);

    friend bool operator==(const Rational& lhs, const Rational& rhs)
    {
        return compare(lhs, rhs) == 0;
    }
    friend bool operator!=(const Rational& lhs, const Rational& rhs)
    {
        return !(lhs == rhs);
    }
    friend bool operator<(const Rational& lhs, const Rational& rhs)
    {
        return compare(lhs, rhs) < 0;
    }
    friend bool operator<=(const Rational& lhs, const Rational& rhs)
    {
        return compare(lhs, rhs) <= 0;
    }
    friend bool operator>(const Rational& lhs, const Rational& rhs)
    {
        return rhs < lhs;
    }
    friend bool operator>=(const Rational& lhs, const Rational& rhs)
    {
        return rhs <= lhs;
    }

private:
    const std::int64_t* inlineInteger() const
    {
        return std::get_if<std::int64_t>(&storage_);
    }
    const mpq_class& large() const
    {
        return std::get<mpq_class>(storage_);
    }
    static int compare(const Rational& lhs, const Rational& rhs);
    void storeCanonical(mpq_class value);
    std::variant<std::int64_t, mpq_class> storage_{std::int64_t{0}};
};

} // namespace SVF

#endif // SVF_AE_NUMERIC_VALUE_H
