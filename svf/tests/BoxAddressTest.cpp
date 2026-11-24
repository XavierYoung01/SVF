// Tests for the public Box and Address APIs, linked without PAG or LLVM.
#ifdef NDEBUG
#undef NDEBUG
#endif

#include "AE/Core/AddressDomain.h"
#include "AE/Core/NumericalDomain.h"

#include <array>
#include <cassert>
#include <limits>
#include <set>

using namespace SVF;

static Interval number(std::int64_t value)
{
    return Interval::singleton(Rational(value));
}

static void checkNumbers()
{
    constexpr auto min = std::numeric_limits<std::int64_t>::min();
    constexpr auto max = std::numeric_limits<std::int64_t>::max();
    const Rational one(1);
    const Rational twoTo63("9223372036854775808");
    assert(Rational(max) + one == twoTo63);
    assert(Rational(min) - one == -twoTo63 - one);
    assert(-Rational(min) == twoTo63);
    assert(Rational(min) / Rational(-1) == twoTo63);
    assert(Rational(max) * Rational(2) == twoTo63 * Rational(2) - Rational(2));
    assert(Rational(max) < twoTo63);
    assert((twoTo63 - one).toInt64() == max);
    assert((Rational(2) / Rational(6)).value() == mpq_class(1, 3));

    const std::uint64_t words[] = {7, 0, 0, std::uint64_t{1} << 63};
    const auto positive = Rational::fromIntegerBits(words, 256, false);
    const auto negative = Rational::fromIntegerBits(words, 256, true);
    mpz_class sign = 1;
    sign <<= 255;
    assert(positive.value() == mpq_class(sign + 7));
    assert(negative.value() == mpq_class(-sign + 7));
}

static void checkBox()
{
    constexpr std::array layouts{BoxStorage::Hash, BoxStorage::Page1, BoxStorage::Page2,
                                 BoxStorage::Page4, BoxStorage::Page8, BoxStorage::Page16};
    const Variable value(2);
    const Variable neighboringValue(3);
    const Variable otherPage(100);
    const Variable object(2, NumericType::integer(), Variable::Role::ObjectContent);
    auto reference = BoxDomain::top();
    reference.assignBound(value, number(10));
    reference.assignBound(neighboringValue, number(11));
    reference.assignBound(otherPage, number(12));
    reference.assignBound(object, number(20));

    for (BoxStorage values : layouts)
    {
        for (BoxStorage objects : layouts)
        {
            BoxSemanticConfig config;
            config.storage = {values, objects};
            auto box = BoxDomain::bottom(config);
            box.joinWith(reference);
            assert(box.config().storage.values == values);
            assert(box.config().storage.objectContents == objects);
            assert(box.isSubsetOf(reference) == CheckResult::True);
            assert(reference.isSubsetOf(box) == CheckResult::True);

            auto snapshot = box;
            snapshot.assignBound(value, number(99));
            snapshot.forget(otherPage);
            assert(box.bound(value) == number(10));
            assert(box.bound(otherPage) == number(12));
            assert(snapshot.bound(neighboringValue) == number(11));
            assert(snapshot.bound(object) == number(20));
            assert(snapshot.bound(otherPage).isTop());

            snapshot.joinWith(reference);
            assert(snapshot.bound(value) == Interval::closed(Rational(10), Rational(99)));
            snapshot.meetWith(reference);
            assert(snapshot.bound(value) == number(10));
            assert(snapshot.bound(otherPage) == number(12));
        }
    }
}

static void checkAddress()
{
    constexpr std::array layouts{AddressSetStorage::Hash, AddressSetStorage::OneWithSharedOverflow,
                                 AddressSetStorage::FourWithPrivateOverflow};
    const Variable pointer(1);
    const Variable onNextPage(32);
    const Location blackHole(0);
    assert(blackHole != Location::null());
    for (AddressSetStorage storage : layouts)
    {
        auto addresses = AddressDomain::top(storage);
        AddressSet set = AddressSet::singleton(blackHole);
        for (unsigned id = 2; id <= 6; ++id)
            set.insert(Location(id));
        addresses.assign(pointer, set);
        for (unsigned id = 2; id <= 16; ++id)
            addresses.assign(Variable(id), AddressSet::singleton(Location(id)));
        auto beforePromotion = addresses;
        addresses.assign(onNextPage, AddressSet::singleton(Location::null()));
        assert(beforePromotion.addressSet(onNextPage).isTop());

        auto snapshot = addresses;
        auto extended = snapshot.addressSet(pointer);
        extended.insert(Location(100));
        snapshot.assign(pointer, extended);
        snapshot.forget(onNextPage);
        assert(!addresses.addressSet(pointer).contains(Location(100)));
        assert(snapshot.addressSet(pointer).contains(Location(100)));
        assert(!addresses.addressSet(pointer).contains(Location::null()));
        assert(addresses.addressSet(onNextPage).contains(Location::null()));
        assert(addresses.addressSet(Variable(2)).contains(Location(2)));

        auto differentStorage = AddressDomain::bottom(AddressSetStorage::Hash);
        differentStorage.joinWith(addresses);
        assert(differentStorage.setStorage() == AddressSetStorage::Hash);
        assert(differentStorage.addressSet(pointer) == set);
        snapshot.meetWith(differentStorage);
        assert(snapshot.addressSet(pointer) == set);
        assert(snapshot.without({pointer}).addressSet(pointer).isTop());
        assert(snapshot.addressSet(pointer) == set);
    }
}

int main()
{
    checkNumbers();
    checkBox();
    checkAddress();
}
