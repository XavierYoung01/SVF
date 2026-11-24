//===- AddressDomain.cpp -- Address-set abstract property ----------------===//
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
// Contributors: Xiao Cheng, Jiawei Yang
//
//===----------------------------------------------------------------------===//

#include "AE/Core/AddressDomain.h"

#include <cstdlib>
#include <cassert>
#include <algorithm>
#include <iterator>
#include <sstream>
#include <utility>

namespace SVF
{
FiniteLocationSet::const_iterator::reference
FiniteLocationSet::const_iterator::operator*() const
{
    if (const auto* sorted = std::get_if<pointer>(&position_))
        return **sorted;
    return *std::get<Hash::const_iterator>(position_);
}

FiniteLocationSet::const_iterator& FiniteLocationSet::const_iterator::operator++()
{
    if (auto* sorted = std::get_if<pointer>(&position_))
        ++*sorted;
    else
        ++std::get<Hash::const_iterator>(position_);
    return *this;
}

FiniteLocationSet::const_iterator FiniteLocationSet::const_iterator::operator++(int)
{
    auto previous = *this;
    ++*this;
    return previous;
}

FiniteLocationSet::FiniteLocationSet(const FiniteLocationSet& other)
    : storage_(other.storage_), inlineSize_(other.inlineSize_)
{
    if (const auto* locations = std::get_if<Small>(&other.contents_))
        contents_ = *locations;
    else if (const auto* shared = std::get_if<Shared>(&other.contents_))
        contents_ = *shared;
    else if (const auto* owned = std::get_if<Private>(&other.contents_))
        contents_ = std::make_unique<Buffer>(**owned);
    else
        contents_ = std::make_unique<Hash>(*std::get<std::unique_ptr<Hash>>(other.contents_));
}

FiniteLocationSet::FiniteLocationSet(FiniteLocationSet&& other) noexcept
    : storage_(other.storage_), inlineSize_(other.inlineSize_),
      contents_(std::move(other.contents_))
{
    other.clear();
}

FiniteLocationSet& FiniteLocationSet::operator=(FiniteLocationSet&& other) noexcept
{
    if (this != &other)
    {
        storage_ = other.storage_;
        inlineSize_ = other.inlineSize_;
        contents_ = std::move(other.contents_);
        other.clear();
    }
    return *this;
}

FiniteLocationSet& FiniteLocationSet::operator=(const FiniteLocationSet& other)
{
    if (this != &other)
        *this = FiniteLocationSet(other);
    return *this;
}

std::size_t FiniteLocationSet::size() const
{
    if (const auto* shared = std::get_if<Shared>(&contents_))
        return (*shared)->size();
    if (const auto* owned = std::get_if<Private>(&contents_))
        return (*owned)->size();
    if (const auto* hash = std::get_if<std::unique_ptr<Hash>>(&contents_))
        return (*hash)->size();
    return inlineSize_;
}

std::size_t FiniteLocationSet::inlineCapacity() const
{
    return storage_ == AddressSetStorage::FourWithPrivateOverflow ? 4 : 1;
}

const Location* FiniteLocationSet::sortedData() const
{
    if (const auto* shared = std::get_if<Shared>(&contents_))
        return (*shared)->data();
    if (const auto* owned = std::get_if<Private>(&contents_))
        return (*owned)->data();
    return std::get<Small>(contents_).data();
}

bool FiniteLocationSet::contains(Location location) const
{
    if (const auto* hash = std::get_if<std::unique_ptr<Hash>>(&contents_))
        return (*hash)->count(location) != 0;
    const auto* first = sortedData();
    const auto* last = first + size();
    return std::holds_alternative<Small>(contents_)
           ? std::find(first, last, location) != last
           : std::binary_search(first, last, location);
}

FiniteLocationSet::const_iterator FiniteLocationSet::begin() const
{
    if (const auto* hash = std::get_if<std::unique_ptr<Hash>>(&contents_))
        return const_iterator((*hash)->cbegin());
    return const_iterator(sortedData());
}

FiniteLocationSet::const_iterator FiniteLocationSet::end() const
{
    if (const auto* hash = std::get_if<std::unique_ptr<Hash>>(&contents_))
        return const_iterator((*hash)->cend());
    return const_iterator(sortedData() + size());
}

void FiniteLocationSet::insert(Location location)
{
    if (storage_ == AddressSetStorage::Hash)
    {
        if (!std::holds_alternative<std::unique_ptr<Hash>>(contents_))
            contents_ = std::make_unique<Hash>();
        std::get<std::unique_ptr<Hash>>(contents_)->insert(location);
        return;
    }

    const auto* first = sortedData();
    const auto* last = first + size();
    const auto* position = std::lower_bound(first, last, location);
    if (position != last && *position == location)
        return;
    const auto index = position - first;
    if (auto* small = std::get_if<Small>(&contents_))
    {
        if (inlineSize_ < inlineCapacity())
        {
            std::move_backward(small->begin() + index, small->begin() + inlineSize_,
                               small->begin() + inlineSize_ + 1);
            (*small)[index] = location;
            ++inlineSize_;
            return;
        }
        Buffer expanded(first, last);
        expanded.insert(expanded.begin() + index, location);
        assign(std::move(expanded));
    }
    else if (auto* shared = std::get_if<Shared>(&contents_))
    {
        if (shared->use_count() != 1)
            *shared = std::make_shared<Buffer>(**shared);
        (*shared)->insert((*shared)->begin() + index, location);
    }
    else
    {
        auto& owned = std::get<Private>(contents_);
        owned->insert(owned->begin() + index, location);
    }
}

// Input is sorted and unique when it comes from a sorted set operation.
void FiniteLocationSet::assign(std::vector<Location> locations)
{
    if (storage_ == AddressSetStorage::Hash && !locations.empty())
    {
        contents_ = std::make_unique<Hash>(locations.begin(), locations.end());
        inlineSize_ = 0;
    }
    else if (locations.size() <= inlineCapacity())
    {
        Small small{};
        std::copy(locations.begin(), locations.end(), small.begin());
        contents_ = small;
        inlineSize_ = static_cast<std::uint8_t>(locations.size());
    }
    else if (storage_ == AddressSetStorage::OneWithSharedOverflow)
        contents_ = std::make_shared<Buffer>(std::move(locations));
    else
        contents_ = std::make_unique<Buffer>(std::move(locations));
}

void FiniteLocationSet::clear()
{
    contents_ = Small{};
    inlineSize_ = 0;
}

bool operator==(const FiniteLocationSet& lhs, const FiniteLocationSet& rhs)
{
    if (lhs.size() != rhs.size())
        return false;
    if (lhs.storage_ != AddressSetStorage::Hash && rhs.storage_ != AddressSetStorage::Hash)
        return std::equal(lhs.sortedData(), lhs.sortedData() + lhs.size(), rhs.sortedData());
    return std::all_of(lhs.begin(), lhs.end(), [&](Location location)
    {
        return rhs.contains(location);
    });
}

AddressSet AddressSet::bottom()
{
    return AddressSet(false, false);
}

AddressSet AddressSet::objectTop()
{
    return AddressSet(true, false);
}

AddressSet AddressSet::rawTop()
{
    return AddressSet(false, true);
}

AddressSet AddressSet::rawOrNull()
{
    AddressSet result = rawTop();
    result.insert(Location::null());
    return result;
}

AddressSet AddressSet::top()
{
    AddressSet result(true, true);
    result.insert(Location::null());
    return result;
}

AddressSet AddressSet::singleton(Location location)
{
    AddressSet result = bottom();
    result.insert(location);
    return result;
}

bool AddressSet::isBottom() const
{
    return !allObjects_ && !mayContainRawAddress_ && locations_.empty();
}

bool AddressSet::isTop() const
{
    return allObjects_ && mayContainRawAddress_ &&
           locations_.contains(Location::null());
}

bool AddressSet::isObjectTop() const
{
    return allObjects_ && !mayContainRawAddress_ && locations_.empty();
}

bool AddressSet::isRawTop() const
{
    return !allObjects_ && mayContainRawAddress_ && locations_.empty();
}

bool AddressSet::hasUnknownObject() const
{
    return allObjects_;
}

bool AddressSet::mayContainRawAddress() const
{
    return mayContainRawAddress_;
}

bool AddressSet::isFinite() const
{
    return !allObjects_ && !mayContainRawAddress_;
}

bool AddressSet::isSingleton() const
{
    return isFinite() && locations_.size() == 1;
}

bool AddressSet::contains(Location location) const
{
    return (allObjects_ && !location.isNull()) ||
           locations_.contains(location);
}

bool AddressSet::hasIntersection(const AddressSet& other) const
{
    if (isBottom() || other.isBottom())
        return false;
    if (mayContainRawAddress_ && other.mayContainRawAddress_)
        return true;
    if (allObjects_ && other.allObjects_)
        return true;
    if (allObjects_)
    {
        if (std::any_of(other.locations_.begin(), other.locations_.end(),
                        [](Location location)
    {
        return !location.isNull();
        }))
        return true;
    }
    if (other.allObjects_)
    {
        if (std::any_of(locations_.begin(), locations_.end(),
                        [](Location location)
    {
        return !location.isNull();
        }))
        return true;
    }
    const auto* smaller = &locations_;
    const auto* larger = &other.locations_;
    if (larger->size() < smaller->size())
        std::swap(smaller, larger);
    return std::any_of(smaller->begin(), smaller->end(), [&](Location location)
    {
        return larger->contains(location);
    });
}

std::size_t AddressSet::size() const
{
    if (allObjects_)
    {
        assert(false && "object-top address set has no finite size");
        std::abort();
    }
    return locations_.size();
}

bool AddressSet::empty() const
{
    return isBottom();
}

const FiniteLocationSet& AddressSet::locations() const
{
    if (allObjects_)
    {
        assert(false && "object-top address set has no finite enumeration");
        std::abort();
    }
    return locations_;
}

void AddressSet::insert(Location location)
{
    if (allObjects_ && !location.isNull())
        return;
    locations_.insert(location);
}

void AddressSet::joinWith(const AddressSet& other)
{
    if (other.isBottom())
        return;
    const bool includeNull = contains(Location::null()) ||
                             other.contains(Location::null());
    mayContainRawAddress_ =
        mayContainRawAddress_ || other.mayContainRawAddress_;
    if (allObjects_ || other.allObjects_)
    {
        allObjects_ = true;
        locations_.clear();
        if (includeNull)
            locations_.insert(Location::null());
        return;
    }
    if (locations_.storage() == AddressSetStorage::Hash ||
            other.locations_.storage() == AddressSetStorage::Hash ||
            (locations_.size() <= 2 && other.locations_.size() <= 2))
    {
        for (Location location : other.locations_)
            locations_.insert(location);
        return;
    }
    std::vector<Location> joined;
    joined.reserve(locations_.size() + other.locations_.size());
    std::set_union(locations_.begin(), locations_.end(),
                   other.locations_.begin(), other.locations_.end(),
                   std::back_inserter(joined));
    locations_.assign(std::move(joined));
}

void AddressSet::meetWith(const AddressSet& other)
{
    const bool raw = mayContainRawAddress_ &&
                     other.mayContainRawAddress_;
    const bool includeNull = contains(Location::null()) &&
                             other.contains(Location::null());
    const bool objects = allObjects_ && other.allObjects_;
    FiniteLocationSet intersection(locations_.storage());
    if (allObjects_ && !other.allObjects_)
    {
        for (Location location : other.locations_)
            if (!location.isNull())
                intersection.insert(location);
    }
    else if (!allObjects_ && other.allObjects_)
    {
        for (Location location : locations_)
            if (!location.isNull())
                intersection.insert(location);
    }
    else if (!allObjects_ && !other.allObjects_)
    {
        if (locations_.storage() == AddressSetStorage::Hash ||
            other.locations_.storage() == AddressSetStorage::Hash ||
            (locations_.size() <= 2 && other.locations_.size() <= 2))
        {
            for (Location location : locations_)
            {
                if (!location.isNull() &&
                        other.locations_.contains(location))
                    intersection.insert(location);
            }
        }
        else
        {
            std::vector<Location> common;
            common.reserve(
                std::min(locations_.size(), other.locations_.size()));
            std::set_intersection(locations_.begin(), locations_.end(),
                                  other.locations_.begin(),
                                  other.locations_.end(),
                                  std::back_inserter(common));
            common.erase(std::remove_if(common.begin(), common.end(),
                                        [](Location location)
            {
                return location.isNull();
            }), common.end());
            intersection.assign(std::move(common));
        }
    }
    if (includeNull)
        intersection.insert(Location::null());
    allObjects_ = objects;
    mayContainRawAddress_ = raw;
    locations_ = std::move(intersection);
}

bool AddressSet::isSubsetOf(const AddressSet& other) const
{
    if (mayContainRawAddress_ && !other.mayContainRawAddress_)
        return false;
    if (contains(Location::null()) && !other.contains(Location::null()))
        return false;
    if (allObjects_ && !other.allObjects_)
        return false;
    for (Location location : locations_)
    {
        if (!location.isNull() && !other.contains(location))
            return false;
    }
    return true;
}

std::string AddressSet::toString() const
{
    if (isTop())
        return "top";
    if (isObjectTop())
        return "object-top";
    if (isRawTop())
        return "raw-top";
    if (isBottom())
        return "bottom";
    if (allObjects_)
    {
        std::string result = mayContainRawAddress_
                             ? "raw+object-top"
                             : "object-top";
        if (contains(Location::null()))
            result += "+null";
        return result;
    }
    std::ostringstream output;
    output << (mayContainRawAddress_ ? "raw+{" : "{");
    bool first = true;
    std::vector<Location> sorted(locations_.begin(), locations_.end());
    std::sort(sorted.begin(), sorted.end());
    for (Location location : sorted)
    {
        if (!first)
            output << ",";
        first = false;
        if (location.isNull())
            output << "null";
        else
            output << location.id();
    }
    output << "}";
    return output.str();
}

void AddressSet::useStorage(AddressSetStorage storage)
{
    if (locations_.storage() == storage)
        return;
    FiniteLocationSet converted(storage);
    for (Location location : locations_)
        converted.insert(location);
    locations_ = std::move(converted);
}

AddressDomain AddressDomain::top(AddressSetStorage storage)
{
    return AddressDomain(false, storage);
}

AddressDomain AddressDomain::bottom(AddressSetStorage storage)
{
    return AddressDomain(true, storage);
}

AddressDomain AddressDomain::without(const std::set<Variable>& omitted) const
{
    if (bottom_ || omitted.empty())
        return *this;
    AddressDomain result = top(storage_);
    if (!paged_)
    {
        result.smallValues_ = smallValues_;
        result.size_ = size_;
        const auto& values = *smallValues_;
        const auto first = std::find_if(values.begin(), values.end(),
                                        [&](const auto& value)
        {
            return omitted.count(value.first);
        });
        if (first != values.end())
        {
            result.smallValues_ = std::make_shared<SmallValues>(
                                        values.begin(), first);
            for (auto it = first; it != values.end(); ++it)
                if (!omitted.count(it->first))
                    result.smallValues_->push_back(*it);
            result.size_ = result.smallValues_->size();
        }
    }
    else
    {
        result.paged_ = true;
        result.size_ = size_;
        result.pages_.reserve(pages_.size());
        for (const auto& entry : pages_)
        {
            std::shared_ptr<ValuePage> selected;
            for (std::size_t i = 0; i < ValuesPerPage; ++i)
            {
                const auto& slot = entry.page->values[i];
                if (slot && omitted.count(slot->variable))
                {
                    if (!selected)
                        selected = std::make_shared<ValuePage>(*entry.page);
                    selected->values[i].reset();
                    --result.size_;
                }
            }
            if (!selected)
                result.pages_.push_back(entry);
            else if (!pageIsEmpty(*selected))
                result.pages_.push_back({entry.index, std::move(selected)});
        }
    }

    return result;
}

std::unique_ptr<AbstractDomain> AddressDomain::clone() const
{
    return std::make_unique<AddressDomain>(*this);
}

AddressSet AddressDomain::addressSet(Variable variable) const
{
    if (bottom_)
        return AddressSet::bottom();
    const AddressSet* value = findValue(variable);
    return value ? *value : AddressSet::top();
}

std::vector<Variable> AddressDomain::nonDefaultVariables() const
{
    std::vector<Variable> variables;
    variables.reserve(size_);
    if (!paged_)
    {
        for (const auto& [variable, value] : *smallValues_)
        {
            (void)value;
            variables.push_back(variable);
        }
        return variables;
    }
    for (const ValuePageEntry& entry : pages_)
    {
        for (std::size_t slot = 0; slot < ValuesPerPage; ++slot)
        {
            if (entry.page->values[slot])
                variables.push_back(entry.page->values[slot]->variable);
        }
    }
    return variables;
}

std::vector<Variable> AddressDomain::nonDefaultVariablesBefore(
    Variable upperBound) const
{
    std::vector<Variable> variables;
    if (!paged_)
    {
        for (const auto& [variable, value] : *smallValues_)
        {
            (void)value;
            if (variable.id() >= upperBound.id())
                break;
            variables.push_back(variable);
        }
        return variables;
    }
    for (const ValuePageEntry& entry : pages_)
    {
        if (entry.index * ValuesPerPage >= upperBound.id())
            break;
        for (std::size_t slot = 0; slot < ValuesPerPage; ++slot)
        {
            if (!entry.page->values[slot])
                continue;
            const Variable variable = entry.page->values[slot]->variable;
            if (variable.id() < upperBound.id())
                variables.push_back(variable);
        }
    }
    return variables;
}

void AddressDomain::assign(Variable variable, AddressSet addresses)
{
    if (bottom_)
        return;
    if (addresses.isTop())
        eraseValue(variable);
    else
        storeValue(variable, std::move(addresses));
}

void AddressDomain::forget(Variable variable)
{
    assign(variable, AddressSet::top());
}

bool AddressDomain::hasCompatibleDomain(const AbstractDomain& other) const
{
    return other.isDomain<AddressDomain>();
}

void AddressDomain::joinDomain(const AbstractDomain& other)
{
    const AddressDomain& address = requireAddress(other);
    if (address.bottom_)
        return;
    if (bottom_)
    {
        if (storage_ == address.storage_)
            *this = address;
        else
        {
            bottom_ = false;
            for (Variable variable : address.nonDefaultVariables())
                assign(variable, address.addressSet(variable));
        }
        return;
    }
    AddressDomain result = top(storage_);
    for (Variable variable : nonDefaultVariables())
    {
        AddressSet joined = addressSet(variable);
        joined.joinWith(address.addressSet(variable));
        if (!joined.isTop())
            result.assign(variable, std::move(joined));
    }
    *this = std::move(result);
}

void AddressDomain::meetDomain(const AbstractDomain& other)
{
    const AddressDomain& address = requireAddress(other);
    if (bottom_ || address.bottom_)
    {
        makeBottom();
        return;
    }
    AddressDomain result = top(storage_);
    std::vector<Variable> variables = nonDefaultVariables();
    const std::vector<Variable> otherVariables = address.nonDefaultVariables();
    variables.insert(variables.end(), otherVariables.begin(),
                     otherVariables.end());
    std::sort(variables.begin(), variables.end());
    variables.erase(std::unique(variables.begin(), variables.end()),
                    variables.end());
    for (Variable variable : variables)
    {
        AddressSet value = addressSet(variable);
        value.meetWith(address.addressSet(variable));
        if (!value.isTop())
            result.assign(variable, std::move(value));
    }
    *this = std::move(result);
}

void AddressDomain::widenDomain(const AbstractDomain& next)
{
    joinDomain(next);
}

void AddressDomain::narrowDomain(const AbstractDomain& next)
{
    meetDomain(next);
}

bool AddressDomain::isBottomDomain() const
{
    return bottom_;
}

bool AddressDomain::isTopDomain() const
{
    return !bottom_ && size_ == 0;
}

bool AddressDomain::leqDomain(const AbstractDomain& other) const
{
    const AddressDomain& address = requireAddress(other);
    if (bottom_)
        return true;
    if (address.bottom_)
        return false;
    if (size_ < address.size_)
        return false;

    auto pairIsBelow = [&](const Value& right)
    {
        const AddressSet* left = findValue(right.first);
        return left && left->isSubsetOf(right.second);
    };

    if (!address.paged_)
        return std::all_of(address.smallValues_->begin(),
                           address.smallValues_->end(), pairIsBelow);

    if (!paged_)
        return false;

    std::size_t leftPage = 0;
    for (const ValuePageEntry& rightPage : address.pages_)
    {
        while (leftPage < pages_.size() &&
                pages_[leftPage].index < rightPage.index)
            ++leftPage;
        if (leftPage == pages_.size() ||
                pages_[leftPage].index != rightPage.index)
            return false;
        if (pages_[leftPage].page == rightPage.page)
            continue;
        for (std::size_t slot = 0; slot < ValuesPerPage; ++slot)
        {
            const std::optional<ValueSlot>& right =
                rightPage.page->values[slot];
            if (!right)
                continue;
            const std::optional<ValueSlot>& left =
                pages_[leftPage].page->values[slot];
            if (!left || left->variable != right->variable ||
                    !left->addresses.isSubsetOf(right->addresses))
                return false;
        }
    }
    return true;
}

std::string AddressDomain::domainToString() const
{
    std::ostringstream output;
    if (bottom_)
        return "bottom";
    output << "{";
    bool first = true;
    for (Variable variable : nonDefaultVariables())
    {
        if (!first)
            output << ", ";
        first = false;
        output << variable.id() << "=" << addressSet(variable).toString();
    }
    output << "}";
    return output.str();
}

const AddressDomain& AddressDomain::requireAddress(
    const AbstractDomain& other) const
{
    requireCompatible(other);
    return static_cast<const AddressDomain&>(other);
}

std::shared_ptr<AddressDomain::SmallValues> AddressDomain::emptySmallValues()
{
    static const std::shared_ptr<SmallValues> empty =
        std::make_shared<SmallValues>();
    return empty;
}

const AddressSet* AddressDomain::findValue(Variable variable) const
{
    if (!paged_)
    {
        const auto iterator = std::lower_bound(
                                  smallValues_->begin(), smallValues_->end(), variable,
                                  [](const Value& value, Variable key)
        {
            return value.first.id() < key.id();
        });
        if (iterator == smallValues_->end() ||
                iterator->first.id() != variable.id())
            return nullptr;
        if (iterator->first != variable)
        {
            assert(false && "Variable ID was reused with a different numeric type");
            std::abort();
        }
        return &iterator->second;
    }
    const std::size_t pageIndex = variable.id() / ValuesPerPage;
    const auto iterator = std::lower_bound(
                              pages_.begin(), pages_.end(), pageIndex,
                              [](const ValuePageEntry& entry, std::size_t index)
    {
        return entry.index < index;
    });
    if (iterator == pages_.end() || iterator->index != pageIndex)
        return nullptr;
    const std::optional<ValueSlot>& value =
        iterator->page->values[variable.id() % ValuesPerPage];
    if (!value)
        return nullptr;
    if (value->variable != variable)
    {
        assert(false && "Variable ID was reused with a different numeric type");
        std::abort();
    }
    return &value->addresses;
}

void AddressDomain::storeValue(Variable variable, AddressSet addresses)
{
    addresses.useStorage(storage_);
    if (!paged_)
    {
        SmallValues& values = writableSmallValues();
        auto iterator = std::lower_bound(
                            values.begin(), values.end(), variable,
                            [](const Value& value, Variable key)
        {
            return value.first.id() < key.id();
        });
        if (iterator != values.end() &&
                iterator->first.id() == variable.id())
        {
            if (iterator->first != variable)
            {
                assert(false && "Variable ID was reused with a different numeric type");
                std::abort();
            }
            iterator->second = std::move(addresses);
            return;
        }
        values.insert(iterator, Value(variable, std::move(addresses)));
        ++size_;
        if (size_ > SmallThreshold)
            promoteToPages();
        return;
    }
    std::optional<ValueSlot>& slot =
        writablePage(variable.id() / ValuesPerPage)
        .values[variable.id() % ValuesPerPage];
    if (!slot)
        ++size_;
    else if (slot->variable != variable)
    {
        assert(false && "Variable ID was reused with a different numeric type");
        std::abort();
    }
    slot = ValueSlot{variable, std::move(addresses)};
}

void AddressDomain::eraseValue(Variable variable)
{
    if (!paged_)
    {
        SmallValues& values = writableSmallValues();
        const auto iterator = std::lower_bound(
                                  values.begin(), values.end(), variable,
                                  [](const Value& value, Variable key)
        {
            return value.first.id() < key.id();
        });
        if (iterator != values.end() &&
                iterator->first.id() == variable.id())
        {
            if (iterator->first != variable)
            {
                assert(false && "Variable ID was reused with a different numeric type");
                std::abort();
            }
            values.erase(iterator);
            --size_;
        }
        return;
    }
    const std::size_t pageIndex = variable.id() / ValuesPerPage;
    auto iterator = std::lower_bound(
                        pages_.begin(), pages_.end(), pageIndex,
                        [](const ValuePageEntry& entry, std::size_t index)
    {
        return entry.index < index;
    });
    if (iterator == pages_.end() || iterator->index != pageIndex)
        return;
    if (iterator->page.use_count() != 1)
        iterator->page = std::make_shared<ValuePage>(*iterator->page);
    std::optional<ValueSlot>& slot =
        iterator->page->values[variable.id() % ValuesPerPage];
    if (!slot)
        return;
    if (slot->variable != variable)
    {
        assert(false && "Variable ID was reused with a different numeric type");
        std::abort();
    }
    slot.reset();
    --size_;
    if (pageIsEmpty(*iterator->page))
        pages_.erase(iterator);
}

void AddressDomain::promoteToPages()
{
    if (paged_)
        return;
    const SmallValues values = *smallValues_;
    paged_ = true;
    size_ = 0;
    smallValues_ = emptySmallValues();
    for (const auto& [variable, addresses] : values)
        storeValue(variable, addresses);
}

AddressDomain::SmallValues& AddressDomain::writableSmallValues()
{
    if (smallValues_.use_count() != 1)
        smallValues_ = std::make_shared<SmallValues>(*smallValues_);
    return *smallValues_;
}

AddressDomain::ValuePage& AddressDomain::writablePage(std::size_t pageIndex)
{
    auto iterator = std::lower_bound(
                        pages_.begin(), pages_.end(), pageIndex,
                        [](const ValuePageEntry& entry, std::size_t index)
    {
        return entry.index < index;
    });
    if (iterator == pages_.end() || iterator->index != pageIndex)
        iterator = pages_.insert(
                       iterator, {pageIndex, std::make_shared<ValuePage>()});
    else if (iterator->page.use_count() != 1)
        iterator->page = std::make_shared<ValuePage>(*iterator->page);
    return *iterator->page;
}

bool AddressDomain::pageIsEmpty(const ValuePage& page)
{
    return std::none_of(page.values.begin(), page.values.end(),
                        [](const std::optional<ValueSlot>& value)
    {
        return value.has_value();
    });
}

void AddressDomain::makeBottom()
{
    bottom_ = true;
    paged_ = false;
    size_ = 0;
    smallValues_ = emptySmallValues();
    pages_.clear();
}

} // namespace SVF
