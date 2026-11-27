//===- BoxDomain.h -- Interval box domain -----------------------*- C++ -*-===//
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

#ifndef SVF_AE_BOX_DOMAIN_H
#define SVF_AE_BOX_DOMAIN_H

#include "AE/Core/NumericalDomain.h"

#include <algorithm>
#include <array>
#include <memory>
#include <optional>
#include <set>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace SVF
{

enum class BoxStorage
{
    Hash = 0,
    Page1 = 1,
    Page2 = 2,
    Page4 = 4,
    Page8 = 8,
    Page16 = 16
};

struct BoxStorageConfig
{
    BoxStorage values = BoxStorage::Page8;
    BoxStorage objectContents = BoxStorage::Page8;
};

struct BoxSemanticConfig
{
    bool integerTightening = true;
    std::shared_ptr<DiagnosticSink> diagnostics;
    BoxStorageConfig storage;

    bool operationCompatible(const BoxSemanticConfig& other) const
    {
        return integerTightening == other.integerTightening;
    }
};

/// Non-relational numerical property with finite non-Top support over stable
/// typed Variables. Variable IDs are the global sparse page coordinates.
class BoxDomain final : public NumericalDomain
{
    friend class BoxAddressDomain;

public:
    using NumericalDomain::assignParallel;
    using NumericalDomain::bound;
    using NumericalDomain::substitute;
    using NumericalDomain::substituteParallel;

    static BoxDomain top(const BoxSemanticConfig& config = {});
    static BoxDomain bottom(const BoxSemanticConfig& config = {});
    static BoxDomain fromConstraints(const LinearConstraintSet& constraints,
                                     const BoxSemanticConfig& config = {});

    BoxDomain(const BoxDomain& other);
    BoxDomain(BoxDomain&& other) noexcept = default;
    BoxDomain& operator=(const BoxDomain& other) = default;
    BoxDomain& operator=(BoxDomain&& other) noexcept = default;

    DomainKind kind() const noexcept override
    {
        return DomainKind::Box;
    }
    std::unique_ptr<AbstractDomain> clone() const override;
    const BoxSemanticConfig& config() const
    {
        return config_;
    }

    void assign(Variable target, const LinearExpression& expression) override;
    void assign(Variable target, const TreeExpression& expression) override;
    void assignParallel(const LinearAssignmentList& assignments) override;
    void substitute(Variable target,
                    const LinearExpression& expression) override;
    void substituteParallel(const LinearAssignmentList& assignments) override;
    void assume(const LinearConstraint& constraint) override;
    void assume(const TreeConstraint& constraint) override;
    void assumeAll(const LinearConstraintSet& constraints) override;
    void forget(Variable variable) override;
    void project(const std::vector<Variable>& retained) override;
    void expand(Variable source, const std::vector<Variable>& copies) override;
    void fold(Variable target, const std::vector<Variable>& folded) override;

    CheckResult entails(const LinearConstraint& constraint) const override;
    Interval bound(Variable variable) const override;
    Interval bound(const LinearExpression& expression) const override;
    /// Variables whose bounds are represented explicitly because they are
    /// stricter than the analysis-wide Top default. This is a storage
    /// observation for sparse scheduling; absence never means undefined.
    std::vector<Variable> constrainedVariables() const;
    std::vector<Variable> constrainedVariablesBefore(
        Variable upperBound) const;
    std::vector<Variable> supportVariables() const override
    {
        return constrainedVariables();
    }
    LinearConstraintSet toConstraints() const override;
    void close() override;
    void canonicalize() override;

    BoxDomain join(const BoxDomain& other) const;
    BoxDomain meet(const BoxDomain& other) const;
    BoxDomain widen(const BoxDomain& next) const;
    BoxDomain widen(const BoxDomain& next, const WideningPolicy& policy) const;
    BoxDomain narrow(const BoxDomain& next) const;

private:
    struct BoundSlot
    {
        Variable variable;
        Interval interval;

        friend bool operator==(const BoundSlot& lhs, const BoundSlot& rhs)
        {
            return lhs.variable == rhs.variable && lhs.interval == rhs.interval;
        }
    };

    class BoundStore
    {
        using Slot = std::optional<BoundSlot>;
        using Page = std::shared_ptr<Slot>;
        struct PageEntry
        {
            std::size_t index;
            Page page;
        };
        using Hash = std::unordered_map<std::uint32_t, BoundSlot>;
        using Directory = std::vector<PageEntry>;

        template <typename Pages>
        static auto findPage(Pages& pages, std::size_t index)
        {
            return std::lower_bound(pages.begin(), pages.end(), index,
                                    [](const PageEntry& entry, std::size_t key)
            {
                return entry.index < key;
            });
        }

        template <std::size_t Width>
        static Page allocatePage()
        {
            auto slots = std::make_shared<std::array<Slot, Width>>();
            return Page(slots, slots->data());
        }

        Page newPage() const;
        void detach(Page& page) const;
        bool emptyPage(const Page& page) const;

        std::uint32_t width_;
        std::variant<Hash, Directory> storage_;

    public:
        explicit BoundStore(BoxStorage storage);
        const BoundSlot* find(std::uint32_t id) const;
        void assign(BoundSlot slot);
        void erase(Variable variable);
        void join(const BoundStore& other);
        bool equalPages(const BoundStore& other) const;
        void clear();
        bool empty() const;
        BoundStore without(const std::set<Variable>& omitted) const;

        template <typename Visitor>
        bool forEach(Visitor visit) const
        {
            if (const auto* hash = std::get_if<Hash>(&storage_))
            {
                for (const auto& item : *hash)
                    if (!visit(item.second))
                        return false;
            }
            else
            {
                for (const auto& entry : std::get<Directory>(storage_))
                    for (std::size_t i = 0; i < width_; ++i)
                    {
                        const auto& slot = entry.page.get()[i];
                        if (slot && !visit(*slot))
                            return false;
                    }
            }
            return true;
        }
    };

    BoxDomain(BoxSemanticConfig config, bool bottom);

    const void* dynamicTypeToken() const noexcept override
    {
        return staticTypeToken<BoxDomain>();
    }
    bool hasCompatibleDomain(const AbstractDomain& other) const override;
    void joinDomain(const AbstractDomain& other) override;
    void meetDomain(const AbstractDomain& other) override;
    void widenDomain(const AbstractDomain& next) override;
    void narrowDomain(const AbstractDomain& next) override;
    bool isBottomDomain() const override;
    bool isTopDomain() const override;
    bool leqDomain(const AbstractDomain& other) const override;
    std::string domainToString() const override;

    const BoxDomain& requireBox(const AbstractDomain& other) const;
    const Interval& boundAt(Variable variable) const;
    void storeBound(Variable variable, Interval interval);
    void eraseBound(Variable variable);
    BoundStore& storeFor(Variable variable);
    const BoundStore& storeFor(Variable variable) const;
    BoxDomain withoutBounds(const std::set<Variable>& omitted) const;
    std::vector<Variable> boundedVariables() const;
    std::vector<Variable> boundedVariablesBefore(
        Variable upperBound) const;
    void makeBottom();
    void canonicalize(Variable variable);
    void assignInterval(Variable target, const Interval& value) override;
    void setBound(Variable variable, Interval interval);
    void report(OperationKind operation, ApproximationKind approximation,
                std::string reason, bool best = true) const;
    BoxSemanticConfig config_;
    BoundStore values_;
    BoundStore objectContents_;
    bool bottom_ = false;
};

} // namespace SVF

#endif // SVF_AE_BOX_DOMAIN_H
