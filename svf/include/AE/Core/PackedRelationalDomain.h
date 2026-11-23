//===- PackedRelationalDomain.h -- Packed Relational Domain --------===//
//
//                     SVF: Static Value-Flow Analysis
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
//===----------------------------------------------------------------------===//

// SPDX-License-Identifier: AGPL-3.0-or-later
#ifndef SVF_AE_PACKED_RELATIONAL_DOMAIN_H
#define SVF_AE_PACKED_RELATIONAL_DOMAIN_H
#include "AE/Core/OctagonDomain.h"
#include <functional>
#include <set>
#include <map>
namespace SVF
{
// Stable logical packs with extensible coordinates and a global Box fallback
// for values whose numerical ownership is outside the relational schema.
// This does not select/change the fixpoint executor.
class PackedRelationalDomain final : public NumericalDomain
{
public:
    using Packing = std::vector<std::vector<Variable>>;
    using NumericalDomain::bound;
    using NumericalDomain::assignParallel;
    using NumericalDomain::substitute;
    using NumericalDomain::substituteParallel;
    explicit PackedRelationalDomain(std::shared_ptr<const Packing>, bool bottom = false);
    /// Extend an existing logical pack without changing its SSA identity.
    static void registerVariable(const std::shared_ptr<const Packing>&,
                                 std::size_t logical, Variable);
    const std::vector<Variable>& packVariables(std::size_t logical) const;
    DomainKind kind() const noexcept override
    {
        return DomainKind::Octagon;
    }
    std::unique_ptr<AbstractDomain> clone() const override;
    void assign(Variable, const LinearExpression&) override;
    void assign(Variable, const TreeExpression&) override;
    void assignParallel(const LinearAssignmentList&) override;
    void substitute(Variable, const LinearExpression&) override;
    void substituteParallel(const LinearAssignmentList&) override;
    void assume(const LinearConstraint&) override;
    void assume(const TreeConstraint&) override;
    void assumeAll(const LinearConstraintSet&) override;
    void forget(Variable) override;
    void project(const std::vector<Variable>&) override;
    void expand(Variable, const std::vector<Variable>&) override;
    void fold(Variable, const std::vector<Variable>&) override;
    CheckResult entails(const LinearConstraint&) const override;
    Interval bound(Variable) const override;
    Interval bound(const LinearExpression&) const override;
    std::vector<Variable> supportVariables() const override;
    LinearConstraintSet toConstraints() const override;
    void close() override;
    void canonicalize() override;
    // Executor storage boundary: a pack is an indivisible abstract location.
    // Logical singleton packs live in box_; physical indices are schema-only.
    const OctagonDomain& packState(std::size_t logical) const;
    bool isRelationalPack(std::size_t logical) const;
    std::size_t materializedPackCount() const
    {
        return packs_.size();
    }
    const std::vector<std::size_t>& relationalPackIndices() const;
    bool ownsNumerical(Variable v) const
    {
        return layout_->owners.count(v) != 0;
    }
    const BoxDomain& fallbackState() const
    {
        return box_;
    }
    // Legacy snapshots contain one Octagon per logical pack; singleton bounds
    // are restored into Box. Packed numerical coordinates remain in Octagon.
    void restoreComponents(BoxDomain fallback, std::vector<OctagonDomain> packs);
    void restoreRelationalComponents(BoxDomain fallback, std::vector<OctagonDomain> packs);
private:
    const void* dynamicTypeToken() const noexcept override
    {
        return staticTypeToken<PackedRelationalDomain>();
    }
    bool hasCompatibleDomain(const AbstractDomain&) const override;
    void joinDomain(const AbstractDomain&) override;
    void meetDomain(const AbstractDomain&) override;
    void widenDomain(const AbstractDomain&) override;
    void narrowDomain(const AbstractDomain&) override;
    bool isBottomDomain() const override;
    bool isTopDomain() const override;
    bool leqDomain(const AbstractDomain&) const override;
    std::string domainToString() const override;
    std::vector<Variable> relationalClosureState(const std::vector<Variable>&) const override;
    bool contains(std::size_t, Variable) const;
    bool usesFallback(Variable) const;
    struct Layout
    {
        std::vector<std::size_t> logicalToPhysical, physicalToLogical;
        std::map<Variable,std::vector<std::size_t>> owners;
        std::set<Variable> singletons;
        std::vector<std::vector<Variable>> variables;
    };
    static std::shared_ptr<Layout> layoutFor(const std::shared_ptr<const Packing>&);
    template <class Operation>
    void updateFallback(BoxDomain& next, const std::set<Variable>& targets,
                        const std::set<Variable>& reads,
                        Operation operation) const;
    void normalizeBottom();
    void importOutside(OctagonDomain&, std::size_t, const std::set<Variable>&) const;
    void update(const std::set<Variable>& targets, const std::set<Variable>& reads,
                const std::function<void(OctagonDomain&, std::size_t)>& operation);
    std::shared_ptr<const Packing> packing_;
    std::shared_ptr<const Layout> layout_;
    BoxDomain box_;
    std::vector<OctagonDomain> packs_;
};
}
#endif
