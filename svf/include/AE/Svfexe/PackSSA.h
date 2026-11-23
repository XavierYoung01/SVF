//===- PackSSA.h -- Function-local SSA for numerical packs -----------------===//
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
//===----------------------------------------------------------------------===//

#ifndef INCLUDE_AE_SVFEXE_PACKSSA_H_
#define INCLUDE_AE_SVFEXE_PACKSSA_H_

#include "Graphs/ICFG.h"
#include <cstddef>
#include <iosfwd>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <vector>

namespace SVF
{

/// Versions describe storage and dependencies; the ICFG interpreter owns values.
class PackSSA
{
public:
    using PackID = std::size_t;
    using VersionID = std::size_t;
    using PackSet = std::set<PackID>;
    using Routes = std::map<PackID, VersionID>;
    using NodeDefinitions = std::map<const ICFGNode*, PackSet>;
    using EdgeDefinitions = std::map<const IntraCFGEdge*, PackSet>;
    static constexpr VersionID InvalidVersion =
        std::numeric_limits<VersionID>::max();

    enum class Kind
    {
        Root, FormalIn, ActualOut, Phi, Statement, Edge
    };

    struct Operand
    {
        VersionID version;
        const ICFGNode* predecessor;
        const IntraCFGEdge* edge;
        std::size_t block;
    };

    struct Version
    {
        VersionID id;
        PackID pack;
        Kind kind;
        const ICFGNode* node;
        const IntraCFGEdge* edge;
        std::vector<Operand> operands;
        std::size_t block;
    };

    /// ActualIN and FormalOUT are uses of source; the destination is a definition.
    struct Connection
    {
        const ICFGEdge* edge;
        PackID pack;
        VersionID source;
        VersionID target;
    };

    PackSSA(const ICFG& graph, const PackSet& packs,
            const NodeDefinitions& nodes, const EdgeDefinitions& edges);
    ~PackSSA();
    PackSSA(const PackSSA&) = delete;
    PackSSA& operator=(const PackSSA&) = delete;

    const Routes& before(const ICFGNode* node) const;
    const Routes& after(const ICFGNode* node) const;
    const Routes& onEdge(const IntraCFGEdge* edge) const;
    const Routes& inputDefinitions(const ICFGNode* node) const;
    const Routes& outputDefinitions(const ICFGNode* node) const;
    const Routes& edgeDefinitions(const IntraCFGEdge* edge) const;
    const std::vector<Version>& versions() const;
    const std::vector<Connection>& connections() const;
    /// Removing dominance backedges must leave each local CFG acyclic.
    bool hasReducibleControlFlow() const;
    void verify() const;
    void dump(std::ostream& out) const;

private:
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

} // namespace SVF

#endif
