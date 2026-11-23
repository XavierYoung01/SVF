//===- PackSSA.cpp -- Function-local SSA for numerical packs ---------------===//
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

#include "AE/Svfexe/PackSSA.h"
#include "SVFIR/SVFVariables.h"
#include <algorithm>
#include <deque>
#include <ostream>
#include <stdexcept>
#include <string>
#include <utility>

using namespace SVF;

struct PackSSA::Impl
{
    static constexpr std::size_t Invalid = PackSSA::InvalidVersion;

    struct Block
    {
        std::size_t id;
        const FunObjVar* function;
        const ICFGNode* node;
        const IntraCFGEdge* edge;
        std::string role;
        std::vector<std::size_t> incoming, outgoing;
        Routes input, output, before, after;
    };

    struct Arc
    {
        std::size_t source, target;
        const IntraCFGEdge* original;
        std::string kind;
    };

    const ICFG& graph;
    PackSet packs;
    NodeDefinitions nodeWrites;
    EdgeDefinitions edgeWrites;
    std::vector<Block> blocks;
    std::vector<Arc> arcs;
    std::map<const ICFGNode*, std::size_t> nodeBlocks;
    std::map<const IntraCFGEdge*, std::size_t> edgeBlocks;
    std::map<const IntraCFGEdge*, Routes> edgeRoutes;
    std::map<std::size_t, std::vector<std::size_t>> groups;
    std::vector<std::size_t> roots, idom, order, enter, leave;
    std::vector<std::vector<std::size_t>> children;
    std::vector<std::set<std::size_t>> frontiers;
    std::vector<Version> versions;
    std::vector<Connection> connections;

    Impl(const ICFG& cfg, const PackSet& ps, const NodeDefinitions& nw,
         const EdgeDefinitions& ew) : graph(cfg), packs(ps), nodeWrites(nw),
        edgeWrites(ew)
    {
        buildGraph();
        buildDominance();
        placeDefinitions();
        rename();
        connect();
    }

    static std::size_t group(const FunObjVar* function)
    {
        return function ? static_cast<std::size_t>(function->getId()) + 1 : 0;
    }

    std::size_t addBlock(const FunObjVar* function, const ICFGNode* node,
                         const IntraCFGEdge* edge, const std::string& role)
    {
        const auto id = blocks.size();
        blocks.push_back({id, function, node, edge, role, {}, {}, {}, {}, {}, {}});
        groups[group(function)].push_back(id);
        return id;
    }

    void addArc(std::size_t source, std::size_t target,
                const IntraCFGEdge* original, const std::string& kind)
    {
        const auto id = arcs.size();
        arcs.push_back({source, target, original, kind});
        blocks[source].outgoing.push_back(id);
        blocks[target].incoming.push_back(id);
    }

    void markReachable(std::size_t start, std::set<std::size_t>& seen) const
    {
        std::vector<std::size_t> work{start};
        while (!work.empty())
        {
            const auto block = work.back();
            work.pop_back();
            if (!seen.insert(block).second) continue;
            for (auto arc : blocks[block].outgoing)
                work.push_back(arcs[arc].target);
        }
    }

    void buildGraph()
    {
        for (auto it = graph.begin(); it != graph.end(); ++it)
        {
            const auto* node = it->second;
            const std::string role = SVFUtil::isa<FunEntryICFGNode>(node) ? "formal-in" :
                                     SVFUtil::isa<RetICFGNode>(node) ? "actual-out" :
                                     SVFUtil::isa<GlobalICFGNode>(node) ? "global" : "normal";
            nodeBlocks.emplace(node, addBlock(node->getFun(), node, nullptr, role));
        }
        for (auto it = graph.begin(); it != graph.end(); ++it)
        {
            const auto* node = it->second;
            for (const auto* base : node->getOutEdges())
            {
                const auto* edge = SVFUtil::dyn_cast<IntraCFGEdge>(base);
                if (!edge || edge->getSrcNode()->getFun() != edge->getDstNode()->getFun())
                    continue;
                const auto source = nodeBlocks.at(edge->getSrcNode());
                const auto target = nodeBlocks.at(edge->getDstNode());
                const auto write = edgeWrites.find(edge);
                if (edge->getCondition() || (write != edgeWrites.end() && !write->second.empty()))
                {
                    const auto middle = addBlock(node->getFun(), nullptr, edge, "edge");
                    edgeBlocks.emplace(edge, middle);
                    addArc(source, middle, edge, "edge-enter");
                    addArc(middle, target, edge, "edge-leave");
                }
                else
                {
                    const auto* call = SVFUtil::dyn_cast<CallICFGNode>(node);
                    const bool summary = call && call->getRetICFGNode() == edge->getDstNode();
                    addArc(source, target, edge, summary ? "summary" : "intra");
                }
            }
        }
        for (auto it = graph.begin(); it != graph.end(); ++it)
        {
            const auto* call = SVFUtil::dyn_cast<CallICFGNode>(it->second);
            if (!call || !call->getRetICFGNode()) continue;
            const auto source = nodeBlocks.at(call);
            const auto target = nodeBlocks.at(call->getRetICFGNode());
            bool present = false;
            for (const auto* base : call->getOutEdges())
                if (SVFUtil::isa<IntraCFGEdge>(base) && base->getDstNode() == call->getRetICFGNode())
                    present = true;
            if (!present) addArc(source, target, nullptr, "summary");
        }
        // Synthetic seeds do not introduce executable ICFG edges.
        for (auto& entry : groups)
        {
            const auto members = entry.second;
            const auto root = addBlock(blocks[members.front()].function, nullptr, nullptr, "super");
            roots.push_back(root);
            std::set<std::size_t> seen;
            for (auto block : members)
                if (blocks[block].role == "formal-in" || blocks[block].role == "global")
                {
                    addArc(root, block, nullptr, "seed");
                    markReachable(block, seen);
                }
            for (auto block : members)
                if (blocks[block].node && !seen.count(block))
                {
                    if (blocks[block].role == "normal") blocks[block].role = "disconnected";
                    addArc(root, block, nullptr, "seed");
                    markReachable(block, seen);
                }
        }
    }

    void buildDominance()
    {
        idom.assign(blocks.size(), Invalid);
        order.assign(blocks.size(), Invalid);
        children.resize(blocks.size());
        frontiers.resize(blocks.size());
        for (auto root : roots)
        {
            std::vector<std::size_t> post;
            std::set<std::size_t> seen{root};
            std::vector<std::pair<std::size_t, std::size_t>> stack{{root, 0}};
            while (!stack.empty())
            {
                auto& frame = stack.back();
                if (frame.second == blocks[frame.first].outgoing.size())
                {
                    post.push_back(frame.first);
                    stack.pop_back();
                    continue;
                }
                const auto next = arcs[blocks[frame.first].outgoing[frame.second++]].target;
                if (seen.insert(next).second) stack.emplace_back(next, 0);
            }
            std::reverse(post.begin(), post.end());
            for (std::size_t i = 0; i < post.size(); ++i) order[post[i]] = i;
            idom[root] = root;
            bool changed = true;
            while (changed)
            {
                changed = false;
                for (auto block : post)
                {
                    if (block == root) continue;
                    auto parent = Invalid;
                    for (auto arc : blocks[block].incoming)
                    {
                        auto pred = arcs[arc].source;
                        if (idom[pred] == Invalid) continue;
                        if (parent == Invalid) parent = pred;
                        else
                        {
                            auto left = parent;
                            auto right = pred;
                            while (left != right)
                            {
                                while (order[left] > order[right]) left = idom[left];
                                while (order[right] > order[left]) right = idom[right];
                            }
                            parent = left;
                        }
                    }
                    if (parent != Invalid && idom[block] != parent)
                    {
                        idom[block] = parent;
                        changed = true;
                    }
                }
            }
        }
        for (const auto& block : blocks)
        {
            if (idom[block.id] == Invalid) throw std::logic_error("PackSSA: unrooted local block");
            if (idom[block.id] != block.id) children[idom[block.id]].push_back(block.id);
            if (block.incoming.size() < 2) continue;
            for (auto arc : block.incoming)
            {
                auto runner = arcs[arc].source;
                while (runner != idom[block.id])
                {
                    frontiers[runner].insert(block.id);
                    if (idom[runner] == runner) break;
                    runner = idom[runner];
                }
            }
        }
        enter.resize(blocks.size());
        leave.resize(blocks.size());
        std::size_t clock = 0;
        for (auto root : roots)
        {
            std::vector<std::pair<std::size_t, bool>> work{{root, false}};
            while (!work.empty())
            {
                const auto event = work.back();
                work.pop_back();
                if (event.second) leave[event.first] = clock++;
                else
                {
                    enter[event.first] = clock++;
                    work.emplace_back(event.first, true);
                    for (auto child : children[event.first]) work.emplace_back(child, false);
                }
            }
        }
    }

    VersionID define(std::size_t block, PackID pack, Kind kind)
    {
        if (!packs.count(pack)) throw std::logic_error("PackSSA: unknown pack in write set");
        const auto& b = blocks[block];
        const auto id = versions.size();
        const ICFGNode* node = b.node ? b.node : b.edge ? b.edge->getSrcNode() : nullptr;
        versions.push_back({id, pack, kind, node, b.edge, {}, block});
        return id;
    }

    void placeDefinitions()
    {
        for (auto& block : blocks)
        {
            if (block.role == "super") continue;
            const bool boundary = block.role == "formal-in" || block.role == "actual-out" ||
                                  block.role == "global" || block.role == "disconnected";
            if (boundary)
            {
                const auto kind = block.role == "formal-in" ? Kind::FormalIn :
                                  block.role == "actual-out" ? Kind::ActualOut : Kind::Root;
                for (auto pack : packs) block.input.emplace(pack, define(block.id, pack, kind));
            }
            if (block.node)
            {
                const auto found = nodeWrites.find(block.node);
                if (found != nodeWrites.end())
                    for (auto pack : found->second)
                        block.output.emplace(pack, define(block.id, pack, Kind::Statement));
            }
            if (block.edge)
            {
                const auto found = edgeWrites.find(block.edge);
                if (found != edgeWrites.end())
                    for (auto pack : found->second)
                        block.output.emplace(pack, define(block.id, pack, Kind::Edge));
            }
        }
        for (auto pack : packs)
        {
            std::deque<std::size_t> work;
            std::set<std::size_t> queued;
            for (const auto& block : blocks)
                if (block.input.count(pack) || block.output.count(pack))
                {
                    queued.insert(block.id);
                    work.push_back(block.id);
                }
            while (!work.empty())
            {
                const auto block = work.front();
                work.pop_front();
                for (auto join : frontiers[block])
                {
                    if (blocks[join].input.count(pack)) continue;
                    blocks[join].input.emplace(pack, define(join, pack, Kind::Phi));
                    if (queued.insert(join).second) work.push_back(join);
                }
            }
        }
    }

    void rename()
    {
        std::map<PackID, std::vector<VersionID>> stacks;
        for (auto root : roots)
        {
            std::vector<std::pair<std::size_t, bool>> work{{root, false}};
            while (!work.empty())
            {
                const auto event = work.back();
                work.pop_back();
                auto& block = blocks[event.first];
                if (event.second)
                {
                    for (const auto& def : block.output) stacks.at(def.first).pop_back();
                    for (const auto& def : block.input) stacks.at(def.first).pop_back();
                    continue;
                }
                for (const auto& def : block.input) stacks[def.first].push_back(def.second);
                if (block.role != "super")
                    for (auto pack : packs)
                    {
                        if (stacks[pack].empty()) throw std::logic_error("PackSSA: missing incoming definition");
                        block.before.emplace(pack, stacks[pack].back());
                    }
                for (const auto& def : block.output) stacks[def.first].push_back(def.second);
                if (block.role != "super")
                    for (auto pack : packs) block.after.emplace(pack, stacks[pack].back());
                for (auto arcID : block.outgoing)
                {
                    const auto& arc = arcs[arcID];
                    for (const auto& def : blocks[arc.target].input)
                    {
                        auto& version = versions[def.second];
                        if (version.kind != Kind::Phi) continue;
                        if (stacks[def.first].empty()) throw std::logic_error("PackSSA: undefined phi operand");
                        const auto* predecessor = block.node ? block.node :
                                                  block.edge ? block.edge->getSrcNode() : nullptr;
                        version.operands.push_back({stacks[def.first].back(), predecessor,
                                                    arc.original, block.id});
                    }
                }
                work.emplace_back(block.id, true);
                for (auto child : children[block.id]) work.emplace_back(child, false);
            }
        }
        for (auto& version : versions)
            std::sort(version.operands.begin(), version.operands.end(),
                      [](const Operand& a, const Operand& b) { return a.block < b.block; });
    }

    void connect()
    {
        for (auto it = graph.begin(); it != graph.end(); ++it)
            for (const auto* edge : it->second->getOutEdges())
            {
                const auto& source = blocks[nodeBlocks.at(edge->getSrcNode())];
                const auto& target = blocks[nodeBlocks.at(edge->getDstNode())];
                if (const auto* intra = SVFUtil::dyn_cast<IntraCFGEdge>(edge))
                {
                    const auto middle = edgeBlocks.find(intra);
                    edgeRoutes.emplace(intra, middle == edgeBlocks.end() ? source.after : blocks[middle->second].after);
                }
                else if (SVFUtil::isa<CallCFGEdge>(edge) || SVFUtil::isa<RetCFGEdge>(edge))
                    for (auto pack : packs)
                        connections.push_back({edge, pack, source.after.at(pack), target.input.at(pack)});
            }
    }

    bool dominates(std::size_t definition, std::size_t use) const
    {
        return enter[definition] <= enter[use] && leave[use] <= leave[definition];
    }

    static const char* kindName(Kind kind)
    {
        switch (kind)
        {
        case Kind::Root: return "root";
        case Kind::FormalIn: return "formal-in";
        case Kind::ActualOut: return "actual-out";
        case Kind::Phi: return "phi";
        case Kind::Statement: return "statement";
        case Kind::Edge: return "edge";
        }
        throw std::logic_error("PackSSA: invalid definition kind");
    }

    void verify() const;
    void dump(std::ostream& out) const;
};

void PackSSA::Impl::verify() const
{
    auto require = [](bool valid, const char* message)
    {
        if (!valid) throw std::logic_error(message);
    };
    auto reference = [&](VersionID version, PackID pack, std::size_t use)
    {
        require(version < versions.size(), "PackSSA: invalid version reference");
        require(versions[version].pack == pack, "PackSSA: reference changes pack");
        require(dominates(versions[version].block, use), "PackSSA: definition does not dominate use");
    };
    for (const auto& block : blocks)
    {
        if (block.role == "super") continue;
        require(block.before.size() == packs.size() && block.after.size() == packs.size(),
                "PackSSA: incomplete pack routes");
        for (auto pack : packs)
        {
            const auto before = block.before.at(pack);
            const auto after = block.after.at(pack);
            reference(before, pack, block.id);
            reference(after, pack, block.id);
            const auto& def = versions[before];
            require(def.block != block.id || (def.kind != Kind::Statement && def.kind != Kind::Edge),
                    "PackSSA: pre-state refers to local post-definition");
            const auto local = block.output.find(pack);
            require(after == (local == block.output.end() ? before : local->second),
                    "PackSSA: post-state disagrees with local definitions");
            const auto input = block.input.find(pack);
            if (input != block.input.end())
                require(input->second == before, "PackSSA: incoming definition not used");
        }
    }
    for (const auto& version : versions)
    {
        require(version.id < versions.size() && &versions[version.id] == &version,
                "PackSSA: inconsistent version ID");
        if (version.kind != Kind::Phi)
        {
            require(version.operands.empty(), "PackSSA: unexpected phi operands");
            continue;
        }
        const auto& block = blocks[version.block];
        require(version.operands.size() == block.incoming.size(), "PackSSA: incomplete phi operands");
        std::multiset<std::size_t> expected, actual;
        for (auto arc : block.incoming) expected.insert(arcs[arc].source);
        for (const auto& operand : version.operands)
        {
            actual.insert(operand.block);
            reference(operand.version, version.pack, operand.block);
            require(blocks[operand.block].after.at(version.pack) == operand.version,
                    "PackSSA: phi operand is not predecessor output");
        }
        require(expected == actual, "PackSSA: phi predecessor mismatch");
    }
    for (const auto& declared : nodeWrites)
    {
        const auto found = nodeBlocks.find(declared.first);
        require(found != nodeBlocks.end(), "PackSSA: write on unknown node");
        for (auto pack : declared.second)
            require(blocks[found->second].output.count(pack), "PackSSA: missing statement definition");
    }
    for (const auto& declared : edgeWrites)
    {
        if (declared.second.empty()) continue;
        const auto found = edgeBlocks.find(declared.first);
        require(found != edgeBlocks.end(), "PackSSA: write on nonlocal edge");
        for (auto pack : declared.second)
            require(blocks[found->second].output.count(pack), "PackSSA: missing edge definition");
    }
    for (const auto& connection : connections)
    {
        const auto& source = blocks[nodeBlocks.at(connection.edge->getSrcNode())];
        const auto& target = blocks[nodeBlocks.at(connection.edge->getDstNode())];
        require(source.after.at(connection.pack) == connection.source &&
                target.input.at(connection.pack) == connection.target,
                "PackSSA: interprocedural interface mismatch");
        const auto expected = SVFUtil::isa<CallCFGEdge>(connection.edge) ? Kind::FormalIn : Kind::ActualOut;
        require(versions[connection.target].kind == expected, "PackSSA: wrong interface definition");
    }
}

void PackSSA::Impl::dump(std::ostream& out) const
{
    const auto nodeID = [](const ICFGNode* node)
    {
        return node ? std::to_string(node->getId()) : std::string("-");
    };
    const auto edgeKey = [&](const IntraCFGEdge* edge)
    {
        if (!edge) return std::string("-\t-\t-\t-");
        return nodeID(edge->getSrcNode()) + "\t" + nodeID(edge->getDstNode()) + "\t" +
               (edge->getCondition() ? std::to_string(edge->getCondition()->getId()) : "-") + "\t" +
               (edge->getCondition() ? std::to_string(edge->getSuccessorCondValue()) : "-");
    };
    out << "pack-ssa\t1\n";
    for (const auto& block : blocks)
    {
        const auto function = block.function ? std::to_string(block.function->getId()) : "-";
        const auto edgeSource = block.edge ? nodeID(block.edge->getSrcNode()) : "-";
        const auto edgeTarget = block.edge ? nodeID(block.edge->getDstNode()) : "-";
        const auto condition = block.edge && block.edge->getCondition() ?
                               std::to_string(block.edge->getCondition()->getId()) : "-";
        const auto label = block.edge && block.edge->getCondition() ?
                           std::to_string(block.edge->getSuccessorCondValue()) : "-";
        out << "block\t" << block.id << '\t' << function << '\t' << nodeID(block.node)
            << '\t' << edgeSource << '\t' << edgeTarget << '\t' << (block.role == "super" ? 1 : 0)
            << '\t' << block.role << '\t' << condition << '\t' << label << '\n';
        out << "dom\t" << block.id << '\t' << idom[block.id] << '\n';
    }
    for (const auto& arc : arcs)
        out << "cfg\t" << arc.source << '\t' << arc.target << '\t' << arc.kind << '\n';
    for (const auto& version : versions)
    {
        out << "version\t" << version.id << '\t' << version.pack << '\t' << kindName(version.kind)
            << '\t' << version.block << '\t' << nodeID(version.node) << '\n';
        for (std::size_t i = 0; i < version.operands.size(); ++i)
            out << "operand\t" << version.id << '\t' << i << '\t' << version.operands[i].version
                << '\t' << version.operands[i].block << '\n';
    }
    for (const auto& block : blocks)
    {
        for (const auto& route : block.before)
            out << "route\tbefore\t" << block.id << '\t' << route.first << '\t' << route.second << '\n';
        for (const auto& route : block.after)
            out << "route\tafter\t" << block.id << '\t' << route.first << '\t' << route.second << '\n';
        if (block.edge)
            for (const auto& def : block.output)
                out << "edge-def\t" << edgeKey(block.edge) << '\t' << def.first << '\t' << def.second << '\n';
        if (!block.node) continue;
        for (const auto& def : block.input)
            out << "input-def\t" << nodeID(block.node) << '\t' << def.first << '\t' << def.second << '\n';
        for (const auto& def : block.output)
            out << "output-def\t" << nodeID(block.node) << '\t' << def.first << '\t' << def.second << '\n';
        const char* port = SVFUtil::isa<CallICFGNode>(block.node) ? "ActualIN" :
                           SVFUtil::isa<FunExitICFGNode>(block.node) ? "FormalOUT" :
                           SVFUtil::isa<FunEntryICFGNode>(block.node) ? "FormalIN" :
                           SVFUtil::isa<RetICFGNode>(block.node) ? "ActualOUT" : nullptr;
        if (port)
        {
            const bool input = SVFUtil::isa<FunEntryICFGNode>(block.node) || SVFUtil::isa<RetICFGNode>(block.node);
            for (const auto& value : input ? block.input : block.after)
                out << "port\t" << port << '\t' << nodeID(block.node) << '\t' << value.first << '\t' << value.second << '\n';
        }
    }
    for (auto it = graph.begin(); it != graph.end(); ++it)
        for (const auto* base : it->second->getOutEdges())
            if (const auto* edge = SVFUtil::dyn_cast<IntraCFGEdge>(base))
            {
                for (const auto& route : edgeRoutes.at(edge))
                    out << "edge-route\t" << edgeKey(edge) << '\t' << route.first << '\t' << route.second << '\n';
                const auto found = edgeWrites.find(edge);
                if (found != edgeWrites.end())
                    for (auto pack : found->second)
                        out << "declared-edge-write\t" << edgeKey(edge) << '\t' << pack << '\n';
            }
    for (auto it = graph.begin(); it != graph.end(); ++it)
    {
        const auto found = nodeWrites.find(it->second);
        if (found != nodeWrites.end())
            for (auto pack : found->second)
                out << "declared-node-write\t" << it->second->getId() << '\t' << pack << '\n';
    }
    for (const auto& connection : connections)
    {
        const auto* call = SVFUtil::dyn_cast<CallCFGEdge>(connection.edge);
        const auto* ret = SVFUtil::dyn_cast<RetCFGEdge>(connection.edge);
        const auto* callsite = call ? call->getCallSite() : ret->getCallSite();
        out << "connection\t" << (call ? "call" : "ret") << '\t' << callsite->getId()
            << '\t' << connection.pack << '\t' << connection.source << '\t' << connection.target
            << '\t' << nodeID(connection.edge->getSrcNode()) << '\t' << nodeID(connection.edge->getDstNode()) << '\n';
    }
}

PackSSA::PackSSA(const ICFG& graph, const PackSet& packs,
                 const NodeDefinitions& nodes, const EdgeDefinitions& edges)
    : impl_(std::make_unique<Impl>(graph, packs, nodes, edges))
{
    verify();
}

PackSSA::~PackSSA() = default;

const PackSSA::Routes& PackSSA::before(const ICFGNode* node) const
{
    static const Routes empty;
    const auto found = impl_->nodeBlocks.find(node);
    return found == impl_->nodeBlocks.end() ? empty : impl_->blocks[found->second].before;
}

const PackSSA::Routes& PackSSA::after(const ICFGNode* node) const
{
    static const Routes empty;
    const auto found = impl_->nodeBlocks.find(node);
    return found == impl_->nodeBlocks.end() ? empty : impl_->blocks[found->second].after;
}

const PackSSA::Routes& PackSSA::onEdge(const IntraCFGEdge* edge) const
{
    static const Routes empty;
    const auto found = impl_->edgeRoutes.find(edge);
    return found == impl_->edgeRoutes.end() ? empty : found->second;
}

const PackSSA::Routes& PackSSA::inputDefinitions(const ICFGNode* node) const
{
    static const Routes empty;
    const auto found = impl_->nodeBlocks.find(node);
    return found == impl_->nodeBlocks.end() ? empty : impl_->blocks[found->second].input;
}

const PackSSA::Routes& PackSSA::outputDefinitions(const ICFGNode* node) const
{
    static const Routes empty;
    const auto found = impl_->nodeBlocks.find(node);
    return found == impl_->nodeBlocks.end() ? empty : impl_->blocks[found->second].output;
}

const PackSSA::Routes& PackSSA::edgeDefinitions(const IntraCFGEdge* edge) const
{
    static const Routes empty;
    const auto found = impl_->edgeBlocks.find(edge);
    return found == impl_->edgeBlocks.end() ? empty : impl_->blocks[found->second].output;
}

const std::vector<PackSSA::Version>& PackSSA::versions() const
{
    return impl_->versions;
}

const std::vector<PackSSA::Connection>& PackSSA::connections() const
{
    return impl_->connections;
}

bool PackSSA::hasReducibleControlFlow() const
{
    std::vector<std::size_t> incoming(impl_->blocks.size(), 0);
    for (const auto& arc : impl_->arcs)
        if (!impl_->dominates(arc.target, arc.source))
            ++incoming[arc.target];
    std::deque<std::size_t> ready;
    for (std::size_t block = 0; block < incoming.size(); ++block)
        if (incoming[block] == 0)
            ready.push_back(block);
    std::size_t visited = 0;
    while (!ready.empty())
    {
        const auto block = ready.front();
        ready.pop_front();
        ++visited;
        for (auto id : impl_->blocks[block].outgoing)
        {
            const auto& arc = impl_->arcs[id];
            if (!impl_->dominates(arc.target, arc.source) && --incoming[arc.target] == 0)
                ready.push_back(arc.target);
        }
    }
    return visited == impl_->blocks.size();
}

void PackSSA::verify() const
{
    impl_->verify();
}

void PackSSA::dump(std::ostream& out) const
{
    impl_->dump(out);
}
