//===- AbstractInterpretation.h -- Abstract Execution----------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
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


//
//  Created on: Jan 10, 2024
//      Author: Xiao Cheng, Jiawei Wang
// The implementation is based on
// Xiao Cheng, Jiawei Wang and Yulei Sui. Precise Sparse Abstract Execution via Cross-Domain Interaction.
// 46th International Conference on Software Engineering. (ICSE24)
//
#pragma once
#include "AE/Core/AbstractDomain.h"
#include "AE/Core/AddressDomain.h"
#include "AE/Core/BoxAddressDomain.h"
#include "AE/Core/ICFGWTO.h"
#include "AE/Core/NumericalDomain.h"
#include "AE/Svfexe/AEDetector.h"
#include "AE/Svfexe/AEStat.h"
#include "AE/Svfexe/AEWTO.h"
#include "AE/Svfexe/AbsExtAPI.h"
#include "AE/Svfexe/PackingInput.h"
#include "AE/Svfexe/SVFIRAdapter.h"
#include "Graphs/CallGraph.h"
#include "Graphs/SCC.h"
#include "SVFIR/SVFIR.h"
#include "Util/SVFBugReport.h"
#include "Util/WorkList.h"
#include <memory>
#include <set>
#include <vector>

namespace SVF
{
class SVFGBuilder;
class SparseObjGraph;
class AbstractInterpretation;
class AbsExtAPI;
class AllocationSizeModel;
class AEStat;
/// AbstractInterpretation is same as Abstract Execution.
///
/// Owns the per-node abstract trace and exposes the read/write API
/// directly (no separate state-manager indirection).  Sparse modes are
/// implemented as subclasses that override the virtual hooks below
/// (cycle helpers, ValVar accessors, joinStates, def/use queries).
class AbstractInterpretation
{
    friend class AEStat;
    friend class ImpactRelationPacking;
    friend class AbsExtAPI;
    friend class BufOverflowDetector;
    friend class NullptrDerefDetector;

public:
    using State = SVF::BoxAddressDomain;

    /*
     * For recursive test case
     * int demo(int a) {
        if (a >= 10000)
            return a;
            demo(a+1);
        }

        int main() {
            int result = demo(0);
        }
     * if set TOP, result = [-oo, +oo] since the return value, and any stored
     object pointed by q at *q = p in recursive functions will be set to the top
     value.
     * if set WIDEN_ONLY, result = [10000, +oo] since only widening is applied
     at the cycle head of recursive functions without narrowing.
     * if set WIDEN_NARROW, result = [10000, 10000] since both widening and
     narrowing are applied at the cycle head of recursive functions.
     * */
    enum AESparsity
    {
        Dense,
        SemiSparse,
        Sparse,
        OhPackedSparse,
        /// D3: MemorySSA content versions, definition-site constraints,
        /// branch-refinement channel and use-site recovery (relational only).
        VersionedSparse
    };

    enum AENumericalDomain
    {
        Box,
        Octagon,
        Polyhedra
    };

    enum AERelationalPolicy
    {
        WholeRelational,
        QuerySliceRelational,
        EvaStyleRelational,
        QueryEvaRelational,
        SyntaxPackedRelational,
        ClosurePackedRelational,
        ImpactPackedRelational,
        LearnedPackedRelational,
        DuetPackedRelational,
        SpePackedRelational
    };

    enum AERelationalCallPolicy
    {
        ThroughCalls,
        IntraproceduralCalls
    };

    enum HandleRecur
    {
        TOP,
        WIDEN_ONLY,
        WIDEN_NARROW
    };

    enum AEFunEntryMode
    {
        MAIN,
        NO_MAIN
    };

    virtual void runOnModule();

    /// Destructor
    virtual ~AbstractInterpretation();

    /// Program entry
    void analyse();

    /// Analyze all entry points (functions without callers)
    void analyzeFromAllProgEntries();
    void initializeRootArguments(const FunEntryICFGNode* entry, const ICFGNode* node);

    /// Get all entry point functions (functions without callers)
    FIFOWorkList<const FunObjVar*> collectProgEntryFuns();

    /// Factory: returns the singleton instance.  The concrete class is
    /// chosen once, on first call, from `Options::AESparsity()`:
    /// the native Box semi-sparse/full-sparse implementation, or the dense
    /// Box implementation. Must be called only after option parsing.
    static AbstractInterpretation& getAEInstance();

    /// Select the provided-family path before the first getAEInstance() call.
    /// Dense Octagon accepts overlapping packs. The sparse PackSSA executor
    /// requires disjoint packs and a Post ledger. The family may be empty.
    static AbstractInterpretation& getAEInstanceWithPacking(RelationPacking packing);

    /// Same path, with the provider called before any numerical state is built.
    static AbstractInterpretation& getAEInstanceWithPacking(PackingProvider provider);
    static bool usesPackSSA();
    static bool usesOnDemand();
    AENumericalDomain numericalDomain() const;
    AESparsity sparsity() const;
    AERelationalPolicy relationalPolicy() const;
    bool packSSAEnabled() const;
    const State* intervalInputState(const ICFGNode* node) const;
    const State* intervalInputState(const SVFStmt* statement) const;

    void addDetector(std::unique_ptr<AEDetector> detector)
    {
        detectors.push_back(std::move(detector));
    }

    enum class QueryOutcome
    {
        Unreachable,
        Safe,
        Unsupported,
        May
    };

    /// Register a syntactic detector query before analysis. Registered but
    /// unevaluated queries remain Unreachable in the final ledger.
    void registerQuery(AEDetector::DetectorKind detector,
                       const ICFGNode* node, const SVFVar* operand,
                       const std::string& queryKind, const SVFStmt* site = nullptr);

    /// Merge a path/iteration result into a registered query. May dominates
    /// Unsupported, which dominates Safe; this prevents a later safe visit
    /// from hiding an earlier uncertain or unsafe one.
    void recordQuery(AEDetector::DetectorKind detector,
                     const ICFGNode* node, const SVFVar* operand,
                     const std::string& queryKind, QueryOutcome outcome,
                     const std::string& reason = "", const SVFStmt* site = nullptr);

    /// Retrieve SVFVar given its ID; asserts if no such variable exists
    inline const SVFVar* getSVFVar(NodeID varId) const
    {
        return svfir->getSVFVar(varId);
    }

    // ---- Domain projection access ------------------------------------

    /// Read a top-level variable's abstract value.  Dense base does a
    /// direct trace lookup; sparse subclasses override with their own
    /// resolution chain (def-site walk, call-result fallback, etc.).
    /// All three overloads are virtual so full-sparse can route ObjVar
    /// reads through the SVFG.
    virtual SVF::Interval getInterval(const ValVar* var,
                                      const ICFGNode* node);
    /// Return the numerical payload conditional on the value being
    /// initialized. Ordinary reads use getInterval(), which applies AE's
    /// uninitialized-read policy.
    virtual SVF::Interval getDefinedInterval(
        const ValVar* var, const ICFGNode* node);
    virtual SVF::Interval getInterval(const ObjVar* var,
                                      const ICFGNode* node);
    virtual SVF::Interval getInterval(const SVFVar* var,
                                      const ICFGNode* node);
    virtual SVF::AddressSet getAddressSet(const ValVar* var,
                                          const ICFGNode* node);
    virtual SVF::AddressSet getAddressSet(const ObjVar* var,
                                          const ICFGNode* node);
    virtual SVF::AddressSet getAddressSet(const SVFVar* var,
                                          const ICFGNode* node);

    /// Side-effect-free check that the node state is reachable and the value
    /// belongs to the typed analysis vocabulary. A supported but unconstrained
    /// value is represented by its facet's Top, not by absence.
    virtual bool hasAbsValue(const ValVar* var, const ICFGNode* node) const;
    virtual bool hasAbsValue(const ObjVar* var, const ICFGNode* node) const;
    virtual bool hasAbsValue(const SVFVar* var, const ICFGNode* node) const;

    /// Whether the numerical facet still includes the absent/uninitialized
    /// alternative. External-call fallback uses this to define an otherwise
    /// unmodelled non-void result as initialized Top without overwriting a
    /// handler's precise result.
    virtual bool numericalValueMayBeUninitialized(
        const ValVar* var, const ICFGNode* node) const;

    /// Write both scalar facets without constructing an intermediate value
    /// object. Sparse subclasses re-route ValVar writes to the def-site.
    virtual void updateValue(const ValVar* var,
                             const SVF::Interval& interval,
                             const SVF::AddressSet& addresses,
                             const ICFGNode* node);
    virtual void updateValue(const ObjVar* var,
                             const SVF::Interval& interval,
                             const SVF::AddressSet& addresses,
                             const ICFGNode* node);
    virtual void updateValue(const SVFVar* var,
                             const SVF::Interval& interval,
                             const SVF::AddressSet& addresses,
                             const ICFGNode* node);
    virtual void addUninitializedNumericalAlternative(
        const ValVar* var, const ICFGNode* node);

    void updateInterval(const SVFVar* var,
                        const SVF::Interval& interval,
                        const ICFGNode* node);
    void updateAddressSet(const SVFVar* var,
                          const SVF::AddressSet& addresses,
                          const ICFGNode* node);

    /// Interpret i1 truth consistently in the test helper and query ledger.
    bool isAssertionTrue(const ValVar* condition, const ICFGNode* node);

    /// Representation-independent memory and lifetime access uses native
    /// abstract locations; no encoded integer-address protocol is exposed.
    virtual SVF::Interval getMemoryInterval(
        SVF::Location location, const ICFGNode* node);
    virtual SVF::AddressSet getMemoryAddressSet(
        SVF::Location location, const ICFGNode* node);
    virtual bool hasMemoryValue(SVF::Location location,
                                const ICFGNode* node) const;
    virtual void updateMemoryValue(SVF::Location location,
                                   const SVF::Interval& interval,
                                   const SVF::AddressSet& addresses,
                                   const ICFGNode* node);
    struct RecursiveMod
    {
        NodeBS modifiedBases;
        bool allObjects = false;
    };
    /// Static overapproximation for TOP calls, available to version builders.
    bool recursiveTopSummary(const CallICFGNode*) const;
    RecursiveMod recursiveTopMod(const CallICFGNode*) const;
    virtual void prepareRecursiveHavoc(const CallICFGNode*, const NodeBS&, bool)
    {
    }
    virtual void markFreedMemory(SVF::Location location,
                                 const ICFGNode* node);
    virtual bool isFreedMemory(SVF::Location location,
                               const ICFGNode* node) const;

    // ---- State Access -------------------------------------------------

    /// Return the authoritative complete state used for control-flow joins
    /// and fixpoint computation.
    virtual const SVF::AbstractDomain& getAbstractState(
        const ICFGNode* node) const;

    /// Return the analysis-wide SSA-value carrier when the selected sparse
    /// implementation separates ValVars from ICFG memory states. Other
    /// implementations return nullptr.
    virtual const SVF::AbstractDomain* getScalarAbstractState()
    const;

    virtual bool hasAbsState(const ICFGNode* node) const;

    virtual SVF::Location locationOf(const ObjVar* object) const;
    virtual const ObjVar* objectAt(SVF::Location location) const;

    // ---- GEP / Load-Store / Type Helpers ------------------------------

    SVF::Interval getGepElementIndex(const GepStmt* gep);
    SVF::Interval getGepByteOffset(const GepStmt* gep);
    SVF::AddressSet getGepObjAddrs(
        const ValVar* pointer, const SVF::Interval& offset,
        const ICFGNode* node);

    /// Virtual so full-sparse can layer the GepObj overlay on top.
    virtual void loadValue(const ValVar* pointer,
                           SVF::Interval& interval,
                           SVF::AddressSet& addresses,
                           bool& numericalMayBeUninitialized,
                           const ICFGNode* node);
    virtual void storeValue(const ValVar* pointer,
                            const SVF::Interval& interval,
                            const SVF::AddressSet& addresses,
                            const ICFGNode* node);

    struct AllocationSizeBounds
    {
        u32_t lowerBound;
        u32_t upperBound;
    };

    AllocationSizeBounds getAllocaInstByteSize(const AddrStmt* addr);
    /// Sparrow Size(o) model shared by the main analysis, detector and packers.
    const AllocationSizeModel& allocationSizeModel();
    /// Sound lower bound on the bytes of every object allocated at `base`'s
    /// site in the current fixpoint; nullopt when the size is not modelled.
    std::optional<s64_t> allocationByteLowerBound(const BaseObjVar* base);
    /// Size(o) := allocated element count (D-005). Strong as in Sparrow
    /// unless SVF_AE_SIZE_WEAK is set.
    void assignAllocationSize(const AddrStmt* addr);
    /// Value of an unmodelled input (external result, root argument,
    /// unresolved call): its machine type range for integers, else Top.
    SVF::Interval unknownInterval(const SVFVar* var) const;

    const Set<const ICFGNode*>& getAnalyzedNodes() const
    {
        return allAnalyzedNodes;
    }

protected:
    /// Factory-only construction. External callers use getAEInstance().
    explicit AbstractInterpretation(bool intervalPreanalysis = false);

    /// SVF's BlackHole is an explicit summary object in the current transfer
    /// policy, not AddressSet object-top. Keeping its Location concrete
    /// matches the pointer-analysis value-flow contract while AddressSet still
    /// supports object-top for clients that require arbitrary modeled objects.
    SVF::AddressSet blackHoleAddressSet() const;
    // ---- Cycle helpers implemented by Box-backed execution modes ----
    // The dense versions write only to trace[cycle_head].  The semi-sparse
    // subclass adds def-site scatter on top for body ValVars.

    /// Clone the complete cycle-head state. Sparse subclasses may first gather
    /// values held at def-sites; dense implementations clone their domain
    /// state directly.
    virtual std::unique_ptr<SVF::AbstractDomain> cloneCycleHeadState(
        const ICFGCycleWTO* cycle);
    /// Widen prev with cur; write the widened state to trace[cycle_head].
    /// Returns true when next == prev (fixpoint).  Semi-sparse subclass
    /// additionally scatters ValVars to their def-sites.
    virtual bool widenCycleState(const SVF::AbstractDomain& prev,
                                 const SVF::AbstractDomain& cur,
                                 const ICFGCycleWTO* cycle);

    /// Narrow prev with cur; write the narrowed state back.  Returns true
    /// when narrowing is disabled or the narrowed state equals prev.
    /// Semi-sparse subclass scatters the narrowed ValVars on non-fixpoint.
    virtual bool narrowCycleState(const SVF::AbstractDomain& prev,
                                  const SVF::AbstractDomain& cur,
                                  const ICFGCycleWTO* cycle);

protected:
    /// Representation-independent state lifecycle used by the shared WTO and
    /// call/return drivers. Dense and sparse analyses provide different
    /// storage implementations behind this small surface.
    virtual void resetAbstractState(const ICFGNode* node);
    virtual void copyAbstractState(const ICFGNode* source,
                                   const ICFGNode* destination);
    virtual std::unique_ptr<SVF::AbstractDomain> cloneAbstractState(
        const ICFGNode* node) const;
    virtual std::unique_ptr<SVF::AbstractDomain> cloneScalarSummary() const
    {
        return nullptr;
    }

    /// Normalize a node after its transfers and detectors have consumed any
    /// temporary operands. Native sparse implementations use this boundary to
    /// keep ValVar values out of persistent ICFG states.
    virtual void finalizeAbstractState(const ICFGNode* node);
    virtual void beginAbstractState(const ICFGNode*) {}
    /// Capture edge definitions after refinement and parallel phi transfer.
    virtual void recordIncomingAbstractState(const ICFGEdge*, const State&) {}
    virtual void initializeExecutionPolicy() {}

    /// Pull-based state merge: read abstractTrace[pred] for each predecessor,
    /// apply branch refinement for conditional IntraCFGEdges, and join into
    /// abstractTrace[node]. Returns true if at least one predecessor had state.
    /// Virtual so full-sparse can layer per-MRSVFGNode obj pulls on top of the
    /// base ICFG-edge merge.
    virtual bool mergeStatesFromPredecessors(const ICFGNode* node);
    void initializeSparseObjectRoutes();
    State sparseObjectPredecessor(const State&) const;
    void pullSparseObjectRoutes(const ICFGNode*, const State* previous);
    bool routesObject(SVF::Variable) const;
    void recordSparseObjectStore(const ICFGNode*, const SVF::AddressSet&);
    std::unique_ptr<SVFGBuilder> objectRouteBuilder_;
    std::unique_ptr<SparseObjGraph> objectRoutes_;
    std::set<SVF::Variable> objectRouteFallback_;
    Map<const ICFGNode*, std::set<SVF::Variable>> objectRouteDefinitions_;
    Map<const ICFGNode*, std::set<SVF::Variable>>
        objectRoutePreviousDefinitions_;
    std::set<SVF::Variable> packedObjectCoordinates_;
    mutable std::set<SVF::Variable> routedObjectVariables_;
    mutable SVF::Location lastRoutedLocation_;
    bool objectRouteFallbackAll_ = false;

    /// Representation-independent feasibility query used by shared transfer
    /// code.  Native dense domains apply the constraint directly.
    virtual bool isBranchEdgeFeasibleAt(const IntraCFGEdge* edge,
                                        const ICFGNode* predecessor);

    bool isSwitchDefaultEdge(const IntraCFGEdge* edge) const;
    bool isSwitchBranchEdgeFeasible(const IntraCFGEdge* edge,
                                    const SVF::Interval& input) const;
    void collectSwitchRefinement(const IntraCFGEdge* edge,
                                 SVF::AbstractDomain& state);

    /// Collect branch-induced interval refinement after a feasible edge has
    /// been selected for normal CFG-state merging.
    void collectBranchRefinement(const IntraCFGEdge* edge,
                                 SVF::AbstractDomain& state);

    /// Hook called by collectBranchRefinement for each object narrowed by the
    /// branch. Dense and semi-sparse implementations meet the constraint into
    /// the transient edge state; full-sparse records it for MemorySSA flow.
    virtual void recordBranchRefinement(
        NodeID objId, const SVF::Interval& narrowed,
        SVF::AbstractDomain& state, const ICFGNode* loadIcfg,
        const ICFGNode* succ);

protected:
    /// Initialize abstract state for the global ICFG node and process global
    /// statements
    virtual void handleGlobalNode();

    /// Materialise the value produced by an AddrStmt without prescribing a
    /// concrete state representation.
    virtual void initializeObjectValue(const ObjVar* object,
                                       SVF::Interval& interval,
                                       SVF::AddressSet& addresses,
                                       const ICFGNode* node);

    /// Handle a call site node: dispatch to ext-call, direct-call, or
    /// indirect-call handling
    virtual void handleCallSite(const ICFGNode* node);

    /// Handle a WTO cycle (loop or recursive function) using widening/narrowing
    /// iteration
    virtual void handleLoopOrRecursion(const ICFGCycleWTO* cycle,
                                       const CallICFGNode* caller);

    /// Handle a function body via worklist-driven WTO traversal starting from
    /// funEntry
    bool handleFunction(const ICFGNode* funEntry, const CallICFGNode* caller);

    /// A context-insensitive callee can grow when a later call site is
    /// analyzed. Recompute already-reached sibling return sites so their
    /// caller states cover the enlarged callee summary.
    void refreshSiblingReturnSites(const FunObjVar* callee,
                                   const RetICFGNode* currentReturn);

    /// Handle an ICFG node: execute statements; return true if state changed
    void handleICFGNode(const ICFGNode* node);

    /// Dispatch an SVF statement
    /// (Addr/Binary/Cmp/Load/Store/Copy/Gep/Select/Phi/Call/Ret) to its handler
    virtual void handleSVFStatement(const SVFStmt* stmt);

    void updateStateOnAddr(const AddrStmt* addr);

    void updateStateOnBinary(const BinaryOPStmt* binary);

    void updateStateOnCmp(const CmpStmt* cmp);

    void updateStateOnLoad(const LoadStmt* load);

    void updateStateOnStore(const StoreStmt* store);

    void updateStateOnCopy(const CopyStmt* copy);

    void updateStateOnCall(const CallPE* callPE);

    void updateStateOnRet(const RetPE* retPE);

    void updateStateOnGep(const GepStmt* gep);

    void updateStateOnSelect(const SelectStmt* select);

    void updateStateOnPhi(const PhiStmt* phi);

    /// Reconstruct and apply a basic-block phi tuple when `node` is the last
    /// ICFG node of that tuple. Shared by solver execution and Post replay.
    void updateStateOnPhiGroupAtNode(const ICFGNode* node);

    /// Apply every phi at one ICFG program point as a simultaneous tuple for
    /// each predecessor, then join predecessor alternatives.  Processing the
    /// targets independently loses relations shared by every alternative.
    void updateStateOnPhiGroup(const std::vector<const PhiStmt*>& phis);

    ICFG* icfg;
    CallGraph* callGraph;
    AEStat* stat;

    AbsExtAPI* getUtils()
    {
        return utils;
    }

    // helper functions in handleCallSite
    virtual bool isExtCall(const CallICFGNode* callNode);
    virtual void handleExtCall(const CallICFGNode* callNode);
    virtual bool isRecursiveFun(const FunObjVar* fun);
    virtual void skipRecursionWithTop(const CallICFGNode* callNode);
    virtual bool isRecursiveCallSite(const CallICFGNode* callNode,
                                     const FunObjVar*);
    virtual void handleFunCall(const CallICFGNode* callNode);

    bool skipRecursiveCall(const CallICFGNode* callNode);
    const FunObjVar* getCallee(const CallICFGNode* callNode);

    Set<const ICFGNode*>
    allAnalyzedNodes; // All nodes ever analyzed (across all entry points)

    std::vector<std::unique_ptr<AEDetector>> detectors;
    AbsExtAPI* utils = nullptr;

protected:
    struct UnknownTargetTelemetry
    {
        std::uint64_t loads = 0;
        std::uint64_t stores = 0;
        std::uint64_t storeCellsVisited = 0;
        std::uint64_t sparseDefinitionCellsVisited = 0;
    };

    bool unknownTargetTelemetryEnabled() const
    {
        return unknownTargetTelemetryEnabled_;
    }
    UnknownTargetTelemetry& unknownTargetTelemetry()
    {
        return unknownTargetTelemetry_;
    }

    virtual State& ensureState(const ICFGNode* node);
    virtual const State& state(const ICFGNode* node) const;
    /// State that owns SSA numerical relations created by a transfer. Dense
    /// AE uses the current ICFG state; semi-sparse AE overrides this with its
    /// module-wide SSA carrier.
    virtual State& scalarTransferState(const ICFGNode* node);
    virtual State phiAlternativeState(const ICFGNode* predecessor);
    virtual void assignRelationalValue(
        const ValVar* target,
        const SVF::LinearExpression& expression,
        const SVF::Interval& interval,
        const SVF::AddressSet& addresses,
        const ICFGNode* node);
    virtual void recordRelationalDependency(SVF::Variable target,
                                            SVF::Variable source);
    /// Record that two results belong to the same simultaneous definition.
    /// Unlike an ordinary use-def dependency, a tuple peer must not be
    /// flattened through the peer's own operands.
    virtual void recordRelationalTupleDependency(
        SVF::Variable target,
        SVF::Variable peer);
    virtual void recordRelationalSummary(SVF::Variable target,
                                         const State& summary,
                                         const ICFGNode* node);
    virtual void assignRelationalStore(
        const ValVar* source, SVF::Variable content,
        const ICFGNode* node);
    virtual void assignRelationalLoad(
        const ValVar* target, SVF::Variable content,
        const ICFGNode* node);
    void joinRelationalMemory(const ValVar* value,
                              const SVF::AddressSet& pointees,
                              const State& before,
                              const ICFGNode* node, bool store);
    virtual void publishRelationalLoad(const ValVar* target,
                                       const ICFGNode* node);
    State topState() const;
    State bottomState() const;
    std::unique_ptr<SVF::NumericalDomain> makeNumericalDomain(
        bool bottom) const;
    bool initializeBuiltInPacking();
    void initializePackingVocabulary();
    void initializeProvidedPacking();
    bool usesBuiltInOnDemand() const;
    void initializeRelationalPolicy();
    void initializeObjectPacking();
    void dumpFixedPacking(const char* prefix) const;
    void initializeSyntaxPacking();
    void initializeFixedPacking();
    void applyRelationalCallBoundary(State& state, const ICFGEdge* edge,
                                     const ICFGNode* target) const;
    /// Execute the binding owned by one return edge before alternative
    /// callee post-states are joined.
    void applyReturnEdgeTransfer(State& state,
                                 const RetCFGEdge* edge) const;
    /// D-009: run every phi of `target`'s block as one parallel assignment
    /// on the incoming edge, before the predecessor states are joined.
    void applyPhiEdgeTransfer(State& state, const ICFGEdge* edge,
                              const ICFGNode* target);
    /// Whether `block` uses the D-009 edge transfer (Dense only, and every
    /// phi maps each incoming edge to exactly one operand).
    bool phiEdgeBlock(const SVFBasicBlock* block);
    /// Publish a representation-specific summary after return alternatives
    /// have been joined at a RetICFGNode.
    virtual void recordMergedReturnSummary(const RetICFGNode* returnSite);

    void assignValue(State& state, SVF::Variable variable,
                     const SVF::Interval& interval,
                     const SVF::AddressSet& addresses);
    void assignMemoryValue(State& state,
                           SVF::Variable content,
                           const SVF::Interval& interval,
                           const SVF::AddressSet& addresses);
    /// Strong writes require a definite, non-summary, live memory cell.
    bool canStrongStore(const SVF::AddressSet& pointees,
                        const ObjVar& object, const State& state);
    bool canRefineMemory(const SVF::AddressSet& pointees,
                         const ObjVar& object, const State& state);
    SVF::Variable memoryVariable(const ObjVar& object,
                                 const State& state) const;
    void assignInterval(State& state, SVF::Variable variable,
                        const SVF::Interval& interval);
    void constrainInterval(State& state, SVF::Variable variable,
                           const SVF::Interval& interval) const;
    virtual void materializeValue(State& state, const ValVar* value,
                                  const ICFGNode* node);
    virtual void materializeRelations(
        State& state, const std::vector<SVF::Variable>& variables,
        const ICFGNode* node);
    /// Rebuild a bounded affine expression from a uniquely defined SSA value.
    /// Integer arithmetic is unfolded only when its interval proves that the
    /// LLVM operation cannot wrap at this program point. Unsupported
    /// definitions remain sound leaf variables.
    std::optional<SVF::LinearExpression>
    reconstructLinearExpression(
        const SVFVar* operand, State& state, const ICFGNode* node,
        std::vector<SVF::Variable>& relationVariables,
        unsigned depth, std::set<NodeID>& visiting);
    void forgetValue(State& state,
                     SVF::Variable variable) const;
    struct ConditionRefinement
    {
        const SVFVar* condition;
        bool taken;
    };
    using ConditionAlternatives = std::vector<std::vector<ConditionRefinement>>;
    ConditionAlternatives conditionAlternatives(const SVFVar*, bool taken) const;
    void collectConditionWrites(const SVFVar*, bool taken, const ICFGNode*,
                                std::set<SVF::Variable>&, unsigned depth = 0) const;
    void collectComparisonWrites(const SVFVar*, std::set<SVF::Variable>&,
                                 unsigned depth) const;
    std::set<SVF::Variable> branchWrites(const IntraCFGEdge*) const;
    void assumeBranch(const IntraCFGEdge* edge, State& state);
    void assumeCondition(const SVFVar* condition, bool taken, State& state,
                         const ICFGNode* source, unsigned depth = 0);

    SVFIR* svfir{nullptr};
    AEWTO* preAnalysis{nullptr};
    bool intervalPreanalysis_ = false;
    SVFIRAdapter adapter_;
    std::shared_ptr<AllocationSizeModel> allocationSizeModel_;
    std::shared_ptr<const std::vector<SVF::Variable>>
    relationalVocabulary_;
    std::shared_ptr<const std::vector<std::vector<SVF::Variable>>>
    relationalPacking_;
    std::map<const ObjVar*, std::size_t> objectPacks_;
    bool providedPacking_ = false;
    PackingProvider packingProvider_;
    std::size_t relationalSeedCount_ = 0;
    std::size_t relationalDroppedCount_ = 0;
    Map<const ICFGNode*, State> abstractTrace_;
    Map<const ICFGNode*, State> intervalInputs_;
    Map<const SVFStmt*, State> intervalStatementInputs_;
    std::unique_ptr<AbstractInterpretation> intervalPreanalysis();
    SVF::Variable intervalOffsetVariable(const SVFVar* variable) const;
    SVF::Interval intervalPointerOffset(const SVFVar* variable, const State& state) const;
    void updateIntervalPointerOffsets(const SVFStmt* statement, const State& before);
    mutable std::map<NodeID, SVF::Variable> intervalOffsets_;

    unsigned summaryIteration_ = 0;
    // A predecessor merge overwrites the Dense node's current state. Keep
    // split-phi widening history separate from that incoming pre-state.
    Map<const PhiStmt*, SVF::Interval> phiIntervalHistory_;
    Map<const SVFBasicBlock*, bool> phiEdgeBlocks_;
    /// D-014 item 6: comparisons use their direct operands only (depth 0);
    /// relations through earlier definitions come from the pack's state.
    static constexpr unsigned kComparisonUnfoldDepth = 0;
    std::size_t phiEdgeFallbackBlocks_ = 0;
    bool unknownTargetTelemetryEnabled_ = false;
    UnknownTargetTelemetry unknownTargetTelemetry_;

    struct QueryRecord
    {
        AEDetector::DetectorKind detector = AEDetector::UNKNOWN;
        NodeID icfgNode = 0;
        NodeID operand = 0;
        std::string queryKind;
        std::string function;
        std::string sourceLocation;
        std::string semanticSite;
        const SVFStmt* statement = nullptr;
        QueryOutcome outcome = QueryOutcome::Unreachable;
        std::string reason;
        bool observed = false;
    };

    struct CertifiedQuery
    {
        std::string row;
        std::string outcome;
    };
    using CertifiedQueries = std::map<std::string, CertifiedQuery>;

    Map<std::string, QueryRecord> queryLedger_;
    CertifiedQueries boxQueries_;
    bool strictQueryCoverage() const;
    std::string queryLedgerPath() const;
    CertifiedQueries readCertifiedQueries(const std::string& path, bool sameRun) const;
    void writeBoxMayLedger(const CertifiedQueries* relational) const;
    bool prepareBoxMayDemand();
    void selectBoxMayPacks();
    std::vector<std::string> queryIdentityFields(const QueryRecord& record) const;
    bool queryLedgerEnabled() const;
    void enumerateQueries();
    void enumerateStandardAssertionQueries();
    void recordReachedAssertion(const CallICFGNode* call);
    void writeQueryLedger();
    void writeQueryLedgerTo(const std::string& path) const;
    void writeInvariantStates(const std::string& path) const;
    /// Evaluate queries afresh on converged solver states or independently
    /// reconstructed Post states. The iteration ledger remains available.
    void recheckQueriesOnFinalStates(Map<const ICFGNode*, State>& finals,
                                     const std::string& path, bool readSolverStates = false);
    Map<const ICFGNode*, State>* recheckStates_ = nullptr;

    bool postCheckEnabled() const;
    /// Reconstruct the semantic post-state exposed to the dense-equation
    /// checker. Sparse solvers materialize only scalars available at `node`.
    virtual State reconstructPostState(
        const ICFGNode* node,
        const std::set<SVF::Variable>& availableScalars);
    virtual void normalizePostReplayState(
        State& state,
        const std::set<SVF::Variable>& availableScalars) const;
    virtual void preparePostReplayState(
        State& state, const ICFGNode* target,
        const std::set<SVF::Variable>& inputScalars) const;
    virtual void restorePostReplayCallerFrame(
        State& state, const RetICFGNode* returnSite,
        const State& callerState,
        const std::set<SVF::Variable>& callerScalars) const;
    void verifyPostFixpoint();

    bool shouldApplyNarrowing(const FunObjVar* fun);

private:
    static AbstractInterpretation& getAEInstanceImpl(PackingProvider provider);
};
} // namespace SVF
