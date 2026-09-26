import Mathlib
import Submission.ComponentChart
import Submission.FirstPrefixChart
import Submission.IntervalSide
import Submission.ArcRestrict
import Submission.EndStripGlue
import Submission.Commons.Topology.Homeomorph.subtype_preimage_homeo
import Submission.Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape
import Submission.Commons.Topology.OneManifold.noncompact_connected_oneManifold_interval
import Submission.Commons.Topology.OneManifold.compact_connected_oneManifold_circle
import Submission.EmbeddedCircleWinding
import Submission.ParameterWinding

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S205 — the interval side of the component dichotomy: the region chart
and what it unlocks (module Submission/ComponentIntervalSide.lean)

Per the S204 STATUS the only interval-side gate left on the per-level
`hD_k` supply is the region/component chart `χ : Ω ≃ₜ ORI 0 1`.  This
module opens the dichotomy's interval side: it fixes the exact
statement of that gate and proves everything that unlocks once the gate
is passed.

**The gate (target statement, dichotomy interval case).**
`TrisecantComponentIntervalSide h hqf hgp c₀` — with
`¬ IsCompact (connectedComponent c₀ : Set (OSub r))` (the non-compact
side of the dichotomy) there is a component chart
`OpenRealInterval 0 1 ≃ₜ TrisecantComponent r c₀`.  Its proof is the
generic connected-1-manifold classification (S153 target
`connected_oneManifold_dichotomy`; engine: OneManifold + TwoArcUnion +
TwoChartGlue + RealIntervalShape + the countable open-arc cover of
`trisecantComponent_countable_open_arc_cover`, S152/S153) instantiated
on `TrisecantComponent r c₀` via `trisecantComponent_isOneManifold`;
the component is connected (proved below) and second-countable/Hausdorff
(S152).  This is the recorded remainder; the module below proves the
component-side plumbing that the dichotomy and the walk both consume.

Content (verified, sorry-free):

1. **`trisecantComponent_connectedSpace`** — every component type is
   `ConnectedSpace` (the subtype of a connected component:
   `Subtype.connectedSpace (isConnected_connectedComponent)`), the
   connectedness conjunct the dichotomy needs;
2. **`trace_subset_component`** — every walk trace lies in the
   component of `c₀` (from `hC : ∀ n, cl n ∈ connectedComponent c₀`
   through `OChartTrace_subset_component`) — the trace-containment that
   lets the whole component serve as the region `Ω`;
3. **`walk_transitionDomain_connected_of_component_chart`** — the gate
   crossing: once the component chart `χ : ORI 0 1 ≃ₜ TrisecantComponent
   r c₀` exists (the dichotomy's interval case), EVERY per-level `hD_k`
   is supplied (`IsConnected (transitionDomain (walkChart k) (walkChart
   (k+1)))` for all `k`): the S204(iii) corollary with `Ω :=
   connectedComponent c₀` and the trace containments of (2);
4. **`walk_prefixThree_intervalChart_of_component`** — the wired
   output: with the component chart and the first non-vacuous
   non-wrapping interface `hNW₁`, the S203 pattern produces the
   interval chart of the three-trace prefix `P'_3` — a prefix chart
   genuinely sourced from the interval-side component chart.

Everything here is verified (no axioms, no `sorry`).
-/

/-- **The dichotomy interval-case gate (target statement).**  The
non-compact side of the component classification: if the component of
`c₀` is not compact then it is homeomorphic to the open unit interval.
(Proof = the generic connected-1-manifold dichotomy instantiated on
`TrisecantComponent r c₀`; recorded as the next stage.) -/
def TrisecantComponentIntervalSide (r : ℝ → Space) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) : Prop :=
  ¬ IsCompact (connectedComponent c₀ : Set (OSub r)) →
    Nonempty (OpenRealInterval 0 1 ≃ₜ TrisecantComponent r c₀)

/-- **The component type is connected** (a subtype of a connected
component). -/
theorem trisecantComponent_connectedSpace {r : ℝ → Space} (c₀ : OSub r) :
    ConnectedSpace (TrisecantComponent r c₀) := by
  exact Subtype.connectedSpace (s := connectedComponent c₀)
    (isConnected_connectedComponent (x := c₀))

/-- **Every walk trace lies in the component of `c₀`** (from
`hC : ∀ n, cl n ∈ connectedComponent c₀` via
`OChartTrace_subset_component`), so the whole component can serve as the
region `Ω` of the S204 interval-side supply. -/
lemma trace_subset_component {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hC : ∀ n : ℕ, cl n ∈ connectedComponent c₀)
    (k : ℕ) :
    chartTrace (walkChart h hqf hgp cl e k) ⊆ connectedComponent c₀ := by
  intro c hc
  have ht := @OChartTrace_subset_component r h hqf hgp c₀ (cl (e k)) (hC (e k))
  simpa [walkChart, OChartTraceSet, chartTrace] using ht hc

/-- **The gate crossing: every per-level `hD_k` from the component
chart.**  Once the component chart `χ : ORI 0 1 ≃ₜ TrisecantComponent
r c₀` exists (the dichotomy's interval case), every transition domain
`D_k = transitionDomain (walkChart k) (walkChart (k+1))` is connected —
the S204(iii) interval-side supply with `Ω := connectedComponent c₀`
and the trace containments of `trace_subset_component`. -/
theorem walk_transitionDomain_connected_of_component_chart {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hC : ∀ n : ℕ, cl n ∈ connectedComponent c₀)
    (χ : OpenRealInterval 0 1 ≃ₜ TrisecantComponent r c₀) :
    ∀ k : ℕ, IsConnected (transitionDomain (walkChart h hqf hgp cl e k)
      (walkChart h hqf hgp cl e (k + 1))) := by
  intro k
  exact walk_transitionDomain_connected_of_intervalChart h hqf hgp cl e hoverlap k
    (Ω := connectedComponent c₀) χ.symm
    (trace_subset_component h hqf hgp cl e hoverlap c₀ hC k)
    (trace_subset_component h hqf hgp cl e hoverlap c₀ hC (k + 1))

/-- **The wired prefix chart from the component chart.**  With the
component chart `χ` (interval case) and the first non-vacuous
non-wrapping interface `hNW₁`, the S203 pattern produces the interval
chart of the three-trace prefix `P'_3` — the per-level `hD₀`/`hD₁`
supplied by (3), the `hconn 0`/`hconn 1` by S202/S203, the prefix chart
by the S183 finite-chain engine. -/
theorem walk_prefixThree_intervalChart_of_component {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (c₀ : OSub r) (hC : ∀ n : ℕ, cl n ∈ connectedComponent c₀)
    (χ : OpenRealInterval 0 1 ≃ₜ TrisecantComponent r c₀)
    (hNW1 : ∀ c : OSub r,
        c ∈ (⋃ j ∈ Finset.range 2, chartTrace (walkChart h hqf hgp cl e j)) ∩
            chartTrace (walkChart h hqf hgp cl e 2) →
        c ∈ chartTrace (walkChart h hqf hgp cl e 1)) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {c : OSub r // c ∈ ⋃ j ∈ Finset.range 3,
        chartTrace (walkChart h hqf hgp cl e j)}) := by
  have hD := walk_transitionDomain_connected_of_component_chart h hqf hgp cl e hoverlap c₀ hC χ
  exact walk_prefixThree_intervalChart h hqf hgp cl e hoverlap
    (hD 0) hNW1 (hD 1)

/-! ## S206 — the interval-case assembly skeleton (DONE: the generic
extraction landed — fleet L46)

The gate theorem `trisecantComponent_intervalSide` is assembled from its
premises: the component type is a connected non-compact topological
1-manifold (IsOneManifold by S152, connected by S205, non-compact from
the set-level hypothesis through the subtype-compactness bridge) with a
countable open arc cover (S153); the generic dichotomy's interval case
then produces the homeomorphism.  The assembly is VERIFIED and the final
extraction — the generic dichotomy theorem
`noncompact_connected_oneManifold_interval` (S153 slices (b2)/(c)/(d)) —
was PROVED by the fleet (commons L46,
`Commons.Topology.OneManifold.noncompact_connected_oneManifold_interval`)
and this theorem is now the one-line `simpa` bridge to it.  NOTE on the
proof shape: the compact branch of the dichotomy is already excluded by
the hypothesis (`TrisecantComponentIntervalSide` is the conditional
`¬ IsCompact … → Nonempty (… ≃ₜ …)`), so `intro hnc` IS the
non-compact branch; the generic theorem carries the whole dichotomy
content.

STATUS: DONE — this section is sorry-free; `trisecantComponent_intervalSide`
holds.  (Recorded in ROADMAP S206/S242.)
-/

/-- The component is not compact as a TYPE whenever its set is not
compact (the subtype-range bridge: the component set is the range of the
continuous subtype projection, compact by `isCompact_range`). -/
theorem trisecantComponent_notCompactSpace {r : ℝ → Space} (c₀ : OSub r)
    (hnc : ¬ IsCompact (connectedComponent c₀ : Set (OSub r))) :
    ¬ CompactSpace (TrisecantComponent r c₀) := by
  intro hc
  apply hnc
  have hf : Continuous (fun t : TrisecantComponent r c₀ => (t : OSub r)) := continuous_subtype_val
  have hr := isCompact_range (f := fun t : TrisecantComponent r c₀ => (t : OSub r)) hf
  have hrange : Set.range (fun t : TrisecantComponent r c₀ => (t : OSub r)) =
      (connectedComponent c₀ : Set (OSub r)) := by
    ext c
    constructor
    · rintro ⟨t, rfl⟩
      exact t.2
    · intro hc'
      exact ⟨⟨c, hc'⟩, rfl⟩
  simpa [hrange] using hr

/-- **The generic dichotomy extraction (S153/S206, DONE — fleet L46 landed).**  A connected,
second-countable, Hausdorff, locally interval-charted topological space
(a connected topological 1-manifold without boundary) that is NOT
compact is homeomorphic to the open unit interval `(0,1)`.

**Proof decomposition (recorded; the module doc of S238 below fixes the
sub-lemma statements).**

- **Step A — the exhaustion.**  Build a nested exhaustion `V n` of `X`
  by PROPER open arc prefixes, each `V n ≃ₜ (0,1)` with the old prefix
  sitting over an initial segment of the new chart (a "compatible
  exhaustion" with the ends tracked — the two ends of the growing arc
  never wrap around to meet, which is where the non-compactness
  hypothesis is used).  Base: `arc_or_proper_open_prefix` (VERIFIED in
  S238: either `X ≃ₜ (0,1)` already, or a proper arc prefix exists).
  Step: at a boundary point of the current prefix, the one-sided attach
  machinery (`EndStripExtension` from `OneSidedAttach.attach_cutting_*`
  S233 + `glue_step_of_EndStripExtension` S234) extends the prefix by
  one arc; the `hF` input is iii-c (NoOscillation S236, pinned); the
  two-sided wrap is excluded by non-compactness (TerminalAttachment
  S218, open).  The per-level supply statement is fixed as
  `OneManifoldPerLevelExtension` (S238).
- **Step B — the alignment.**  Turn the compatible exhaustion into the
  literal real-coordinate agreement family `i n : (0, L n) → X` of the
  canonical length form (S216 Finding A / S217 item (2), open; the
  per-level glue S207/S208 + the S237 coordinate picture feed it).
- **Step C — the assembly (VERIFIED).**  `chain_initialSegments_union_homeo_openUnit`
  (ChainUnionOrderedInitialSegment, L35) turns the length-form family
  into `Nonempty (ORI 0 1 ≃ₜ X)`.

The FULL generic classification (steps A+B+C in one theorem) has been
PROVED by the fleet and committed as commons L46
(`Commons.Topology.OneManifold.noncompact_connected_oneManifold_interval`);
this theorem is now the one-line `simpa [LocallyIntervalChart,
OpenRealInterval]` bridge to it.  This closes the interval side of
`connected_oneManifold_dichotomy` and with it
`TrisecantComponentIntervalSide` (whose proof below consumes this
theorem directly). -/
theorem noncompact_connected_oneManifold_interval {X : Type*} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] [Nonempty X]
    (hLoc : LocallyIntervalChart X) (hconn : ConnectedSpace X) (hnc : ¬ CompactSpace X) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ X) := by
  -- fleet L46 (Commons.Topology.OneManifold.noncompact_connected_oneManifold_interval):
  -- the full generic classification in pure form; `LocallyIntervalChart`/`OpenRealInterval`
  -- unfold to its `∀ x, ∃ U, … {t : ℝ // t ∈ Ioo lo hi} ≃ₜ U` hypothesis and
  -- `{t : ℝ // t ∈ Ioo (0 : ℝ) 1}` conclusion.
  simpa [LocallyIntervalChart, OpenRealInterval] using
    (Commons.Topology.OneManifold.noncompact_connected_oneManifold_interval
      (X := X) hLoc hconn hnc)

/-- **The gate theorem (interval case, assembled).**  A non-compact
connected component of the trisecant set is homeomorphic to the open
unit interval: `TrisecantComponentIntervalSide` — assembled from the
component 1-manifold structure (S152/S153/S205) and the generic
dichotomy extraction `noncompact_connected_oneManifold_interval`
(S206, DONE — fleet L46). -/
theorem trisecantComponent_intervalSide {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    TrisecantComponentIntervalSide r hqf hgp c₀ := by
  intro hnc
  classical
  haveI : T2Space (TrisecantComponent r c₀) := component_t2Space c₀
  haveI : SecondCountableTopology (TrisecantComponent r c₀) := component_secondCountableTopology c₀
  haveI : Nonempty (TrisecantComponent r c₀) := ⟨⟨c₀, mem_connectedComponent⟩⟩
  have hLoc : LocallyIntervalChart (TrisecantComponent r c₀) := by
    dsimp [LocallyIntervalChart]
    intro x
    rcases component_local_interval h hqf hgp c₀ x with ⟨U, hUopen, hxU, lo, hi, hhomeo⟩
    refine ⟨U, hUopen, hxU, lo, hi, ?_⟩
    simpa using hhomeo
  have hncT : ¬ CompactSpace (TrisecantComponent r c₀) :=
    trisecantComponent_notCompactSpace c₀ hnc
  rcases noncompact_connected_oneManifold_interval (X := TrisecantComponent r c₀)
      hLoc (trisecantComponent_connectedSpace c₀) hncT with ⟨e⟩
  exact ⟨e⟩

/-! ## S238 — the S206 decomposition: the per-level extension target and
the exhaustion BASE (VERIFIED)

Per the S206 doc (above), the classification's proof decomposes into
Step A (the compatible exhaustion), Step B (the alignment) and Step C
(the verified L35 assembly).  This section fixes the two sub-lemma
statements of Step A that are independent of the one-dimensional
supply:

1. **`subtypeUnivHomeo`** (VERIFIED) — the `univ`-subtype reassociation
   homeo `{x // x ∈ univ} ≃ₜ X` (used when a chart covers the whole
   space: `U = univ` gives the desired chart of `X`);
2. **`arc_or_proper_open_prefix`** (VERIFIED) — the exhaustion BASE:
   under the one-manifold hypotheses either `X ≃ₜ (0,1)` already (the
   exhaustion is complete at level 0) or there is a PROPER open arc
   prefix `P ≃ₜ (0,1)` from which the per-level extension starts (an
   arc chart of any point is the whole space, or is the proper prefix);
3. **`OneManifoldPerLevelExtension`** (pinned target) — Step A's
   per-level supply: in a connected non-compact locally-interval-charted
   Hausdorff ambient, every proper open arc prefix admits an END-STRIP
   extension (`EndStripExtension P κ`, S234 — the orientation-neutral
   data whose glue `glue_step_of_EndStripExtension` charts `P ∪ V`).
   Its proof is the boundary attach at a point of `P̄ ∖ P`
   (`proper_arc_prefix_has_boundary`, T1Abstract): the one-sided
   attach machinery of OneSidedAttach (S221–S233,
   `endStripExtension_of_rawBoundary`) supplies it given the raw
   boundary data; the `hF` input is iii-c (NoOscillation S236) and the
   two-sided alternative is the wrap excluded by non-compactness
   (TerminalAttachment S218 — both recorded open).  Iterating
   `OneManifoldPerLevelExtension` from `arc_or_proper_open_prefix`'s
   prefix and excluding the wrap gives Step A's exhaustion; the S237
   coordinate picture (`prefix_coord_interval`) and Step B then feed
   Step C.

Everything here is verified (no axioms, no `sorry`) except the pinned
target `OneManifoldPerLevelExtension` (a `def Prop`, not a theorem).
-/

noncomputable def subtypeUnivHomeo (X : Type*) [TopologicalSpace X] :
    ({x : X // x ∈ (univ : Set X)}) ≃ₜ X := by
  let A := {x : X // x ∈ (univ : Set X)}
  let F : A → X := fun x => (x : X)
  let G : X → A := fun x => ⟨x, trivial⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    rfl
  have hGF : Function.RightInverse G F := by
    intro x
    rfl
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_id
  let e : A ≃ X := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

/-- **Base of the exhaustion (VERIFIED, sorry-free)**: under the
one-manifold hypotheses, either the whole space is already an arc
(`X ≃ₜ (0,1)` — the exhaustion is complete at level 0) or there is a
PROPER open arc prefix `P ≃ₜ (0,1)` (`P ≠ univ`) from which the
per-level extension can start: take an arc chart `U` of any point
(`hLoc`); if `U = univ` we are done, else `U` itself is the proper
prefix.  This is the first step of the S206 exhaustion: the recursive
growth of a compatible chain of arc prefixes either terminates (the
prefix covers the whole space — the desired chart) or continues from a
proper prefix. -/
theorem arc_or_proper_open_prefix {X : Type*} [TopologicalSpace X] [Nonempty X]
    (hLoc : LocallyIntervalChart X) :
    (Nonempty (OpenRealInterval 0 1 ≃ₜ X)) ∨
      (∃ P : Set X, IsOpen P ∧ P ≠ Set.univ ∧ P.Nonempty ∧
        Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})) := by
  classical
  let x₀ : X := Classical.choice ‹Nonempty X›
  rcases hLoc x₀ with ⟨U, hUopen, hx₀U, lo, hi, hchart⟩
  rcases hchart with ⟨e⟩
  have hlt : lo < hi := by
    let t : OpenRealInterval lo hi := e.symm ⟨x₀, hx₀U⟩
    exact lt_trans t.2.1 t.2.2
  rcases homeo_Ioo_openUnit lo hi hlt with ⟨f⟩
  by_cases hU : U = Set.univ
  · left
    exact ⟨((f.symm.trans e).trans (setEqSubtypeHomeoX hU)).trans (subtypeUnivHomeo X)⟩
  · right
    refine ⟨U, hUopen, hU, ⟨x₀, hx₀U⟩, ?_⟩
    exact ⟨f.symm.trans e⟩

/-- **Step A's per-level supply (PINNED TARGET, a `def Prop` — the proof
is the boundary attach, recorded open).**  In a connected non-compact
Hausdorff locally-interval-charted ambient, every proper open arc
prefix `P` (chart `κ`) admits an END-STRIP extension:
`EndStripExtension P κ` (an open arc-charted `V` attaching over an END
strip of `κ` with `V \ P ≠ ∅`, S234).  Iterated from
`arc_or_proper_open_prefix`'s proper prefix (excluding the two-sided
wrap by non-compactness) this is Step A of the S206 decomposition
(module doc S238); its proof is the one-sided boundary attach of
OneSidedAttach (S233 `endStripExtension_of_rawBoundary`) with the `hF`
input of iii-c (NoOscillation S236). -/
def OneManifoldPerLevelExtension (X : Type*) [TopologicalSpace X] [T2Space X] : Prop :=
  LocallyIntervalChart X → ConnectedSpace X → ¬ CompactSpace X →
    ∀ P : Set X, IsOpen P → P ≠ Set.univ →
      ∀ κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}, EndStripExtension P κ

/-! ## S209 — item (i): the exhaustion ordering — component
path-connectedness and the terminal-extension target (IN PROGRESS)

The remaining interval-side content under the S206 extraction splits
into (i) the exhaustion ORDERING and (ii) the exhaustion-to-interval
assembly.  This section opens (i): it proves the path-connectedness of
the component TYPE (needed by any end/extension argument) and records
the precise target statement of the per-step terminal extension.

**Honest analysis of (i) (per S106).**  The extension lemma as it might
be naively stated — "every proper interval-charted open prefix `P` of a
connected non-compact 1-manifold has an open arc `V` attaching
terminally (`hVend`) and extending `P`" — is NOT derivable from the
current library: the connectedness of `P ∩ V` / the absence of a second
(wrap) intersection component is exactly the content that fails on the
circle (`S¹`), and excluding it needs the very interval structure being
proved (the circularity recorded in S204).  What IS available and
verified at the generic level: the walk ORDERING of a countable open
path-connected cover over a connected ambient
(`ConnectedWalk.exists_pathConnected_open_exhaustion`: consecutive
overlap walk `e` with path-connected open prefixes `V n` nested and
exhausting), and the O-side instance
(`ComponentWalk.component_trace_walk`).  The missing link of (i) is the
per-step overlap-connectedness/terminal-attachment of the NEXT cover arc
to the prefix — the counterpart of the walk `hNW`/`hD` content, which in
the generic setting must come from a genuine one-dimensional analysis
(metric/order refinement of the cover so overlapping arcs meet
connectedly, or an end/ray argument in the non-compact ambient).  The
statements below fix the targets; the ROADMAP S209 entry records the
route and the next feasible verified sub-goals.

Content (verified, sorry-free): **`trisecantComponent_pathConnectedSpace`**
— the component type is path-connected
(`component_isPathConnected_in_O`, set-level, via
`isPathConnected_iff_pathConnectedSpace`) — the topological input of
any path/end argument in the component; and the target
**`TerminalExtensionExists`** — the precise statement of the per-step
extension (item (i)'s first existential, documented for the prover who
attacks the one-dimensional analysis).
-/

/-- The component TYPE is path-connected (the set-level
`component_isPathConnected_in_O` at type level). -/
theorem trisecantComponent_pathConnectedSpace {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    PathConnectedSpace (TrisecantComponent r c₀) := by
  exact (isPathConnected_iff_pathConnectedSpace).mp
    (component_isPathConnected_in_O h hqf hgp c₀)

/-- **Item (i)'s first existential (TARGET statement, IN PROGRESS).**
For a connected non-compact topological 1-manifold `X` (the generic
dichotomy ambient) and a proper open interval-charted prefix `P` (chart
`eP`), there is an open interval-charted arc `V` that meets `P` over a
TERMINAL interval of `eP` (`hVend`, `0 < s < 1`) and extends `P`
properly (`x ∈ V`, `x ∉ P`).  With such `V` the S207/S208 chain step
certifies `P ∪ V` as the next interval-charted prefix; iterating over
the exhaustion (S183/S160) charts every prefix.  Proof pending the
one-dimensional analysis recorded in the S209 module doc and ROADMAP. -/
def TerminalExtensionExists {X : Type*} [TopologicalSpace X] {P : Set X}
    (eP : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : Prop :=
  ∃ V : Set X, IsOpen V ∧
    ∃ eV : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V},
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      (∀ t : OpenRealInterval 0 1,
        (((eP t : {x : X // x ∈ P}) : X)) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1) ∧
      ∃ x : X, x ∈ V ∧ x ∉ P

/-- **Item (i)'s ambient hypothesis (TARGET statement).**  In a
connected non-compact topological 1-manifold, every proper open
interval-charted prefix admits a terminal extension
(`TerminalExtensionExists`) — the generic counterpart of the walk
`hNW`/`hD` content, to be supplied by the one-dimensional analysis
(cover refinement / end argument). -/
def ConnectedNoncompactOneManifold_TerminalExtension (X : Type*) [TopologicalSpace X] : Prop :=
  (∀ P : Set X, IsOpen P → P ≠ Set.univ →
    ∀ eP : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}, TerminalExtensionExists eP)

/-! ## S237 — first lemma of the independent route / iii-c bridge:
the interval chart carries every open arc prefix at finite coordinates

Per the S236 delegation decision, iii-c follows from the interval chart
once the S206 extraction lands (`noncompact_connected_oneManifold_interval`,
above): with the component chart `e : (0,1) ≃ₜ X`, every open arc prefix
`P` (chart `κ : (0,1) ≃ₜ P`) occupies a FINITE coordinate interval
`(a,b)` of the chart.  This section proves exactly that
(`prefix_coord_interval`): the coordinate real set
`chartPrefixCoord e P := val '' {t : (0,1) | e t ∈ P}` is an open
preconnected nonempty subset of `(0,1)` (the coordinate set is open and
connected — homeomorphic to `{x ∈ P}` via the chart `e`
(`Commons.Topology.Homeomorph.subtype_preimage_homeo`, L44) and to
`(0,1)` via `κ`; its real value-image is open by
`isOpenMap_coe_of_isOpen`, ArcRestrict S235), hence by the bounded shape
classification (`Commons.Analysis.RealIntervals.
open_preconnected_nonempty_subset_unit_Ioo_shape`, L45) it is `Ioo a b`
for finite `a < b` — the prefix and its boundary points lie at finite
coordinates of the chart.

This is the first lemma the independent route (and the iii-c corollary)
needs once the component chart exists: with the overlap's coordinate set
a single interval, the overlap-coordinate set `Sℝ` of the attach
statements is interval-like, and the `hF` finite structure (iii-c) and
the end strip follow immediately.  Everything here is generic topology
(any interval chart `e : (0,1) ≃ₜ X` of the whole space), verified,
sorry-free.
-/

def chartPrefixCoord {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X) (P : Set X) : Set ℝ :=
  ((↑) : OpenRealInterval 0 1 → ℝ) '' {t : OpenRealInterval 0 1 | e t ∈ P}

theorem prefix_coord_interval {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X) (P : Set X)
    (hPopen : IsOpen P) (hPne : P.Nonempty)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) :
    ∃ a b : ℝ, a < b ∧ chartPrefixCoord e P = Set.Ioo a b := by
  let T : Set (OpenRealInterval 0 1) := {t : OpenRealInterval 0 1 | e t ∈ P}
  let S : Set ℝ := chartPrefixCoord e P
  have hTopen : IsOpen T := by
    dsimp [T]
    exact e.continuous.isOpen_preimage P hPopen
  have hSval : S = ((↑) : OpenRealInterval 0 1 → ℝ) '' T := by
    dsimp [S, T, chartPrefixCoord]
  have hSopen : IsOpen S := by
    rw [hSval]
    exact isOpenMap_coe_of_isOpen (X := ℝ) (U := Set.Ioo (0 : ℝ) 1) isOpen_Ioo T hTopen
  have hTne : T.Nonempty := by
    rcases hPne with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    dsimp [T]
    rw [e.apply_symm_apply x]
    exact hx
  have hSne : S.Nonempty := by
    rw [hSval]
    exact image_nonempty.mpr hTne
  have hTpc : IsPreconnected T := by
    haveI : ConnectedSpace (OpenRealInterval 0 1) := by
      dsimp [OpenRealInterval]
      exact Subtype.connectedSpace (isConnected_Ioo (a := (0 : ℝ)) (b := 1) (by norm_num))
    have hC : Nonempty ({t : OpenRealInterval 0 1 // t ∈ T} ≃ₜ OpenRealInterval 0 1) := by
      dsimp [T]
      rcases Commons.Topology.Homeomorph.subtype_preimage_homeo
          (X := OpenRealInterval 0 1) (Y := X) e P with ⟨hA⟩
      exact ⟨hA.trans κ.symm⟩
    haveI : ConnectedSpace {t : OpenRealInterval 0 1 // t ∈ T} := by
      rcases hC with ⟨hc⟩
      exact (hc.connectedSpace_iff).mpr ‹ConnectedSpace (OpenRealInterval 0 1)›
    have hIsc : IsConnected T := (isConnected_iff_connectedSpace).mpr ‹ConnectedSpace {t : OpenRealInterval 0 1 // t ∈ T}›
    exact hIsc.2
  have hSpc : IsPreconnected S := by
    rw [hSval]
    exact IsPreconnected.image hTpc (fun t : OpenRealInterval 0 1 => (t : ℝ))
      continuous_subtype_val.continuousOn
  have hS01 : S ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    rw [hSval] at hr
    rcases hr with ⟨t, ht, rfl⟩
    exact t.2
  rcases Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape
      hS01 hSopen hSne hSpc with ⟨a, b, hab, h⟩
  refine ⟨a, b, hab, ?_⟩
  simpa [S, chartPrefixCoord] using h

/-! ## S239 — the single-interval finite structure and the coordinate-set
intersections (VERIFIED, sorry-free)

Step B of the S206 decomposition (the alignment) and the iii-c
interval-side corollary need the real-coordinate machinery of "one
interval is all you get on the line".  This section verifies three
sorry-free lemmas:

1. **`Ioo_inter_Ioo_eq`** — the intersection of two open real intervals
   is the open interval between the max of the left ends and the min of
   the right ends (`(a,b) ∩ (c,d) = (max a c, min b d)`, possibly
   empty);
2. **`chartPrefixCoord_inter`** — the coordinate real set of an
   intersection is the intersection of the coordinate real sets
   (`chartPrefixCoord e (P ∩ Q) = chartPrefixCoord e P ∩
   chartPrefixCoord e Q`: the value-coercion `(0,1) → ℝ` is injective)
   — the set-level half of "in the interval chart the overlap of two
   prefixes is the intersection of their intervals";
3. **`singleInterval_finiteStructure`** — THE no-oscillation-free `hF`:
   for ANY reals `a' b' c₀`, the part of `Ioo a' b'` to the left of `c₀`
   is a FINITE union of open intervals with upper endpoints `≤ c₀` —
   in fact a single (possibly empty) interval `Ioo a' (min b' c₀)`,
   witnessed by the one-point Finset `{(a', min b' c₀)}`.

Together with `prefix_coord_interval` (S237) these give the iii-c
corollary on the interval side: once the component chart `e : (0,1) ≃ₜ
X` exists (S206 / fleet L46), every overlap-coordinate set `Sℝ` is a
single interval, and `singleInterval_finiteStructure` supplies the `hF`
of `attach_cutting_realized` with no further analysis (the finite
structure is automatic for a single interval — no oscillation can even
occur).  The assembly `chartPrefixCoord e (P∩U) = Ioo (max a c) (min b
d)` from `prefix_coord_interval` applied to `P` and `U` and the two
lemmas above is recorded as the next step.
-/

/-- The intersection of two open real intervals is the open interval
between the max of the left ends and the min of the right ends. -/
theorem Ioo_inter_Ioo_eq {a b c d : ℝ} :
    Set.Ioo a b ∩ Set.Ioo c d = Set.Ioo (max a c) (min b d) := by
  ext x
  constructor
  · rintro ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    exact ⟨max_lt_iff.mpr ⟨ha, hc⟩, lt_min_iff.mpr ⟨hb, hd⟩⟩
  · rintro ⟨hmax, hmin⟩
    exact ⟨⟨(max_lt_iff.mp hmax).1, (lt_min_iff.mp hmin).1⟩,
      ⟨(max_lt_iff.mp hmax).2, (lt_min_iff.mp hmin).2⟩⟩

/-- The coordinate real set of an intersection is the intersection of
the coordinate real sets (the value-coercion `(0,1) → ℝ` is injective). -/
theorem chartPrefixCoord_inter {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X) (P Q : Set X) :
    chartPrefixCoord e (P ∩ Q) = chartPrefixCoord e P ∩ chartPrefixCoord e Q := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨t, ht, rfl⟩
    rcases ht with ⟨hP, hQ⟩
    exact ⟨⟨t, hP, rfl⟩, ⟨t, hQ, rfl⟩⟩
  · intro hr
    rcases hr.1 with ⟨t₁, ht₁, hv₁⟩
    rcases hr.2 with ⟨t₂, ht₂, hv₂⟩
    have hteq : t₁ = t₂ := by
      apply Subtype.ext
      exact hv₁.trans hv₂.symm
    have hQ₁ : e t₁ ∈ Q := by
      change e t₂ ∈ Q at ht₂
      rw [hteq]
      exact ht₂
    refine ⟨t₁, ⟨ht₁, hQ₁⟩, hv₁⟩

/-- **The single-interval finite structure**: for ANY real `a' b' c₀`
(an interval possibly empty, a cut point possibly anywhere), the part of
`Ioo a' b'` to the left of `c₀` is a FINITE union of open intervals with
upper endpoints `≤ c₀` — in fact a single (possibly empty) interval
`Ioo a' (min b' c₀)`, witnessed by the one-point Finset
`{(a', min b' c₀)}`.  (This is the `hF` of the attach statements in the
interval-like case: once the overlap-coordinate set is a single
interval, no-oscillation is automatic and the finite structure is
one interval.) -/
theorem singleInterval_finiteStructure (a' b' c₀ : ℝ) :
    ∃ F : Finset (ℝ × ℝ),
      Set.Ioo a' b' ∩ Set.Iio c₀ = ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧
      ∀ p ∈ F, p.2 ≤ c₀ := by
  refine ⟨{(a', min b' c₀)}, ?_, ?_⟩
  · have hEq : Set.Ioo a' b' ∩ Set.Iio c₀ = Set.Ioo a' (min b' c₀) := by
      ext x
      constructor
      · rintro ⟨⟨ha, hb⟩, hxc⟩
        exact ⟨ha, lt_min_iff.mpr ⟨hb, hxc⟩⟩
      · rintro ⟨ha, hx⟩
        have hx' := lt_min_iff.mp hx
        exact ⟨⟨ha, hx'.1⟩, hx'.2⟩
    rw [hEq]
    simp
  · intro p hp
    simp at hp
    rw [hp]
    exact min_le_right b' c₀

/-! ## S243 — the H2 COMPACT side: gate and component plumbing
(the classification itself is fleet L65, IN FLIGHT)

The compact side of the component dichotomy (H2): a compact connected
component of the trisecant set is homeomorphic to the circle.  The
generic classification has been DISPATCHED to the fleet as commons L65
(`Commons.Topology.OneManifold.compact_connected_oneManifold_circle`,
pure form, IN FLIGHT — the compact analogue of L46).  This section fixes
the component-side statements and verifies the plumbing that does NOT
need L65:

1. **`TrisecantComponentCompactSide`** — the gate statement: a compact
   component (its set is compact) is homeomorphic to the circle
   (`Circle ≃ₜ TrisecantComponent r c₀`), mirroring
   `TrisecantComponentIntervalSide`;
2. **`trisecantComponent_compactSpace`** (VERIFIED, sorry-free) — the
   set-level-to-type bridge of the compact direction:
   `IsCompact (connectedComponent c₀ : Set (OSub r)) ⟹
   CompactSpace (TrisecantComponent r c₀)` (`isCompact_iff_compactSpace`);
3. **`trisecantComponent_compactSide`** — the ASSEMBLED gate theorem
   (recorded; to be completed the moment L65 lands, exactly as
   `trisecantComponent_intervalSide` was completed by L46): the
   component is T2/second-countable/nonempty (S152), locally
   interval-charted (`component_local_interval`), connected (S205),
   compact by (2), and the L65 classification supplies
   `Nonempty (Circle ≃ₜ TrisecantComponent r c₀)`.

Together with the interval side (S206/S242, closed) this completes the
component dichotomy: each component of the trisecant set is an open
interval (non-compact side) or a circle (compact side) — the input of
the winding/obstruction analysis (Layer-C brick (c)) and the
non-separating-arc construction.
-/

/-- **The dichotomy's compact-case gate (target statement).**  If the
component of `c₀` is compact (as a set) then it is homeomorphic to the
circle: `Circle ≃ₜ TrisecantComponent r c₀`.  (Proof = the generic
compact connected-1-manifold classification — fleet L65,
`Commons.Topology.OneManifold.compact_connected_oneManifold_circle` —
instantiated on `TrisecantComponent r c₀` via
`trisecantComponent_compactSpace`; recorded as the next completion,
mirroring the S206/S242 interval-side completion.) -/
def TrisecantComponentCompactSide (r : ℝ → Space) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) : Prop :=
  IsCompact (connectedComponent c₀ : Set (OSub r)) →
    Nonempty (Circle ≃ₜ TrisecantComponent r c₀)

/-- **The compact-direction set-to-type bridge (VERIFIED)**: if the
component set is compact then the component TYPE is compact
(`isCompact_iff_compactSpace` on the component set, whose subtype is
`TrisecantComponent r c₀`). -/
theorem trisecantComponent_compactSpace {r : ℝ → Space} (c₀ : OSub r) :
    IsCompact (connectedComponent c₀ : Set (OSub r)) →
      CompactSpace (TrisecantComponent r c₀) := by
  intro hcmp
  simpa [TrisecantComponent] using (isCompact_iff_compactSpace.mp hcmp)

/-! ## S244 — the interval-branch obstruction statement: interval
components carry no essential loops (VERIFIED reduction; contractibility
sub-lemma recorded)

Layer-C's obstruction analysis needs: the interval-side components of the
trisecant set (S242: `≃ₜ (0,1)`) cannot host the winding that makes `O`
obstruct every non-separating arc — only circular components wind
(L65/H2).  This section fixes the interval-branch statement and verifies
the reduction that S242 gives:

1. **`LoopsTrivial X`** — every continuous circle map into `X` is
   null-homotopic (no essential loops);
2. **`nullHomotopic_iff_comp_homeo`** (VERIFIED) — null-homotopy
   transfers across a homeomorphism in both directions (compose with the
   homeo / with its inverse);
3. **`LoopsTrivial_of_intervalChart`** (VERIFIED) — given the interval
   chart `e : (0,1) ≃ₜ X` (the S242 output), loop-triviality reduces to
   `LoopsTrivial (ORI 0 1)`;
4. **`TrisecantIntervalComponentLoopsTrivial`** — the interval-branch
   gate on the component: `LoopsTrivial (TrisecantComponent r c₀)`.

The remaining sub-lemma — `LoopsTrivial (ORI 0 1)` (contractibility of
the open interval: `ORI ≃ₜ ℝ` by `homeo_real_openUnit` and `ℝ` is
`ContractibleSpace`, with the straight-line null homotopy transported
back) — is recorded as the next stone; when it lands, the interval
branch of the obstruction (no essential loops in interval components) is
closed by `LoopsTrivial_of_intervalChart` + the S242 chart.
-/

/-- **Interval-branch obstruction statement (generic)**: every continuous
circle map into `X` is null-homotopic — the space carries no essential
loops (so no circular winding can live in it).  The interval components
of the trisecant set (S242: `X ≃ₜ (0,1)`) satisfy this; circular
components (L65/H2) do not. -/
def LoopsTrivial (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ γ : C(Circle, X), NullHomotopic γ

/-- **Null-homotopy transfers across a homeomorphism (both directions,
VERIFIED)**: a circle map into `X` is null-homotopic iff its image under
a homeomorphism `k : X ≃ₜ Y` is null-homotopic.  (Forward:
`nullHomotopic_of_nullHomotopic_comp`; backward: compose the null
homotopy of `k ∘ γ` with `k.symm`, whose composition with `k` is the
identity and whose constant is `k.symm c`.) -/
lemma nullHomotopic_iff_comp_homeo {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (k : X ≃ₜ Y) {γ : C(Circle, X)} :
    NullHomotopic γ ↔ NullHomotopic ((⟨fun x => k x, k.continuous⟩ : C(X, Y)).comp γ) := by
  constructor
  · intro h
    exact nullHomotopic_of_nullHomotopic_comp (⟨fun x => k x, k.continuous⟩ : C(X, Y)) h
  · intro h
    rcases h with ⟨c, H⟩
    rcases H with ⟨Hγ⟩
    let kC : C(X, Y) := ⟨fun x => k x, k.continuous⟩
    let ksymm : C(Y, X) := ⟨fun y => k.symm y, k.symm.continuous⟩
    let Hraw : (ksymm.comp (kC.comp γ)).Homotopy (ksymm.comp (ContinuousMap.const Circle c)) :=
      (ContinuousMap.Homotopy.refl ksymm).comp Hγ
    have hident : ksymm.comp (kC.comp γ) = γ := by
      ext x
      exact k.symm_apply_apply (γ x)
    have hconst : ksymm.comp (ContinuousMap.const Circle c) =
        ContinuousMap.const Circle (k.symm c) := by
      ext x
      rfl
    refine ⟨k.symm c, ?_⟩
    exact ⟨by simpa [hident, hconst] using Hraw⟩

/-- **The S242 reduction (VERIFIED)**: if the space admits the interval
chart `e : (0,1) ≃ₜ X` (the S242 output for an interval component), then
loop-triviality reduces to loop-triviality of the model interval
`(0,1)`: `LoopsTrivial (ORI 0 1) → LoopsTrivial X` (transport the null
homotopy through the chart by `nullHomotopic_iff_comp_homeo`).  The
remaining sub-lemma — `LoopsTrivial (ORI 0 1)` (the open interval is
contractible: `ORI ≃ₜ ℝ` via `homeo_real_openUnit` and `ℝ` is
`ContractibleSpace`) — is the interval branch's contractibility content,
recorded as the next stone. -/
theorem LoopsTrivial_of_intervalChart {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X) (hI : LoopsTrivial (OpenRealInterval 0 1)) :
    LoopsTrivial X := by
  intro γ
  let ksymm : C(X, OpenRealInterval 0 1) :=
    ⟨fun x => e.symm x, e.symm.continuous⟩
  have hloop : NullHomotopic (ksymm.comp γ) := hI (ksymm.comp γ)
  exact (nullHomotopic_iff_comp_homeo e.symm).mpr hloop

/-- **The interval-branch gate on the trisecant component (statement)**:
every continuous circle map into an interval-side component is
null-homotopic — an interval component carries no essential loops, so no
circular winding can live in it (the obstruction/winding analysis of
Layer C consumes this: only circular components can obstruct).  Given
the interval-side chart `e` (S242, `trisecantComponent_intervalSide`),
`LoopsTrivial_of_intervalChart` reduces this to `LoopsTrivial (ORI 0
1)`; the assembly is complete once the contractibility sub-lemma
(`LoopsTrivial (ORI 0 1)`, via `homeo_real_openUnit` to `ℝ` +
`ContractibleSpace ℝ`) lands. -/
def TrisecantIntervalComponentLoopsTrivial (r : ℝ → Space)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) : Prop :=
  LoopsTrivial (TrisecantComponent r c₀)

/-! ## S244 (completion) — the interval branch CLOSED: `LoopsTrivial
(ORI 0 1)` proved and the trisecant gate assembled (VERIFIED, sorry-free)

The recorded sub-lemma of S244 lands:

1. **`LoopsTrivial_openUnit`** (VERIFIED) — the open unit interval has
   no essential loops: transport the loop to `ℝ` through
   `homeo_real_openUnit` (`ℝ ≃ₜ (0,1)`), get null-homotopy of the
   `ℝ`-loop from `ContractibleSpace ℝ` (`id_nullhomotopic` +
   `ContinuousMap.Nullhomotopic.comp_left`, Mathlib), and pull the null
   homotopy back through the inverse of the homeo
   (`rH.apply_symm_apply`);
2. **`trisecantIntervalComponent_loopsTrivial`** (VERIFIED) — THE
   interval branch of the Layer-C obstruction is CLOSED: under the
   non-compact hypothesis, every interval-side component of the
   trisecant set carries no essential loops
   (`TrisecantIntervalComponentLoopsTrivial`): the S242 interval-side
   gate (`trisecantComponent_intervalSide`) supplies the chart
   `e : (0,1) ≃ₜ TrisecantComponent r c₀`, and
   `LoopsTrivial_of_intervalChart e` + `LoopsTrivial_openUnit` conclude.

With this, "only circular components obstruct" is established on the
interval side: interval components cannot host the winding that makes
`O` obstruct every non-separating arc — the obstruction analysis reduces
to the circular (compact) components, whose classification is fleet L65
(IN FLIGHT, staged in S243).
-/

/-- **The open unit interval has no essential loops (VERIFIED)**: every
continuous circle map into `(0,1)` is null-homotopic.  Proof: transport
to `ℝ` through `homeo_real_openUnit` (`ℝ ≃ₜ (0,1)`); maps into `ℝ` are
null-homotopic because `ℝ` is `ContractibleSpace`
(`id_nullhomotopic` + `ContinuousMap.Nullhomotopic.comp_left`, Mathlib);
pull the null homotopy back through the inverse of the homeo. -/
theorem LoopsTrivial_openUnit : LoopsTrivial (OpenRealInterval 0 1) := by
  intro γ
  rcases homeo_real_openUnit with ⟨rH⟩
  let γℝ : C(Circle, ℝ) := ⟨fun x => rH.symm (γ x), rH.symm.continuous.comp γ.continuous⟩
  have hid : ContinuousMap.Nullhomotopic (ContinuousMap.id ℝ) := id_nullhomotopic ℝ
  have hγℝ : ContinuousMap.Nullhomotopic γℝ := by
    have hc : (ContinuousMap.id ℝ).comp γℝ = γℝ := by
      ext x
      rfl
    have h := (ContinuousMap.Nullhomotopic.comp_left (f := (ContinuousMap.id ℝ)) hid (g := γℝ))
    simpa [hc] using h
  rcases hγℝ with ⟨c, hHom⟩
  rcases hHom with ⟨Hγ⟩
  let rHC : C(ℝ, OpenRealInterval 0 1) := ⟨fun x => rH x, rH.continuous⟩
  have Hback : (rHC.comp γℝ).Homotopy (rHC.comp (ContinuousMap.const Circle c)) :=
    (ContinuousMap.Homotopy.refl rHC).comp Hγ
  have hident : rHC.comp γℝ = γ := by
    ext x
    dsimp [γℝ, rHC]
    exact congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ)) (rH.apply_symm_apply (γ x))
  have hconst : rHC.comp (ContinuousMap.const Circle c) =
      ContinuousMap.const Circle (rH c) := by
    ext x
    rfl
  refine ⟨rH c, ?_⟩
  exact ⟨by simpa [hident, hconst] using Hback⟩

/-- **The interval branch of the obstruction CLOSED (VERIFIED)**: every
interval-side component of the trisecant set carries no essential loops
(`LoopsTrivial`): the S242 interval-side gate supplies the chart
`e : (0,1) ≃ₜ TrisecantComponent r c₀` and `LoopsTrivial_of_intervalChart
e` + `LoopsTrivial_openUnit` give the conclusion. -/
theorem trisecantIntervalComponent_loopsTrivial {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    (hnc : ¬ IsCompact (connectedComponent c₀ : Set (OSub r))) :
    TrisecantIntervalComponentLoopsTrivial r hqf hgp c₀ := by
  have hchart : Nonempty (OpenRealInterval 0 1 ≃ₜ TrisecantComponent r c₀) :=
    trisecantComponent_intervalSide h hqf hgp c₀ hnc
  rcases hchart with ⟨e⟩
  unfold TrisecantIntervalComponentLoopsTrivial
  exact LoopsTrivial_of_intervalChart e LoopsTrivial_openUnit

/-! ## S245 — the compact-side completion drafts and the circular winding
skeleton

While the compact classification (fleet L65,
`Commons.Topology.OneManifold.compact_connected_oneManifold_circle`) is
in flight (its child is committing the arc-branch dichotomy pieces:
`arc_branch_left_dichotomy`, `arc_branch_right_dichotomy`,
`arc_extension_or_compact`, `oneManifold_dichotomy`, …), this section
fixes the component-side drafts that do NOT need L65:

1. **`trisecantComponent_compactSide_of_circleClassification`**
   (VERIFIED) — the assembly TAIL: given the circle classification
   `Nonempty (Circle ≃ₜ TrisecantComponent r c₀)` (the L65 output), the
   compact-case gate `TrisecantComponentCompactSide` holds;
2. **`trisecantComponent_compactSide_premises`** (VERIFIED) — the
   component PREMISES for the L65 call: under
   `IsCompact (connectedComponent c₀ : Set (OSub r))`,
   `LocallyIntervalChart ∧ ConnectedSpace ∧ CompactSpace` of the
   component (instances S152, `component_local_interval`, S205, and the
   S243 compact bridge `trisecantComponent_compactSpace`);
3. **the L65 final body (recorded, 3 lines)** — the moment L65 lands,
   `trisecantComponent_compactSide` is:
   `intro hcmp; classical; haveI … S152 instances; rcases
   (trisecantComponent_compactSide_premises h hqf hgp c₀ hcmp) with
   ⟨hLoc, hconn, hCmpT⟩; rcases (Commons.Topology.OneManifold.
   compact_connected_oneManifold_circle (X := TrisecantComponent r c₀)
   hLoc hconn hCmpT) with ⟨e⟩; exact ⟨e⟩`.
   Together with the interval side (S206/S242/S244) this closes the
   component dichotomy: every trisecant component is an open interval or
   a circle.
-/


/-- **Compact-case assembly TAIL (VERIFIED)**: given the circle
classification of the component (`Nonempty (Circle ≃ₜ TrisecantComponent
r c₀)` — the L65 output), the compact-case gate holds.  (The full
`trisecantComponent_compactSide` theorem body — S245 item (3) — is the
three-line composition of the S152/S205/S243 premises with the L65 call,
appended the moment L65 lands.) -/
theorem trisecantComponent_compactSide_of_circleClassification {r : ℝ → Space}
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    (hcircle : Nonempty (Circle ≃ₜ TrisecantComponent r c₀)) :
    TrisecantComponentCompactSide r hqf hgp c₀ := by
  intro hcmp
  exact hcircle

/-- **Component premises for the L65 call (VERIFIED)**: under the
set-level compactness of the component, the component TYPE is
`LocallyIntervalChart` (from `component_local_interval`), `ConnectedSpace`
(S205) and `CompactSpace` (S243 `trisecantComponent_compactSpace`); the
T2/second-countable/nonempty instances are S152.  This is exactly the
hypothesis list of `Commons.Topology.OneManifold.
compact_connected_oneManifold_circle` (L65). -/
theorem trisecantComponent_compactSide_premises {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    (hcmp : IsCompact (connectedComponent c₀ : Set (OSub r))) :
    LocallyIntervalChart (TrisecantComponent r c₀) ∧
      ConnectedSpace (TrisecantComponent r c₀) ∧
      CompactSpace (TrisecantComponent r c₀) := by
  classical
  haveI : T2Space (TrisecantComponent r c₀) := component_t2Space c₀
  haveI : SecondCountableTopology (TrisecantComponent r c₀) := component_secondCountableTopology c₀
  haveI : Nonempty (TrisecantComponent r c₀) := ⟨⟨c₀, mem_connectedComponent⟩⟩
  have hLoc : LocallyIntervalChart (TrisecantComponent r c₀) := by
    dsimp [LocallyIntervalChart]
    intro x
    rcases component_local_interval h hqf hgp c₀ x with ⟨U, hUopen, hxU, lo, hi, hhomeo⟩
    refine ⟨U, hUopen, hxU, lo, hi, ?_⟩
    simpa using hhomeo
  have hCmpT : CompactSpace (TrisecantComponent r c₀) := trisecantComponent_compactSpace c₀ hcmp
  exact ⟨hLoc, trisecantComponent_connectedSpace c₀, hCmpT⟩


/-! ## S245(b) — the circular winding skeleton: statement split, chart
assumptions, case decomposition (statements; the winding content is
Layer-C brick (c), deferred)

With the dichotomy closed (interval side DONE; compact side = L65 +
`trisecantComponent_compactSide`), the Layer-C obstruction analysis
reduces to CIRCULAR components: an embedded circle component `C ⊆
trisecantSet r` of the band that obstructs every non-separating arc must
wind once or twice around the band's core.  Skeleton (recorded):

- **`IsCircleEmbedding C`** — `C` is the image of an embedded circle
  (`SimpleClosedCurve OpenMobius`);
- **`CircularTrisecantComponent r C`** — `C` is an embedded circle in
  the band, contained in the trisecant set `O`, and ESSENTIAL (not
  null-homotopic) — an obstructing candidate (interval components were
  excluded by S244: `trisecantIntervalComponent_loopsTrivial` makes
  every interval component null-homotopic, so only essential circular
  components can obstruct);
- the two winding predicates `WindsOnce C`, `WindsTwice C` (Layer-C
  brick (c)) measure the ambient class of `C` in the band:
  `WindsOnce` = odd lift-monodromy on the ordered double cover (the
  lifted lift interchanges the two sheets, endpoints advance by a half
  period with a swap), `WindsTwice` = even/closed lift (endpoints each
  wind once).  CHART ASSUMPTION: `C ≃ₜ Circle` via the compact
  component classification (L65 + `trisecantComponent_compactSide`),
  and the winding is read on the core-circle parametrisation
  (`Pi1Mobius`/`Pi1OpenMobius`: `coreFactor : AddCircle period → OpenMobius`,
  π₁ ≅ ℤ);
- the CASE DECOMPOSITION (the obstruction dichotomy): if a circular
  component obstructs all non-separating arcs then it is essential
  (done above) and winds once or twice —
  `ObstructingCircleWindsOnceOrTwice` (the contrapositive
  "non-essential or winds 0 ⇒ a non-separating arc avoiding O exists"
  feeds Layer B's disk construction via `classBandArc_disk_bounds`);
  the two contradictions close the obstruction: ONCE ⇒ the middle family
  advances by a half-period per circuit with the sheets swapped — the
  jump/continuity contradiction (the once-winding jump analysis);
  TWICE ⇒ the middle family is surjective over the parameter circle
  (`knotParam_surj_of_lift_advance`, ParameterWinding S78) contradicting
  `TrisecantStructure.exists_uncovered_middle` (the extremal-point /
  lemma-compact argument).  Both contradictions were scoped in ROADMAP
  S112; the two target theorems (ROADMAP S60 names):
  `no_onceWinding_component` and `no_twiceWinding_component`, plus the
  assembly `obstruction_contradiction_of_circular` — recorded, content
  = Layer-C brick (c).
-/


/-- An embedded circle in the band: `C` is the image of a simple closed
curve (`SimpleClosedCurve OpenMobius`). -/
def IsCircleEmbedding (C : Set OpenMobius) : Prop :=
  ∃ γ : SimpleClosedCurve OpenMobius, C = γ.image

/-- A circular trisecant component: an embedded circle in the band,
contained in the trisecant set `O`, and ESSENTIAL (its parametrisation
is not null-homotopic) — an obstructing candidate.  (Interval components
were excluded in S244 (`trisecantIntervalComponent_loopsTrivial`), so
only essential circular components can obstruct every non-separating
arc.) -/
def CircularTrisecantComponent (r : ℝ → Space) (C : Set OpenMobius) : Prop :=
  IsCircleEmbedding C ∧ C ⊆ trisecantSet r ∧
    ∃ γ : SimpleClosedCurve OpenMobius, γ.image = C ∧ γ.IsEssential

/-! ## S246 — the ONCE branch: the real-analysis avatar and the pinned
reduction (VERIFIED avatar; the winding semantics are Layer-C brick (c),
deferred)

Per the S245(b) decomposition, `no_onceWinding_component` and
`no_twiceWinding_component` are the two case contradictions of the
circular obstruction.  This section fixes what is provable NOW on the
ONCE branch:

- **`no_periodic_advance`** (VERIFIED) — the real-analysis avatar of the
  ONCE jump: a real function cannot be simultaneously `T`-periodic (a
  well-defined function on the component circle `AddCircle T` — the
  middle IS a genuine function of the component parameter under
  `AtMostOneMiddle`, `quadrisecantFree_iff_atMostOneMiddle`) and advance
  by a non-zero `p` per circuit (`g(t + T) = g t + p` at `t = 0` gives
  `p = 0`).  The ONCE data give a half-period advance (`p = halfPeriod ≠
  0`, `halfPeriod_pos`); the formal ONCE contradiction combines this with
  the circle-map DEGREE fact (open): a genuine circle-valued function has
  INTEGER lift advance, so a half-period advance is impossible — or the
  middle is ill-defined, giving two middles on some class, contradicting
  QuadrisecantFree.  The degree fact (continuous `C(AddCircle T,
  AddCircle period)` maps have an integer-valued lift-advance over a
  circuit) is the missing formal object of the ONCE branch (candidate
  fleet dispatch once the covering/degree theory is pinned; recorded in
  ROADMAP S112-C as the hardest remaining analytic piece).

The TWICE branch needs no new analysis beyond its family-production
lemma (S78 assembled the contradiction).  Both targets are recorded in
the S245(b) doc with their ROADMAP S60 names; they become concrete
theorems once the winding predicates `WindsOnce`/`WindsTwice` are
defined from the ordered-double-cover measurement (Layer-C brick (c)).
-/

/-- **The ONCE-branch real-analysis avatar (VERIFIED)**: a real function
cannot be simultaneously `T`-periodic (a well-defined function on the
circle `AddCircle T` — the middle is a genuine function of the component
parameter under `AtMostOneMiddle`) and advance by a non-zero amount `p`
per circuit (the half-period advance of the ONCE lift).  Proof: evaluate
at `t = 0`: `g T = g 0` (periodicity) and `g T = g 0 + p` (advance), so
`p = 0`, contradicting `p ≠ 0`.  This is the analytic core of the ONCE
jump: the formal ONCE contradiction will combine it with the circle-map
degree fact (a genuine circle-valued function has INTEGER lift advance,
so a half-period advance forces the middle to be ill-defined — two
middles — contradicting `quadrisecantFree_iff_atMostOneMiddle`). -/
theorem no_periodic_advance {g : ℝ → ℝ} {T p : ℝ} (hp : p ≠ 0)
    (hper : ∀ t : ℝ, g (t + T) = g t)
    (hadv : ∀ t : ℝ, g (t + T) = g t + p) : False := by
  have h0 := hper 0
  have h1 := hadv 0
  rw [h0] at h1
  have hp0 : p = 0 := by linarith
  exact hp hp0

/-! ## S248 — the TWICE family-production endpoint: precise statement,
bridge and assembly (VERIFIED, sorry-free)

The geometric family-production lemma of the TWICE branch (S247 doc):
from TWICE circular-component data produce the advancing genuine-middle
family consumed by `twiceWinding_middle_contradiction`.  This section
fixes the statement precisely and verifies the two pieces that are pure
assembly:

1. **`MiddlePointsOnClass_subset_MiddleCovered`** (VERIFIED) — the
   bridge: a middle parameter of a secant CLASS is a covered middle
   parameter (`∈ MiddleCovered r`), witnessed by the representative's
   endpoints `p.1.1 ≠ p.1.2` — this turns the component's unique-middle
   selection into the `hmid` hypothesis of the TWICE contradiction;
2. **`no_twiceWinding_data`** (VERIFIED) — THE production endpoint: given
   the TWICE circular-component data — the component circle chart
   `χ : AddCircle T ≃ₜ TrisecantComponent r c₀` (L65 +
   `trisecantComponent_compactSide`), the continuous unique-middle
   selection `μ` on the component (`μ z ∈ MiddlePointsOnClass r (z : OSub
   r)`), and a real lift `G` of `μ ∘ χ` advancing a FULL period per
   circuit — the TWICE contradiction closes by pure assembly
   (`S247.twiceWinding_middle_contradiction` fed by the bridge).

The constituent facts the geometric development must supply (each an
itemized separate piece, recorded): (i) the component circle chart `χ` —
fleet L65 (IN FLIGHT) + `trisecantComponent_compactSide` (S245,
recorded three-line body); (ii) the continuous unique-middle selection
`μ` on the component with `μ z ∈ MiddlePointsOnClass r (z : OSub r)` —
from the O-structure (the Milestone-2 middle-section continuity,
recorded) plus `quadrisecantFree_iff_atMostOneMiddle`; (iii) the TWICE
measurement giving the full-period advancing lift `G` compatible with
`μ ∘ χ` (the winding measurement of Layer-C brick (c)).  Once (i)–(iii)
exist, the TWICE branch is fully assembled by `no_twiceWinding_data`.
-/

/-- **The class-middle ⊆ covered-middle bridge (VERIFIED)**: a middle
parameter of a secant CLASS (a representative chord's strict middle) is a
covered middle parameter (`∈ MiddleCovered r`): the representative's
endpoints `p.1.1 ≠ p.1.2` witness the chord.  This is the fact that
turns the component's unique-middle selection into the `hmid` hypothesis
of the TWICE contradiction (S247). -/
theorem MiddlePointsOnClass_subset_MiddleCovered {r : ℝ → Space} (c : OpenMobius) :
    MiddlePointsOnClass r c ⊆ MiddleCovered r := by
  intro m hm
  rcases (mem_MiddlePointsOnClass_iff r c m).mp hm with ⟨p, hp, hmi⟩
  exact (mem_MiddleCovered_iff r m).mpr ⟨p.1.1, p.1.2, p.2, hmi⟩

/-- **The geometric family-production endpoint (VERIFIED, sorry-free)**:
given the TWICE circular-component data — the component circle chart
`χ : AddCircle T ≃ₜ TrisecantComponent r c₀` (from L65 +
`trisecantComponent_compactSide`), the continuous unique-middle
selection `μ` on the component (`μ z ∈ MiddlePointsOnClass r (z : OSub
r)`), and a real lift `G` of the composite `μ ∘ χ` advancing a FULL
period per circuit (`G (t + T) = G t + period`) — the TWICE
contradiction closes by pure assembly: `S247.twiceWinding_middle_contradiction`
fed by the bridge `MiddlePointsOnClass_subset_MiddleCovered` (each `G`-
value is the middle of its class, hence middle-covered).  This is the
whole content of the family-production lemma: the constituent facts are
exactly the hypotheses below (each a separate geometric development,
itemized in the doc): (i) the component circle chart `χ` — L65 (in
flight) + `trisecantComponent_compactSide`; (ii) the continuous
unique-middle selection `μ` on the component and its membership in
`MiddlePointsOnClass` (from the O-structure and
`quadrisecantFree_iff_atMostOneMiddle`); (iii) the TWICE measurement
giving the full-period advancing lift `G` compatible with `μ ∘ χ` (the
winding measurement of Layer-C brick (c)). -/
theorem no_twiceWinding_data {r : ℝ → Space} (h : IsSmoothKnot r)
    (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    (μ : TrisecantComponent r c₀ → AddCircle period) (hμc : Continuous μ)
    (hμ : ∀ z : TrisecantComponent r c₀,
      μ z ∈ MiddlePointsOnClass r ((z : OSub r) : OpenMobius))
    {G : ℝ → ℝ} (hG : Continuous G)
    (hadv : ∀ t : ℝ, G (t + T) = G t + period)
    (hcompat : ∀ t : ℝ, (G t : AddCircle period) = μ (χ (t : AddCircle T))) :
    False := by
  exact twiceWinding_middle_contradiction h hT hG hadv (by
    intro t
    rw [hcompat t]
    exact MiddlePointsOnClass_subset_MiddleCovered (r := r)
      (((χ (t : AddCircle T) : TrisecantComponent r c₀) : OSub r) : OpenMobius)
      (hμ (χ (t : AddCircle T))))

/-! ## S249 (completion) — the COMPACT side CLOSED: `trisecantComponent_compactSide`
(VERIFIED, sorry-free) — fleet L65 landed

The recorded S243/S245 three-line body is now real: the compact
classification `Commons.Topology.OneManifold.compact_connected_oneManifold_circle`
(fleet L65) landed, and this section closes the compact side of the
component dichotomy:

1. **`compact_connected_oneManifold_circle_local`** (VERIFIED) — the
   bundled-`LocallyIntervalChart` local bridge mirroring the interval-side
   wrapper (`simpa [LocallyIntervalChart, OpenRealInterval]` transports the
   L65 pure-form hypothesis list to the bundled form);
2. **`trisecantComponent_compactSide`** (VERIFIED) — THE compact-case gate
   ASSEMBLED: under `IsCompact (connectedComponent c₀ : Set (OSub r))` the
   component TYPE is `Nonempty (Circle ≃ₜ TrisecantComponent r c₀)` — the
   S152/S205/S243 premises (`trisecantComponent_compactSide_premises`) feed
   the L65 classification.  Together with the interval side
   (`trisecantComponent_intervalSide`, S206/S242) this CLOSES the component
   dichotomy: every connected component of the trisecant set is an open
   interval (non-compact side) or a circle (compact side).
-/

/-- **The compact-case local bridge (VERIFIED)**: a connected compact
second-countable Hausdorff locally interval-charted space is
homeomorphic to the circle — the bundled-`LocallyIntervalChart` version
of fleet L65 (`Commons.Topology.OneManifold.
compact_connected_oneManifold_circle`), mirroring the interval-side
wrapper `noncompact_connected_oneManifold_interval`. -/
theorem compact_connected_oneManifold_circle_local {X : Type*} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] [Nonempty X]
    (hLoc : LocallyIntervalChart X) (hconn : ConnectedSpace X) (hcmp : CompactSpace X) :
    Nonempty (Circle ≃ₜ X) := by
  simpa [LocallyIntervalChart, OpenRealInterval] using
    (Commons.Topology.OneManifold.compact_connected_oneManifold_circle (X := X) hLoc hconn hcmp)

/-- **The compact-case gate theorem (ASSEMBLED, VERIFIED)**: a compact
connected component of the trisecant set is homeomorphic to the circle
`Circle ≃ₜ TrisecantComponent r c₀` — the S243 `TrisecantComponentCompactSide`
gate realized: the component premises (S152 T2/second-countable/nonempty,
`component_local_interval` locally interval-charted, S205 connected, S243
compact bridge) feed the fleet L65 classification.  With the interval side
(`trisecantComponent_intervalSide`) this closes the component dichotomy:
each component of `O` is an open interval (non-compact) or a circle
(compact). -/
theorem trisecantComponent_compactSide {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    (hcmp : IsCompact (connectedComponent c₀ : Set (OSub r))) :
    Nonempty (Circle ≃ₜ TrisecantComponent r c₀) := by
  classical
  haveI : T2Space (TrisecantComponent r c₀) := component_t2Space c₀
  haveI : SecondCountableTopology (TrisecantComponent r c₀) := component_secondCountableTopology c₀
  haveI : Nonempty (TrisecantComponent r c₀) := ⟨⟨c₀, mem_connectedComponent⟩⟩
  rcases (trisecantComponent_compactSide_premises h hqf hgp c₀ hcmp) with ⟨hLoc, hconn, hCmpT⟩
  exact compact_connected_oneManifold_circle_local hLoc hconn hCmpT


/-! ## S250 — compact components are embedded circles of the band
(VERIFIED, sorry-free)

With the compact classification closed (S249), this section connects the
dichotomy to the Layer-C winding skeleton (S245(b)): a circle-charted
component `TrisecantComponent r c₀` is realized as a `SimpleClosedCurve
OpenMobius` (an injective continuous circle map) whose image is exactly the
set-level component `(fun s : OSub r => (s : OpenMobius)) '' (connectedComponent
c₀ : Set (OSub r))`:

1. **`component_simpleClosedCurve_of_circleHomeo`** (VERIFIED) — given the
   circle homeo `χ : Circle ≃ₜ TrisecantComponent r c₀` (the S249 output),
   the composite of `χ` with the two subtype projections is injective
   (two `Subtype.ext`s from equality of the `OpenMobius` values) and
   continuous, with image exactly the component val-set (forward: each
   `χ z` witnesses with its component membership; backward:
   `χ.symm ⟨s, hs⟩` and `χ.apply_symm_apply`);
2. **`compact_component_isCircleEmbedding`** (VERIFIED) — a compact
   component (set-level) is `IsCircleEmbedding` of its val-image set:
   `trisecantComponent_compactSide` (S249) + (1).

This is the `IsCircleEmbedding` half of the S245(b) `CircularTrisecantComponent`
vocabulary; the essentiality conjunct (`IsEssential`) and the winding
measurement (once/twice) are the Layer-C brick-(c) content that consumes it.
-/

/-- **A circle-charted component is an embedded circle of the band (S250)**:
given the circle homeo `χ : Circle ≃ₜ TrisecantComponent r c₀` (the S249
compact-side output), the composite of `χ` with the subtype projections is an
injective continuous circle map into `OpenMobius` (a `SimpleClosedCurve`)
whose image is exactly the set-level component
`(fun s : OSub r => (s : OpenMobius)) '' (connectedComponent c₀ : Set (OSub r))`. -/
theorem component_simpleClosedCurve_of_circleHomeo {r : ℝ → Space} (c₀ : OSub r)
    (χ : Circle ≃ₜ TrisecantComponent r c₀) :
    ∃ γ : SimpleClosedCurve OpenMobius,
      γ.image = (fun s : OSub r => (s : OpenMobius)) '' (connectedComponent c₀ : Set (OSub r)) := by
  let f : C(Circle, OpenMobius) :=
    ⟨fun z : Circle => (((χ z : TrisecantComponent r c₀) : OSub r) : OpenMobius),
      (continuous_subtype_val.comp continuous_subtype_val).comp χ.continuous⟩
  have hinj : Function.Injective f := by
    intro z w hzw
    apply χ.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hzw
  refine ⟨⟨f, hinj⟩, ?_⟩
  unfold SimpleClosedCurve.image
  ext c
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(χ z : TrisecantComponent r c₀), (χ z : TrisecantComponent r c₀).2, ?_⟩
    rfl
  · rintro ⟨s, hs, hc⟩
    refine ⟨χ.symm ⟨s, hs⟩, ?_⟩
    calc
      (((χ (χ.symm ⟨s, hs⟩) : TrisecantComponent r c₀) : OSub r) : OpenMobius)
          = (((⟨s, hs⟩ : TrisecantComponent r c₀) : OSub r) : OpenMobius) := by
            rw [χ.apply_symm_apply ⟨s, hs⟩]
      _ = (s : OpenMobius) := by rfl
      _ = c := by exact hc

/-- **A compact component of the trisecant set is an embedded circle of the
band (S250)**: `trisecantComponent_compactSide` (S249) supplies the circle
homeo and `component_simpleClosedCurve_of_circleHomeo` realizes it as a
`SimpleClosedCurve OpenMobius` whose image is the component's set-level
val-image. -/
theorem compact_component_isCircleEmbedding {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    (hcmp : IsCompact (connectedComponent c₀ : Set (OSub r))) :
    IsCircleEmbedding ((fun s : OSub r => (s : OpenMobius)) '' (connectedComponent c₀ : Set (OSub r))) := by
  rcases trisecantComponent_compactSide h hqf hgp c₀ hcmp with ⟨χ⟩
  rcases component_simpleClosedCurve_of_circleHomeo c₀ χ with ⟨γ, hγ⟩
  unfold IsCircleEmbedding
  refine ⟨γ, ?_⟩
  exact hγ.symm


/-! ## S251 — the component dichotomy in disjunctive form + the interval
components as embedded open arcs (VERIFIED, sorry-free)

With both sides closed (S242 interval, S249 compact, S250 circle
realization), this section adds the two closing corollaries:

1. **`trisecantComponent_dichotomy`** (VERIFIED) — the disjunctive form of
   the component classification: every connected component of the
   trisecant set (`TrisecantComponent r c₀`) is homeomorphic to the open
   unit interval or to the circle (`by_cases` on the set-level compactness
   of the component feeds `trisecantComponent_intervalSide` /
   `trisecantComponent_compactSide`);
2. **`component_arc_of_intervalHomeo`** (VERIFIED) — the interval-side
   mirror of `component_simpleClosedCurve_of_circleHomeo` (S250): an
   interval-charted component is an embedded open arc of the band — an
   injective continuous `(0,1)`-map whose range is the component val-set
   (same two-`Subtype.ext` injectivity and `e.apply_symm_apply` image
   proof).

Together S250+S251 realize BOTH sides of the dichotomy as concrete
embedded subsets of the band: compact components are embedded circles,
interval components are embedded open arcs — the raw material of the
Layer-B/C non-separating-arc analysis and the winding measurement.
-/

/-- **The component dichotomy, disjunctive form (S251)**: every connected
component of the trisecant set (as a subtype `TrisecantComponent r c₀`) is
homeomorphic either to the open unit interval (non-compact side,
`trisecantComponent_intervalSide` S242) or to the circle (compact side,
`trisecantComponent_compactSide` S249). -/
theorem trisecantComponent_dichotomy {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    (Nonempty (OpenRealInterval 0 1 ≃ₜ TrisecantComponent r c₀)) ∨
      Nonempty (Circle ≃ₜ TrisecantComponent r c₀) := by
  by_cases hcmp : IsCompact (connectedComponent c₀ : Set (OSub r))
  · exact Or.inr (trisecantComponent_compactSide h hqf hgp c₀ hcmp)
  · exact Or.inl (trisecantComponent_intervalSide h hqf hgp c₀ hcmp)

/-- **An interval-charted component is an embedded open arc of the band
(S251)**: given the interval homeo `e : OpenRealInterval 0 1 ≃ₜ
TrisecantComponent r c₀` (the S242 interval-side output), the composite of
`e` with the subtype projections is an injective continuous arc map from
`(0,1)` into `OpenMobius` whose range is exactly the component val-set
`(fun s : OSub r => (s : OpenMobius)) '' (connectedComponent c₀ : Set (OSub r))` —
the interval-side mirror of `component_simpleClosedCurve_of_circleHomeo`. -/
theorem component_arc_of_intervalHomeo {r : ℝ → Space} (c₀ : OSub r)
    (e : OpenRealInterval 0 1 ≃ₜ TrisecantComponent r c₀) :
    ∃ f : C(OpenRealInterval 0 1, OpenMobius), Function.Injective f ∧
      Set.range f = (fun s : OSub r => (s : OpenMobius)) '' (connectedComponent c₀ : Set (OSub r)) := by
  let f : C(OpenRealInterval 0 1, OpenMobius) :=
    ⟨fun x => (((e x : TrisecantComponent r c₀) : OSub r) : OpenMobius),
      (continuous_subtype_val.comp continuous_subtype_val).comp e.continuous⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  refine ⟨f, hinj, ?_⟩
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(e x : TrisecantComponent r c₀), (e x : TrisecantComponent r c₀).2, ?_⟩
    rfl
  · rintro ⟨s, hs, hc⟩
    refine ⟨e.symm ⟨s, hs⟩, ?_⟩
    calc
      (((e (e.symm ⟨s, hs⟩) : TrisecantComponent r c₀) : OSub r) : OpenMobius)
          = (((⟨s, hs⟩ : TrisecantComponent r c₀) : OSub r) : OpenMobius) := by
            rw [e.apply_symm_apply ⟨s, hs⟩]
      _ = (s : OpenMobius) := by rfl
      _ = c := by exact hc

end LeanEval.KnotTheory.Quadrisecant
