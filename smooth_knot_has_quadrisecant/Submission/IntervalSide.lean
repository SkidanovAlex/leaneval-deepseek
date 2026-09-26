import Mathlib
import Submission.LevelZeroHconn
import Submission.Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S204 — the interval-side supply of the per-level `hD_k` (module
Submission/IntervalSide.lean)

Per the S203 STATUS the per-level `hD_k` (connectedness of the
transition domain `transitionDomain (walkChart k) (walkChart (k+1))`)
is the atomic interface the dichotomy's interval side must supply.  The
delegated L33 (`Commons.Topology.ConnectedReal.preconnected_inter_of_isOpen`)
and its ambient consequence L34 (`preconnected_inter_of_homeoUnit`, in
flight) are the real-line primitives of that supply.  This module builds
the O-side wiring that consumes them once the interval chart of a region
is in hand:

1. **`chartTrace_preconnected`** — every chart trace is preconnected (a
   continuous image of the connected chart interval: `chartTrace_eq_range`
   + `isPreconnected_range`), so the traces meet the preconnectedness
   hypothesis of the interval fact with no further input;
2. **`overlapCoordMap` / `continuous_overlapCoordMap`** — the `ch₁`-
   coordinate map on the overlap of two traces (continuous, via the
   chart homeo inverse);
3. **`transitionDomain_preconnected_of_overlap_preconnected`** — the
   coordinate transfer: preconnectedness of the overlap
   `chartTrace ch₁ ∩ chartTrace ch₂` passes to the transition domain
   (its image under the continuous coordinate map, whose range is
   exactly `D`);
4. **`walk_transitionDomain_connected_of_intervalAmbient`** — the
   supply theorem: given an open region `Ω` containing the two
   consecutive traces and the region's interval fact `hInter`
   (intersection of two open preconnected subsets of `Ω` is
   preconnected — derived from L33/L34 through the region chart
   `χ : ↑Ω ≃ₜ (0,1)`), the transition domain is CONNECTED: the `hD_k`
   interface with its Nonempty half from the overlap class (S202) and
   its Preconnected half from the interval-side geometry.  This is the
   per-level interface the dichotomy's interval case instantiates.

DELEGATION STATUS: L33 (`preconnected_inter_of_isOpen`) and L34
(`Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit`) have
BOTH LANDED.  The corollary
**`walk_transitionDomain_connected_of_intervalChart`** instantiates the
`hInter` hypothesis of the supply theorem from the region chart `χ`
via L34 — the first genuinely interval-side-sourced `hD_k` statement
(the dichotomy's interval case supplies `χ` and the trace-containment
per level, or the component chart once per component).

Everything here is verified (no axioms, no `sorry`).
-/

/-- A chart trace is preconnected (a continuous image of the connected
chart interval). -/
lemma chartTrace_preconnected {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    IsPreconnected (chartTrace ch) := by
  have hlt : ch.lo < ch.hi := lt_trans ch.x₀_mem.1 ch.x₀_mem.2
  haveI : PathConnectedSpace (ChartInterval ch.lo ch.hi) := chartInterval_pathConnected hlt
  haveI : ConnectedSpace (ChartInterval ch.lo ch.hi) := PathConnectedSpace.connectedSpace
  rw [chartTrace_eq_range ch]
  exact isPreconnected_range (f := fun t : ChartInterval ch.lo ch.hi => (ch.homeo t).1)
    (continuous_subtype_val.comp ch.homeo.continuous)

/-- The `ch₁`-coordinate map on the overlap of two chart traces, read as
a continuous map from the overlap subtype into the `ch₁`-interval. -/
noncomputable def overlapCoordMap {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀) :
    {c : OSub r // c ∈ chartTrace ch₁ ∩ chartTrace ch₂} → ChartInterval ch₁.lo ch₁.hi :=
  fun c => chParam ch₁ c.1 ((mem_chartTrace ch₁ c.1).mp c.2.1)

/-- The overlap coordinate map is continuous. -/
lemma continuous_overlapCoordMap {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀) :
    Continuous (overlapCoordMap ch₁ ch₂) := by
  let emb : {c : OSub r // c ∈ chartTrace ch₁ ∩ chartTrace ch₂} →
      {c : OSub r // (c : OpenMobius) ∈ ch₁.W} := fun c => ⟨c.1, (mem_chartTrace ch₁ c.1).mp c.2.1⟩
  have hemb : Continuous emb := by
    dsimp [emb]
    exact Continuous.subtype_mk continuous_subtype_val (fun c => (mem_chartTrace ch₁ c.1).mp c.2.1)
  have hgoal : overlapCoordMap ch₁ ch₂ = ch₁.homeo.symm ∘ emb := by
    funext c
    dsimp [overlapCoordMap, emb, chParam]
  rw [hgoal]
  exact (ch₁.homeo.symm.continuous).comp hemb

/-- **S204(i) — the coordinate transfer of overlap preconnectedness.**
The transition domain `transitionDomain ch₁ ch₂` (the coordinate set of
the overlap) is preconnected whenever the overlap
`chartTrace ch₁ ∩ chartTrace ch₂` is: the coordinate map is continuous
and its range is exactly the transition domain. -/
lemma transitionDomain_preconnected_of_overlap_preconnected {r : ℝ → Space} {c₁₀ c₂₀ : OSub r}
    (ch₁ : OSub1Chart r c₁₀) (ch₂ : OSub1Chart r c₂₀)
    (h : IsPreconnected (chartTrace ch₁ ∩ chartTrace ch₂ : Set (OSub r))) :
    IsPreconnected (transitionDomain ch₁ ch₂) := by
  let S : Set (OSub r) := chartTrace ch₁ ∩ chartTrace ch₂
  haveI : PreconnectedSpace {c : OSub r // c ∈ S} :=
    (isPreconnected_iff_preconnectedSpace).mp (by simpa [S] using h)
  have hconnRange : IsPreconnected (Set.range (overlapCoordMap ch₁ ch₂)) :=
    isPreconnected_range (continuous_overlapCoordMap ch₁ ch₂)
  have hrange : Set.range (overlapCoordMap ch₁ ch₂) = transitionDomain ch₁ ch₂ := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      dsimp [overlapCoordMap, transitionDomain]
      have hl : oChartLift ch₁ (chParam ch₁ c.1 ((mem_chartTrace ch₁ c.1).mp c.2.1)) = c.1 :=
        chParam_lift ch₁ ((mem_chartTrace ch₁ c.1).mp c.2.1)
      rw [hl]
      exact (mem_chartTrace ch₂ c.1).mp c.2.2
    · intro hx
      dsimp [transitionDomain] at hx
      let c0 : OSub r := oChartLift ch₁ x
      have hc0₁ : c0 ∈ chartTrace ch₁ := by
        exact (mem_chartTrace ch₁ c0).mpr (oChartLift_mem_W ch₁ x)
      have hc0₂ : c0 ∈ chartTrace ch₂ := by
        exact (mem_chartTrace ch₂ c0).mpr hx
      refine ⟨⟨c0, ⟨hc0₁, hc0₂⟩⟩, ?_⟩
      dsimp [overlapCoordMap]
      apply oChartLift_injective ch₁
      exact chParam_lift ch₁ ((mem_chartTrace ch₁ c0).mp hc0₁)
  simpa [hrange] using hconnRange

/-- **S204(ii) — the interval-side supply of the per-level `hD_k`.**
Given an interval-charted open region `Ω` of the trisecant set containing
the two consecutive traces `T k`, `T (k+1)`, and the region's interval
fact `hInter` (the intersection of two open preconnected subsets of `Ω`
is preconnected — derived from the L33/L34 commons lemmas once the
region's chart `χ : ↑Ω ≃ₜ (0,1)` is in hand), the transition domain
`D_k` is CONNECTED: `IsConnected (transitionDomain (walkChart k)
(walkChart (k+1)))` — the `hD_k` interface, with the Nonempty half from
the overlap class and the Preconnected half from the interval-side
geometry.  This is the interface the dichotomy's interval case
instantiates at every level. -/
theorem walk_transitionDomain_connected_of_intervalAmbient {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (k : ℕ) {Ω : Set (OSub r)}
    (hTsub : chartTrace (walkChart h hqf hgp cl e k) ⊆ Ω)
    (hT1sub : chartTrace (walkChart h hqf hgp cl e (k + 1)) ⊆ Ω)
    (hInter : ∀ ⦃s t : Set (OSub r)⦄, s ⊆ Ω → t ⊆ Ω → IsOpen s → IsOpen t →
      IsPreconnected s → IsPreconnected t → (s ∩ t).Nonempty → IsPreconnected (s ∩ t)) :
    IsConnected (transitionDomain (walkChart h hqf hgp cl e k)
      (walkChart h hqf hgp cl e (k + 1))) := by
  let ch₁ := walkChart h hqf hgp cl e k
  let ch₂ := walkChart h hqf hgp cl e (k + 1)
  have hne : (transitionDomain ch₁ ch₂).Nonempty := by
    dsimp [ch₁, ch₂]
    exact walk_transitionDomain_nonempty h hqf hgp cl e hoverlap k
  have hopre : IsPreconnected (transitionDomain ch₁ ch₂) := by
    dsimp [ch₁, ch₂]
    apply transitionDomain_preconnected_of_overlap_preconnected
    exact hInter hTsub hT1sub (isOpen_chartTrace ch₁) (isOpen_chartTrace ch₂)
      (chartTrace_preconnected ch₁) (chartTrace_preconnected ch₂)
      ⟨walkOverlapClass h hqf hgp cl e hoverlap k,
        ⟨walkOverlapClass_mem_left h hqf hgp cl e hoverlap k,
         walkOverlapClass_mem_right h hqf hgp cl e hoverlap k⟩⟩
  exact ⟨hne, hopre⟩

/-- **S204(iii) — the interval-side-sourced `hD_k` (L34 instantiation).**
With an interval chart `χ : ↑Ω ≃ₜ ORI 0 1` of an open region `Ω`
containing the two consecutive traces `T k`, `T (k+1)`, the transition
domain `D_k` is CONNECTED: the L34 commons lemma
(`preconnected_inter_of_homeoUnit`) instantiates the `hInter` fact of
the supply theorem from `χ`.  This is the per-level `hD_k` statement
the dichotomy's interval case instantiates. -/
theorem walk_transitionDomain_connected_of_intervalChart {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (k : ℕ) {Ω : Set (OSub r)}
    (χ : {c : OSub r // c ∈ Ω} ≃ₜ OpenRealInterval 0 1)
    (hTsub : chartTrace (walkChart h hqf hgp cl e k) ⊆ Ω)
    (hT1sub : chartTrace (walkChart h hqf hgp cl e (k + 1)) ⊆ Ω) :
    IsConnected (transitionDomain (walkChart h hqf hgp cl e k)
      (walkChart h hqf hgp cl e (k + 1))) := by
  let hInter : ∀ ⦃s t : Set (OSub r)⦄, s ⊆ Ω → t ⊆ Ω → IsOpen s → IsOpen t →
      IsPreconnected s → IsPreconnected t → (s ∩ t).Nonempty → IsPreconnected (s ∩ t) := by
    intro s t hssub htsub hs_open ht_open hs ht hne
    exact Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit
      (X := OSub r) (Ω := Ω) χ hs_open ht_open hssub htsub hs ht hne
  exact walk_transitionDomain_connected_of_intervalAmbient h hqf hgp cl e hoverlap k
    (Ω := Ω) hTsub hT1sub hInter

end LeanEval.KnotTheory.Quadrisecant
