import Mathlib
import Submission.Work.Drive.sweepTripleGeneric
import Submission.Work.Drive.sweepTripleSource

/-!
# The base triple locus, and item (f) with the chart containment taken at the locus

`Work.Drive.exists_meet3Hyp_sweepChartFam_of_baseSource` still asks for two design data: a compact set
`K` with (i) the base triple locus inside its interior (`hbase`) and (ii) the base values on `K` inside
one chart (`hsrcK`).  This file **constructs** `K` from the weakest possible datum:

> at the base triple locus itself, the three values lie in the source of one chart `chr p`
> (`hloc` — note that at a triple point the three values are *equal*, so this is a condition on one
> point per locus element, not on a neighbourhood).

The construction is the standard thickening of a compact set:

* `Work.Drive.sweepLocus P Ξ c` — the base triple locus in the nine-box (compact: the box is compact
  and `meet3` is closed);
* `K := Metric.cthickening δ (sweepLocus P Ξ c)` with `δ > 0` chosen so that the *values* on the
  thickening lie in the chart's source (the containment region is open and contains the compact locus,
  so `IsCompact.exists_cthickening_subset_open` applies — no Lebesgue-number argument is needed);
* `hbase` holds because `Metric.thickening δ L` is an open set between the locus and `K`;
* `hsrcK` holds by the choice of `δ`.

The endpoint is **`Work.Drive.exists_meet3Hyp_sweepChartFam_of_locus`**.
-/

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {Q : ℂ → CappingSpace}
variable {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
variable {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}

/-- **The base triple locus** of the design's family, inside the nine-box. -/
def sweepLocus (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ) :
    Set (EuclideanSpace ℝ (Fin 9)) :=
  {y | y ∈ Submission.Drive.unitBox 8 ∧
    Work.Drive.TParity.meet3 (sweepChartFam P Ξ c 0) y}

/-- **At the base parameter the family is the unperturbed clamped sweep** (because `Ξ 0 = id`). -/
lemma sweepChartFam_zero {P Ξ c} (hΞ : ChartPert Q 4 Ξ) (k : Fin 3) :
    sweepChartFam P Ξ c 0 k = clampedSweep (c k) (fun r => 1 - r) (P k) := by
  funext x
  simp only [sweepChartFam, map_zero, hΞ.1]

/-- **The slice of the family at the base parameter is continuous in the box parameter.** -/
lemma continuous_sweepChartFam_zero (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (k : Fin 3) :
    Continuous (fun y : EuclideanSpace ℝ (Fin 9) =>
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y)) := by
  rw [show (fun y : EuclideanSpace ℝ (Fin 9) =>
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y))
      = (fun x : EuclideanSpace ℝ (Fin 3) =>
          clampedSweep (c k) (fun r => 1 - r) (P k) x) ∘
        (fun y : EuclideanSpace ℝ (Fin 9) => Work.Drive.TParity.bPartC k y) from by
    funext y
    rw [Function.comp_apply, sweepChartFam_zero hΞ k]]
  exact (contMDiff_clampedSweep (c k) (fun r => 1 - r) (P k) (by fun_prop) (hP k)).continuous.comp
    (Work.Drive.TParity.bPartC k).continuous

/-- The base triple locus is compact. -/
lemma isCompact_sweepLocus (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (hΞ : ChartPert Q 4 Ξ)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k)) :
    IsCompact (sweepLocus P Ξ c) := by
  have hcont : ∀ k : Fin 3, Continuous (fun y : EuclideanSpace ℝ (Fin 9) =>
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y)) :=
    fun k => continuous_sweepChartFam_zero P Ξ c hΞ hP k
  have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin 9) |
      Work.Drive.TParity.meet3 (sweepChartFam P Ξ c 0) y} := by
    have h1 : IsClosed {y : EuclideanSpace ℝ (Fin 9) |
        sweepChartFam P Ξ c 0 0 (Work.Drive.TParity.bPartC 0 y) =
          sweepChartFam P Ξ c 0 1 (Work.Drive.TParity.bPartC 1 y)} :=
      isClosed_eq (hcont 0) (hcont 1)
    have h2 : IsClosed {y : EuclideanSpace ℝ (Fin 9) |
        sweepChartFam P Ξ c 0 0 (Work.Drive.TParity.bPartC 0 y) =
          sweepChartFam P Ξ c 0 2 (Work.Drive.TParity.bPartC 2 y)} :=
      isClosed_eq (hcont 0) (hcont 2)
    have heq : {y : EuclideanSpace ℝ (Fin 9) |
        Work.Drive.TParity.meet3 (sweepChartFam P Ξ c 0) y} =
      {y | sweepChartFam P Ξ c 0 0 (Work.Drive.TParity.bPartC 0 y) =
          sweepChartFam P Ξ c 0 1 (Work.Drive.TParity.bPartC 1 y)} ∩
      {y | sweepChartFam P Ξ c 0 0 (Work.Drive.TParity.bPartC 0 y) =
          sweepChartFam P Ξ c 0 2 (Work.Drive.TParity.bPartC 2 y)} :=
      Set.ext fun y => Iff.rfl
    rw [heq]
    exact h1.inter h2
  have hsub : sweepLocus P Ξ c ⊆ Submission.Drive.unitBox 8 := fun y hy => hy.1
  rw [sweepLocus]
  exact (isCompact_unitBox 8).inter_right hclosed

/-- **The genericity endpoint with the chart containment taken at the base triple locus only.**

This is `Work.Drive.exists_meet3Hyp_sweepChartFam_of_baseSource` with both design data (`hsrcK` and
`hbase`) replaced by the single condition that the *base* values at the *base triple locus* lie in one
chart.  The compact set `K` is constructed as a thickening of the locus. -/
theorem exists_meet3Hyp_sweepChartFam_of_locus (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (p : CappingSpace)
    (hloc : ∀ y ∈ Submission.Drive.unitBox 8,
      Work.Drive.TParity.meet3 (sweepChartFam P Ξ c 0) y → ∀ k : Fin 3,
        sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp CappingSpace (sweepChartFam P Ξ c t) := by
  have hcont : ∀ k : Fin 3, Continuous (fun y : EuclideanSpace ℝ (Fin 9) =>
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y)) :=
    fun k => continuous_sweepChartFam_zero P Ξ c hΞ hP k
  -- the source-containment region at the base parameter is open and contains the locus
  have hVopen : IsOpen {y : EuclideanSpace ℝ (Fin 9) | ∀ k : Fin 3,
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.eventually_all.mpr fun k => ?_
    exact (hcont k).continuousAt.preimage_mem_nhds
      ((chr p).open_source.mem_nhds (hy k))
  have hLV : sweepLocus P Ξ c ⊆ {y : EuclideanSpace ℝ (Fin 9) | ∀ k : Fin 3,
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source} :=
    fun y hy => hloc y hy.1 hy.2
  obtain ⟨δ, hδpos, hδ⟩ :=
    (isCompact_sweepLocus P Ξ c hΞ hP).exists_cthickening_subset_open hVopen hLV
  refine exists_meet3Hyp_sweepChartFam_of_baseSource P Ξ c hΞ hc hcdist hP hPseam
    (Metric.cthickening δ (sweepLocus P Ξ c)) (isCompact_sweepLocus P Ξ c hΞ hP).cthickening p
    (fun y hy k => hδ hy k) ?_
  -- the base locus lies in the interior of the thickening
  intro y hy hmeet
  have hyL : y ∈ sweepLocus P Ξ c := ⟨hy, hmeet⟩
  exact interior_maximal (Metric.thickening_subset_cthickening δ (sweepLocus P Ξ c))
    Metric.isOpen_thickening (Metric.self_subset_thickening hδpos (sweepLocus P Ξ c) hyL)

end

end Work.Drive
