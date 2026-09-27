import Mathlib
import Submission.Work.Drive.sweepTripleGeneric

/-!
# The chart containment of the design's triple at the base parameter

This file removes the `hcontain` hypothesis of `Work.Drive.exists_meet3Hyp_sweepChartFam` (the
containment of the family's values in one chart, required *for all small parameters* `t` and on a
compact set `K`): it suffices that the containment holds at the **base** parameter `t = 0`, because
the containment region is open and contains the compact set `{0} × K`.

The endpoint is `Work.Drive.exists_meet3Hyp_sweepChartFam_of_baseSource`.
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

/-- **The chart-containment region** of the design's family on the parameter space. -/
def sweepSourceSet (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (p : CappingSpace) : Set (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9)) :=
  {q | ∀ k : Fin 3,
    sweepChartFam P Ξ c q.1 k (Work.Drive.TParity.bPartC k q.2) ∈ (chr p).source}

/-- The chart-containment region is open (each of the three chains is continuous and the chart's
source is open). -/
lemma isOpen_sweepSourceSet (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (p : CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k)) :
    IsOpen (sweepSourceSet P Ξ c p) := by
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  have hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartFam P Ξ c q.1 k q.2) :=
    fun k => contMDiff_sweepChartFam P Ξ c hslice k
  rw [isOpen_iff_mem_nhds]
  intro q hq
  rw [sweepSourceSet] at hq
  refine Filter.eventually_all.mpr fun k => ?_
  have hcont : ContinuousAt (fun q' : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9) =>
      sweepChartFam P Ξ c q'.1 k (Work.Drive.TParity.bPartC k q'.2)) q :=
    ((hG k).continuous.comp
      (continuous_fst.prodMk ((Work.Drive.TParity.bPartC k).continuous.comp continuous_snd))).continuousAt
  exact hcont.preimage_mem_nhds ((chr p).open_source.mem_nhds (hq k))

/-- **If the values of the base triple on a compact set `K` lie in the source of one chart, then so do
the values of the whole family for all parameters of small norm, uniformly on `K`.**

This replaces the hypothesis `hcontain` of `Work.Drive.exists_meet3Hyp_sweepChartFam` (a containment
*for all small `t`*) by the containment at the base parameter `t = 0` alone.  Proof: the containment
region is open and contains the compact set `{0} × K`; the tube lemma
`IsCompact.exists_cthickening_subset_open` produces the uniform radius. -/
lemma exists_eps_source_sweepChartFam (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) (p : CappingSpace)
    (hsrcK : ∀ y ∈ K, ∀ k : Fin 3,
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → ∀ k : Fin 3,
        sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source := by
  have hsub : ({0} ×ˢ K : Set (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9))) ⊆
      sweepSourceSet P Ξ c p := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩ k
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hsrcK y hy k
  obtain ⟨δ, hδpos, hδ⟩ := (isCompact_singleton.prod hK).exists_cthickening_subset_open
    (t := sweepSourceSet P Ξ c p) (isOpen_sweepSourceSet P Ξ c p hΞ hP) hsub
  refine ⟨δ, hδpos, fun t y ht hy k => ?_⟩
  have h1 : (t, y) ∈ Metric.cthickening δ
      ({0} ×ˢ K : Set (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9))) := by
    refine Metric.thickening_subset_cthickening δ _ (Metric.mem_thickening_iff.mpr
      ⟨(0, y), ⟨rfl, hy⟩, ?_⟩)
    have hdist : dist ((t, y) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9))
        ((0 : EuclideanSpace ℝ (Fin 12)), y) = ‖t‖ := by
      rw [Prod.dist_eq, dist_zero_right, dist_self, max_eq_left (by simp)]
    exact lt_of_eq_of_lt hdist ht
  have h2 : (t, y) ∈ sweepSourceSet P Ξ c p := hδ h1
  rw [sweepSourceSet] at h2
  exact h2 k

/-- **The genericity endpoint with the chart containment taken at the base parameter only.**  This is
`Work.Drive.exists_meet3Hyp_sweepChartFam` with its `hcontain` hypothesis (a containment *for all small
`t`*) replaced by the containment at `t = 0` (`hsrcK`); the uniform-in-`t` form follows from
`Work.Drive.exists_eps_source_sweepChartFam`. -/
theorem exists_meet3Hyp_sweepChartFam_of_baseSource (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) (p : CappingSpace)
    (hsrcK : ∀ y ∈ K, ∀ k : Fin 3,
      sweepChartFam P Ξ c 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (sweepChartFam P Ξ c 0) y → y ∈ interior K) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp CappingSpace (sweepChartFam P Ξ c t) := by
  obtain ⟨ε, hε, hcont⟩ := exists_eps_source_sweepChartFam P Ξ c hΞ hP K hK p hsrcK
  exact exists_meet3Hyp_sweepChartFam P Ξ c hΞ hc hcdist hP hPseam K hK p hε
    (fun t y ht hy k => hcont t y ht hy k) hbase

end

end Work.Drive
