import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Harmonic

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace ENNReal BigOperators

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Metric Set Filter Function in
open scoped Topology RealInnerProductSpace InnerProductSpace ENNReal BigOperators in
theorem integrableOn_mul_ballIntegral {n : ℕ} {u φ : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 < r) (hKc : IsCompact K)
    (hφcont : Continuous φ) (hφsupp : tsupport φ ⊆ K)
    (huc : ContinuousOn u (Metric.cthickening r K)) :
    IntegrableOn (fun x => φ x * (∫ y in Metric.ball x r, u y)) K := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin n)) := Metric.cthickening r K
  have hSmeas : MeasurableSet S := isClosed_cthickening.measurableSet
  have hSc : IsCompact S := hKc.cthickening
  obtain ⟨Cφ, hCφ⟩ := IsCompact.exists_bound_of_continuousOn hKc hφcont.continuousOn
  obtain ⟨Cu, hCu⟩ := IsCompact.exists_bound_of_continuousOn hSc huc
  have hzero : ∀ x, x ∉ K → φ x = 0 := by
    intro x hx
    by_contra h
    exact hx (hφsupp (subset_closure (Function.mem_support.mpr h)))
  have hballS : ∀ x ∈ K, Metric.ball x r ⊆ S := fun x hx =>
    (ball_subset_thickening hx r).trans (thickening_subset_cthickening r K)
  -- `u` restricted to the thickening `S` is measurable
  have hu₀ : AEStronglyMeasurable (S.indicator u)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (aestronglyMeasurable_indicator_iff hSmeas).2 (huc.aestronglyMeasurable hSmeas)
  have hu₀snd : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => S.indicator u p.2)
      (volume.prod volume) :=
    hu₀.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hTmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      p.2 ∈ Metric.ball p.1 r} := by
    have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        dist p.2 p.1) := continuous_dist.comp (continuous_snd.prodMk continuous_fst)
    have : {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | p.2 ∈ Metric.ball p.1 r}
        = {p | dist p.2 p.1 < r} := by
      ext p; simp only [Set.mem_ofPred_eq, Metric.mem_ball]
    rw [this]
    exact measurableSet_lt hcont.measurable measurable_const
  have hTind : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (Metric.ball p.1 r).indicator (S.indicator u) p.2) (volume.prod volume) := by
    have h1 := hu₀snd.indicator hTmeas
    have heq : ({p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
          p.2 ∈ Metric.ball p.1 r}.indicator (fun p => S.indicator u p.2))
        = (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (Metric.ball p.1 r).indicator (S.indicator u) p.2) := by
      funext p
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rwa [heq] at h1
  have hw'_meas : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ p.1 * (Metric.ball p.1 r).indicator (S.indicator u) p.2) (volume.prod volume) := by
    have hφ' : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => φ p.1)
        (volume.prod volume) :=
      (hφcont.measurable.aestronglyMeasurable).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
    exact hφ'.mul hTind
  have hw_eq : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ p.1 * (Metric.ball p.1 r).indicator (S.indicator u) p.2)
      = (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ p.1 * (Metric.ball p.1 r).indicator u p.2) := by
    funext p
    by_cases hφ : φ p.1 = 0
    · simp only [hφ, zero_mul]
    · have hp1 : p.1 ∈ K := hφsupp (subset_closure (Function.mem_support.mpr hφ))
      have hind : (Metric.ball p.1 r).indicator (S.indicator u) p.2
          = (Metric.ball p.1 r).indicator u p.2 := by
        by_cases hb : p.2 ∈ Metric.ball p.1 r
        · rw [Set.indicator_of_mem hb (S.indicator u), Set.indicator_of_mem hb u]
          exact Set.indicator_of_mem (hballS p.1 hp1 hb) u
        · rw [Set.indicator_of_notMem hb (S.indicator u), Set.indicator_of_notMem hb u]
      rw [hind]
  have hw_meas : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ p.1 * (Metric.ball p.1 r).indicator u p.2) (volume.prod volume) :=
    hw'_meas.congr (Filter.Eventually.of_forall fun p => congrFun hw_eq p)
  let C : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := K ×ˢ S
  let M : ℝ := max Cφ 0 * max Cu 0
  have hCc : IsCompact C := hKc.prod hSc
  have hCmeas : MeasurableSet C := hCc.isClosed.measurableSet
  have hCfin : (volume.prod volume :
      Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) C ≠ ∞ := by
    change (volume.prod volume) (K ×ˢ S) ≠ ∞
    rw [Measure.prod_prod]
    exact ne_of_lt (ENNReal.mul_lt_top hKc.measure_lt_top hSc.measure_lt_top)
  have hgint : Integrable (C.indicator (fun _ => M)) (volume.prod volume) := by
    rw [integrable_indicator_iff hCmeas]
    exact integrableOn_const hCfin
  have hbound_w : ∀ᵐ p ∂(volume.prod volume :
      Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))),
      ‖φ p.1 * (Metric.ball p.1 r).indicator u p.2‖ ≤ C.indicator (fun _ => M) p := by
    apply Filter.Eventually.of_forall
    intro p
    by_cases hp : p ∈ C
    · rw [Set.indicator_of_mem hp
        (fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => M)]
      have hp1 : p.1 ∈ K := (Set.mem_prod.mp hp).1
      have hp2 : p.2 ∈ S := (Set.mem_prod.mp hp).2
      have h1 : ‖φ p.1‖ ≤ max Cφ 0 := (hCφ p.1 hp1).trans (le_max_left _ _)
      have h2 : ‖(Metric.ball p.1 r).indicator u p.2‖ ≤ max Cu 0 := by
        by_cases hb : p.2 ∈ Metric.ball p.1 r
        · rw [Set.indicator_of_mem hb u]
          exact (hCu p.2 hp2).trans (le_max_left _ _)
        · rw [Set.indicator_of_notMem hb u]
          simp
      calc ‖φ p.1 * (Metric.ball p.1 r).indicator u p.2‖
          = ‖φ p.1‖ * ‖(Metric.ball p.1 r).indicator u p.2‖ := norm_mul _ _
        _ ≤ max Cφ 0 * max Cu 0 := mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
        _ = M := rfl
    · rw [Set.indicator_of_notMem hp
          (fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => M),
        norm_le_zero_iff]
      by_cases hp1 : p.1 ∈ K
      · have hp2 : p.2 ∉ S := fun h => hp (Set.mem_prod.mpr ⟨hp1, h⟩)
        rw [Set.indicator_of_notMem (fun h => hp2 (hballS p.1 hp1 h)) u, mul_zero]
      · rw [hzero p.1 hp1, zero_mul]
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      φ p.1 * (Metric.ball p.1 r).indicator u p.2) (volume.prod volume) :=
    Integrable.mono' hgint hw_meas hbound_w
  -- Integrate the jointly integrable function in the second variable.
  have hInt1 : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => ∫ y, φ x * (Metric.ball x r).indicator u y)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hint.integral_prod_left
  have hInt2 : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => φ x * (∫ y in Metric.ball x r, u y))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply hInt1.congr
    filter_upwards with x
    rw [MeasureTheory.integral_const_mul,
      integral_indicator (s := Metric.ball x r) measurableSet_ball]
  exact hInt2.integrableOn

end

end Commons.Analysis.Harmonic