import Mathlib
import Submission.Work.Beltrami.hasFDerivAt_cauchyInt

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff Topology

/-- The continuous-linear-map valued integrand of the derivative of the Cauchy integral,
`u ↦ u⁻¹ • fderiv ℝ f (z + u)`, is Bochner integrable: it is dominated by
`M * ‖u‖⁻¹` on a large ball (the singularity at `0` is integrable in real dimension two)
and vanishes outside it, because `f` vanishes outside a ball. -/
lemma integrable_smul_fderiv_cauchyInt (f : ℂ → ℂ) (hf : ContDiff ℝ ⊤ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun u : ℂ => (u⁻¹ : ℂ) • fderiv ℝ f (z + u)) volume := by
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  -- a radius outside which `f` vanishes
  obtain ⟨R0, _hR0pos, hR0⟩ := hc.exists_pos_le_norm
  -- a global bound for `‖fderiv ℝ f‖`
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support hfdc (hc.fderiv (𝕜 := ℝ))
  let M' : ℝ := max M 0
  have hM'pos : 0 ≤ M' := le_max_right _ _
  have hM'bound : ∀ w, ‖fderiv ℝ f w‖ ≤ M' := fun w => le_trans (hM w) (le_max_left _ _)
  -- the cutoff radius for the dominating function
  let r : ℝ := R0 + ‖z‖ + 2
  have hr : r = R0 + ‖z‖ + 2 := rfl
  -- `f` vanishes away from the ball of radius `R0`
  have hsup : tsupport f ⊆ Metric.closedBall 0 R0 := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro v hv
    rw [Function.mem_support] at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hv (hR0 v (le_of_lt (not_le.mp h)))
  have hfin : (1 : ℝ) < (Module.finrank ℝ ℂ : ℝ) := by
    rw [Complex.finrank_real_complex]; norm_num
  have hfin1 : (1 : ℕ) ≤ Module.finrank ℝ ℂ := by
    rw [Complex.finrank_real_complex]; norm_num
  -- the dominating function `‖a‖⁻¹`, cut off at the ball of radius `r`
  let bound : ℂ → ℝ := Set.indicator (Metric.ball 0 r) (fun a => M' * ‖a‖⁻¹)
  have hbound : bound = Set.indicator (Metric.ball 0 r) (fun a => M' * ‖a‖⁻¹) := rfl
  have hbound_int : Integrable bound volume := by
    rw [hbound, integrable_indicator_iff measurableSet_ball]
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℝ) (μ := volume)
      (C := M') (α := 1) (r := r) hfin1 hfin ?_ ?_
    · filter_upwards with a
      have hnn : 0 ≤ M' * ‖a‖⁻¹ := mul_nonneg hM'pos (inv_nonneg.mpr (norm_nonneg a))
      have he : ‖(M' * ‖a‖⁻¹ : ℝ)‖ = M' * ‖a‖ ^ (-1 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.rpow_neg_one]
      exact he.le
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
  refine Integrable.mono' hbound_int ?_ ?_
  · -- strong measurability
    have h1 : Measurable (fun u : ℂ => (u⁻¹ : ℂ)) := measurable_inv
    have h2 : Measurable (fun u : ℂ => fderiv ℝ f (z + u)) :=
      hfdc.measurable.comp (by fun_prop)
    exact (h1.smul h2).aestronglyMeasurable
  · -- pointwise domination
    refine Filter.Eventually.of_forall (fun a => ?_)
    by_cases ha : a ∈ Metric.ball 0 r
    · rw [hbound, Set.indicator_of_mem ha]
      calc ‖(a⁻¹ : ℂ) • fderiv ℝ f (z + a)‖
          ≤ ‖(a⁻¹ : ℂ)‖ * ‖fderiv ℝ f (z + a)‖ := norm_smul_le _ _
        _ = ‖a‖⁻¹ * ‖fderiv ℝ f (z + a)‖ := by rw [norm_inv]
        _ ≤ ‖a‖⁻¹ * M' :=
            mul_le_mul_of_nonneg_left (hM'bound (z + a)) (inv_nonneg.mpr (norm_nonneg a))
        _ = M' * ‖a‖⁻¹ := by ring
    · rw [hbound, Set.indicator_of_notMem ha]
      have h1 : r ≤ ‖a‖ := by
        rw [Metric.mem_ball, dist_zero_right] at ha
        exact not_lt.mp ha
      have htsup : z + a ∉ tsupport f := by
        intro hmem
        have hc' := hsup hmem
        rw [Metric.mem_closedBall, dist_zero_right] at hc'
        rw [hr] at h1
        have hza : ‖a‖ ≤ ‖z + a‖ + ‖z‖ := by
          have h := norm_sub_le (z + a) z
          rw [add_sub_cancel_left] at h
          exact h
        linarith
      rw [fderiv_of_notMem_tsupport ℝ htsup, smul_zero, norm_zero]

theorem cauchyInt_fderiv_apply (f : ℂ → ℂ) (hf : ContDiff ℝ ⊤ f) (hc : HasCompactSupport f)
    (z v : ℂ) :
    fderiv ℝ (cauchyInt f) z v = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) v) ∂MeasureTheory.volume := by
  rw [(hasFDerivAt_cauchyInt f hf hc z).fderiv]
  rw [ContinuousLinearMap.integral_apply (integrable_smul_fderiv_cauchyInt f hf hc z) v]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_apply, smul_eq_mul]

end Work.Beltrami
