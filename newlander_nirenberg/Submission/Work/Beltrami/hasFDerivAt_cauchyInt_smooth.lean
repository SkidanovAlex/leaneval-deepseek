import Mathlib
import Submission.Work.Beltrami.dbarW_cauchyT_defs

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff Topology
open Filter

/-- **Differentiation of the Cauchy integral under the integral sign, `C¹` version.**

For a `C¹` compactly supported `f`, the Cauchy integral
`cauchyInt f z = ∫ u, u⁻¹ * f (z + u)` is real-differentiable, with derivative
`∫ u, u⁻¹ • fderiv ℝ f (z + u)`.  The integrand is dominated by the locally
integrable function `u ↦ ‖u‖⁻¹` (integrable in the plane), cut off at the support
of `f`. -/
theorem hasFDerivAt_cauchyInt_c1 (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (z : ℂ) :
    HasFDerivAt (cauchyInt f) (∫ u, (u⁻¹ : ℂ) • (fderiv ℝ f (z + u)) ∂volume) z := by
  have hfc : Continuous f := hf.continuous
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  -- a radius outside which `f` vanishes
  obtain ⟨R0, _hR0pos, hR0⟩ := hc.exists_pos_le_norm
  -- a global bound for `‖fderiv ℝ f‖`
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support hfdc (hc.fderiv (𝕜 := ℝ))
  -- a global bound for `‖f‖`
  obtain ⟨Mf₀, hMf₀⟩ := hfc.bounded_above_of_compact_support hc
  let Mf : ℝ := max Mf₀ 0
  have hMfbound : ∀ w, ‖f w‖ ≤ Mf := fun w => le_trans (hMf₀ w) (le_max_left _ _)
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
  -- integrability of the integrand at the base point
  have hF_int : Integrable (fun a : ℂ => a⁻¹ * f (z + a)) volume := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Metric.ball 0 r) ?_ ?_
    · refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℂ) (μ := volume)
        (C := Mf) (α := 1) (r := r) hfin1 hfin ?_ ?_
      · filter_upwards with a
        rcases eq_or_ne a 0 with h | _h
        · subst h; simp
        · have he : ‖a⁻¹ * f (z + a)‖ ≤ Mf * ‖a‖ ^ (-1 : ℝ) := by
            rw [norm_mul, norm_inv, Real.rpow_neg_one]
            exact le_trans
              (mul_le_mul_of_nonneg_left (hMfbound (z + a)) (inv_nonneg.mpr (norm_nonneg a)))
              (le_of_eq (mul_comm _ _))
          exact he
      · apply AEMeasurable.aestronglyMeasurable
        have h1 : Measurable (fun a : ℂ => a⁻¹) := by measurability
        have h2 : Measurable (fun a : ℂ => f (z + a)) := by fun_prop
        exact (h1.mul h2).aemeasurable
    · intro a ha
      have h1 : r ≤ ‖a‖ := by
        rw [Metric.mem_ball, dist_zero_right] at ha
        exact not_lt.mp ha
      have hza : ‖a‖ - ‖z‖ ≤ ‖z + a‖ := by
        have h := norm_sub_le (z + a) z
        rw [add_sub_cancel_left] at h
        linarith
      have hR0lt : R0 < ‖z + a‖ := by rw [hr] at h1; linarith
      rw [hR0 (z + a) (le_of_lt hR0lt), mul_zero]
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (fun a : ℂ => a⁻¹ * f (x + a)) volume := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    apply AEMeasurable.aestronglyMeasurable
    have h1 : Measurable (fun a : ℂ => a⁻¹) := by measurability
    have h2 : Measurable (fun a : ℂ => f (x + a)) := by fun_prop
    exact (h1.mul h2).aemeasurable
  have hF'_meas : AEStronglyMeasurable (fun a : ℂ => a⁻¹ • fderiv ℝ f (z + a)) volume := by
    apply AEMeasurable.aestronglyMeasurable
    have h1 : Measurable (fun a : ℂ => a⁻¹) := by measurability
    have h2 : Measurable (fun a : ℂ => fderiv ℝ f (z + a)) := by fun_prop
    exact (h1.smul h2).aemeasurable
  -- pointwise domination of the derivative by `bound`
  have h_bound : ∀ᵐ a ∂volume, ∀ x ∈ Metric.ball z (1 / 2),
      ‖a⁻¹ • fderiv ℝ f (x + a)‖ ≤ bound a := by
    refine Filter.Eventually.of_forall (fun a x hx => ?_)
    by_cases ha : a ∈ Metric.ball 0 r
    · rw [hbound, Set.indicator_of_mem ha]
      calc ‖a⁻¹ • fderiv ℝ f (x + a)‖ ≤ ‖a⁻¹‖ * ‖fderiv ℝ f (x + a)‖ := norm_smul_le _ _
        _ = ‖a‖⁻¹ * ‖fderiv ℝ f (x + a)‖ := by rw [norm_inv]
        _ ≤ ‖a‖⁻¹ * M' :=
            mul_le_mul_of_nonneg_left (hM'bound (x + a)) (inv_nonneg.mpr (norm_nonneg a))
        _ = M' * ‖a‖⁻¹ := by ring
    · rw [hbound, Set.indicator_of_notMem ha]
      have h1 : r ≤ ‖a‖ := by
        rw [Metric.mem_ball, dist_zero_right] at ha
        exact not_lt.mp ha
      have hx' : ‖x‖ < ‖z‖ + 1 / 2 := by
        have h := norm_add_le (x - z) z
        rw [sub_add_cancel] at h
        rw [Metric.mem_ball, dist_eq_norm] at hx
        linarith
      have hxa : ‖a‖ - ‖x‖ ≤ ‖x + a‖ := by
        have h := norm_sub_le (x + a) x
        rw [add_sub_cancel_left] at h
        linarith
      have htsup : x + a ∉ tsupport f := by
        intro hmem
        have hc' := hsup hmem
        rw [Metric.mem_closedBall, dist_zero_right] at hc'
        rw [hr] at h1
        linarith
      rw [fderiv_of_notMem_tsupport ℝ htsup, smul_zero, norm_zero]
  -- the integrand is differentiable in the parameter
  have h_diff : ∀ᵐ a ∂volume, ∀ x ∈ Metric.ball z (1 / 2),
      HasFDerivAt (fun x => a⁻¹ * f (x + a)) (a⁻¹ • fderiv ℝ f (x + a)) x := by
    refine Filter.Eventually.of_forall (fun a x _hx => ?_)
    have hd : HasFDerivAt f (fderiv ℝ f (x + a)) (x + a) :=
      (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h1 : HasFDerivAt (fun y : ℂ => y + a) (ContinuousLinearMap.id ℝ ℂ) x :=
      (hasFDerivAt_id x).add_const a
    have h2 : HasFDerivAt (fun y : ℂ => f (y + a)) (fderiv ℝ f (x + a)) x := by
      have h2' := hd.comp x h1
      rw [ContinuousLinearMap.comp_id] at h2'
      exact h2'
    exact h2.const_mul a⁻¹
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun x a => a⁻¹ * f (x + a))
    (F' := fun x a => a⁻¹ • fderiv ℝ f (x + a))
    (x₀ := z) (bound := bound) (s := Metric.ball z (1 / 2))
    (Metric.ball_mem_nhds z (by norm_num)) hF_meas hF_int hF'_meas h_bound hbound_int h_diff

theorem hasFDerivAt_cauchyInt_smooth (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (z : ℂ) :
    HasFDerivAt (cauchyInt f) (∫ u, (u⁻¹ : ℂ) • (fderiv ℝ f (z + u)) ∂MeasureTheory.volume) z :=
  hasFDerivAt_cauchyInt_c1 f hf hc z

end Work.Beltrami
