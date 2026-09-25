import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set
open Work.CR.Flat.Cauchy (dbarTransform)

namespace Work.NN.Core

/-- The derivative of the one-variable Cauchy transform is the Cauchy transform of the
derivative: `fderiv ℝ (T_j g) z v = T_j (fun y => fderiv ℝ g y v) z`, for `ρ > 0`. -/
private theorem transform_fderiv_of_pos {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (j : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) (z v : Fin n → ℂ) :
    fderiv ℝ (fun w => dbarTransform ρ j g w) z v
      = dbarTransform ρ j (fun y => fderiv ℝ g y v) z := by
  set μ : Measure ℂ := volume.restrict (Metric.ball (0 : ℂ) ρ) with hμdef
  have hg_cont : Continuous g := hg.continuous
  have hg_diff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hderiv_cont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall z (1 + ρ)).exists_bound_of_continuousOn
    hderiv_cont.continuousOn
  have hCz : ‖fderiv ℝ g z‖ ≤ C := hC z (by rw [Metric.mem_closedBall, dist_self]; linarith)
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) hCz
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn
    hg_cont.continuousOn
  have hτ : ∀ a : ℂ, ‖Function.update (0 : Fin n → ℂ) j a‖ = ‖a‖ := by
    intro a
    rw [show Function.update (0 : Fin n → ℂ) j a = Pi.single j a from by
          funext l
          rw [Function.update_apply, Pi.single_apply]
          by_cases h : l = j <;> simp [h],
        Pi.norm_single]
  have hcont_shift : ∀ y : Fin n → ℂ, Continuous fun a : ℂ =>
      y + Function.update (0 : Fin n → ℂ) j a := by
    intro y
    exact continuous_const.add (continuous_const.update j continuous_id)
  have hmeasF : ∀ y : Fin n → ℂ, AEStronglyMeasurable
      (fun a : ℂ => g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹) μ := by
    intro y
    have hm : Measurable
        (fun a : ℂ => g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹) :=
      (hg_cont.comp (hcont_shift y)).measurable.mul measurable_inv
    exact hm.aestronglyMeasurable
  have hbound_int : Integrable (fun a : ℂ => C * ‖a‖ ^ (-1 : ℝ)) μ :=
    (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul C
  have hgle : ∀ a : ℂ, ‖a‖ < ρ → ‖g (z + Function.update (0 : Fin n → ℂ) j a)‖ ≤ Cg := by
    intro a ha
    refine hCg _ ?_
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hτ a]
    exact ha.le
  have hF_int : Integrable
      (fun a : ℂ => g (z + Function.update (0 : Fin n → ℂ) j a) * a⁻¹) μ := by
    have hmaj : Integrable (fun a : ℂ => Cg * ‖a‖ ^ (-1 : ℝ)) μ :=
      (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul Cg
    refine Integrable.mono' hmaj (hmeasF z) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with a ha
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at ha
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [Real.zero_rpow (by norm_num : (-1 : ℝ) ≠ 0)]
    · rw [norm_mul, norm_inv, Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_right (hgle a ha) (inv_nonneg.mpr (norm_nonneg a))
  have hF'_meas : AEStronglyMeasurable
      (fun a : ℂ => a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)) μ := by
    have hcont : Continuous fun a : ℂ =>
        fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) :=
      hderiv_cont.comp (hcont_shift z)
    exact (measurable_inv.smul hcont.measurable).aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball z 1,
      ‖a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖
        ≤ C * ‖a‖ ^ (-1 : ℝ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with a ha y hy
    have hmem : y + Function.update (0 : Fin n → ℂ) j a ∈ Metric.closedBall z (1 + ρ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖y - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
      have h2 : ‖a‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp ha
      calc ‖y + Function.update (0 : Fin n → ℂ) j a - z‖
          = ‖(y - z) + Function.update (0 : Fin n → ℂ) j a‖ := by
            congr 1; abel
        _ ≤ ‖y - z‖ + ‖Function.update (0 : Fin n → ℂ) j a‖ := norm_add_le _ _
        _ = ‖y - z‖ + ‖a‖ := by rw [hτ a]
        _ ≤ 1 + ρ := by linarith
    calc ‖a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖
        = ‖a⁻¹‖ * ‖fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖ := norm_smul _ _
      _ = ‖a‖⁻¹ * ‖fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖ := by rw [norm_inv]
      _ ≤ ‖a‖⁻¹ * C := mul_le_mul_of_nonneg_left (hC _ hmem) (inv_nonneg.mpr (norm_nonneg a))
      _ = C * ‖a‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, mul_comm]
  have h_diff : ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball z 1,
      HasFDerivAt
        (fun y : Fin n → ℂ => g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹)
        (a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)) y := by
    refine Filter.Eventually.of_forall (fun a y _ => ?_)
    have h1 : HasFDerivAt (fun y : Fin n → ℂ => y + Function.update (0 : Fin n → ℂ) j a)
        (ContinuousLinearMap.id ℝ (Fin n → ℂ)) y := (hasFDerivAt_id y).add_const _
    have h2 : HasFDerivAt
        (fun y : Fin n → ℂ => g (y + Function.update (0 : Fin n → ℂ) j a))
        (fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)) y := by
      have h := (hg_diff.differentiableAt
        (x := y + Function.update (0 : Fin n → ℂ) j a)).hasFDerivAt.comp y h1
      rwa [ContinuousLinearMap.comp_id] at h
    exact h2.mul_const a⁻¹
  have hdiff : HasFDerivAt
      (fun y : Fin n → ℂ => ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ)
      (∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ) z :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (α := ℂ) (E := ℂ)
      (H := Fin n → ℂ) (μ := μ)
      (F := fun y a => g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹)
      (F' := fun y a => a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a))
      (bound := fun a => C * ‖a‖ ^ (-1 : ℝ))
      (s := Metric.ball z 1) (x₀ := z) (Metric.ball_mem_nhds z one_pos)
      (Filter.Eventually.of_forall hmeasF) hF_int hF'_meas h_bound hbound_int h_diff
  have hInt : Integrable
      (fun a : ℂ => a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)) μ :=
    hbound_int.mono' hF'_meas (h_bound.mono (fun a ha => ha z (Metric.mem_ball_self one_pos)))
  have hTeq : (fun w : Fin n → ℂ => dbarTransform ρ j g w)
      = fun w => -((Real.pi : ℂ))⁻¹ *
          (∫ a, g (w + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ) := by
    funext w
    rw [dbarTransform]
    rfl
  have hL : fderiv ℝ (fun w => dbarTransform ρ j g w) z v
      = -((Real.pi : ℂ))⁻¹ * fderiv ℝ (fun y : Fin n → ℂ =>
          ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ) z v := by
    rw [hTeq, fderiv_const_mul hdiff.differentiableAt (-((Real.pi : ℂ))⁻¹),
      smul_apply, smul_eq_mul]
  have hkey : fderiv ℝ (fun y : Fin n → ℂ =>
        ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ) z v
      = ∫ a, fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) v * a⁻¹ ∂μ := by
    rw [hdiff.fderiv, ContinuousLinearMap.integral_apply hInt]
    apply integral_congr_ae
    filter_upwards with a
    rw [smul_apply, smul_eq_mul, mul_comm]
  have hR : dbarTransform ρ j (fun y => fderiv ℝ g y v) z
      = -((Real.pi : ℂ))⁻¹ *
          (∫ a, fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) v * a⁻¹ ∂μ) := by
    rw [dbarTransform]
    rfl
  rw [hL, hR, hkey]

theorem transform_fderiv {n : ℕ} {ρ : ℝ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) (z v : Fin n → ℂ) : fderiv ℝ (fun w => Work.CR.Flat.Cauchy.dbarTransform ρ j g w) z v = Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => fderiv ℝ g y v) z := by
  rcases le_or_gt ρ 0 with hρle | hρ
  · have hempty : Metric.ball (0 : ℂ) ρ = ∅ := Metric.ball_eq_empty.mpr hρle
    have h1 : (fun w : Fin n → ℂ => dbarTransform ρ j g w) = fun _ : Fin n → ℂ => 0 := by
      funext w
      simp [dbarTransform, hempty]
    have h2 : dbarTransform ρ j (fun y => fderiv ℝ g y v) z = 0 := by
      simp [dbarTransform, hempty]
    rw [h1, h2]
    simp
  · exact transform_fderiv_of_pos hρ j hg z v

end Work.NN.Core
