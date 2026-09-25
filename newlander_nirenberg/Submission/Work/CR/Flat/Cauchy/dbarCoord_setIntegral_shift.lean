import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- Differentiation under the integral sign in the `∂̄`-direction, for the Cauchy-type integral taken in the `j`-th coordinate (namespace `Work.CR.Flat.Cauchy`; `dbarCoord` is from `Submission.Work.CR.Flat.Polydisc`). Write `τ_j w := Function.update (0 : Fin n → ℂ) j w`, the vector whose only nonzero coordinate is the `j`-th, equal to `w`. Let `g : (Fin n → ℂ) → ℂ` be `C¹` with `‖fderiv ℝ g y‖ ≤ M` for all `y`. Then for every `k` and every `z`, the map `y ↦ ∫_{‖w‖<ρ} g (y + τ_j w)/w dw` has `∂̄_k`-derivative equal to the integral of the `∂̄_k`-derivative of the integrand:
`dbarCoord k (fun y => ∫ w in ball 0 ρ, g (y + τ_j w) / w) z = ∫ w in ball 0 ρ, dbarCoord k g (z + τ_j w) / w`.
Both integrals converge absolutely: `g` is bounded near the relevant points (`‖g‖ ≤ ‖g 0‖ + M ‖·‖`) and `‖w‖⁻¹` is integrable on a disc. The intended proof is the standard differentiation-under-the-integral result (e.g. `hasFDerivAt_integral_of_dominated_of_fderiv_le`, or twice `hasDerivAt_integral_of_dominated_loc_of_deriv_le` along the directions `Pi.single k 1` and `Pi.single k Complex.I`), with `dbarCoord k g` the corresponding combination of the two directional derivatives; the required derivative bound is `2M/‖w‖` on the disc. -/
theorem dbarCoord_setIntegral_shift {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {j : Fin n}
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) {M : ℝ}
    (hM : ∀ y : Fin n → ℂ, ‖fderiv ℝ g y‖ ≤ M) (k : Fin n) (z : Fin n → ℂ) :
    dbarCoord k (fun y : Fin n → ℂ =>
        ∫ w in Metric.ball (0 : ℂ) ρ, g (y + Function.update (0 : Fin n → ℂ) j w) / w) z
      = ∫ w in Metric.ball (0 : ℂ) ρ,
          dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) / w := by
  rcases le_or_gt ρ 0 with hρle | hρpos
  · rw [Metric.ball_eq_empty.mpr hρle]
    simp [dbarCoord]
  · have hg_cont : Continuous g := hg.continuous
    have hg_diff : Differentiable ℝ g := hg.differentiable one_ne_zero
    have hderiv_cont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
    have hMnn : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ g 0)) (hM 0)
    obtain ⟨C, hC⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn
      hg_cont.continuousOn
    have hτ : ∀ a : ℂ, ‖Function.update (0 : Fin n → ℂ) j a‖ = ‖a‖ := by
      intro a
      rw [show Function.update (0 : Fin n → ℂ) j a = Pi.single j a from by
            funext l
            rw [Function.update_apply, Pi.single_apply]
            by_cases h : l = j <;> simp [h],
        Pi.norm_single]
    have hgle : ∀ a : ℂ, ‖a‖ < ρ → ‖g (z + Function.update (0 : Fin n → ℂ) j a)‖ ≤ C := by
      intro a ha
      refine hC _ ?_
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hτ a]
      exact ha.le
    set μ : Measure ℂ := volume.restrict (Metric.ball (0 : ℂ) ρ) with hμdef
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
    have hbound_int : Integrable (fun a : ℂ => M * ‖a‖ ^ (-1 : ℝ)) μ :=
      (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul M
    have hF_int : Integrable
        (fun a : ℂ => g (z + Function.update (0 : Fin n → ℂ) j a) * a⁻¹) μ := by
      have hmaj : Integrable (fun a : ℂ => C * ‖a‖ ^ (-1 : ℝ)) μ :=
        (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul C
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
    have h_bound : ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball z ρ,
        ‖a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖
          ≤ M * ‖a‖ ^ (-1 : ℝ) := by
      refine Filter.Eventually.of_forall (fun a y _ => ?_)
      calc ‖a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖
          = ‖a⁻¹‖ * ‖fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖ := by
            rw [norm_smul]
        _ = ‖a‖⁻¹ * ‖fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)‖ := by
            rw [norm_inv]
        _ ≤ ‖a‖⁻¹ * M := mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.mpr (norm_nonneg a))
        _ = M * ‖a‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, mul_comm]
    have h_diff : ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball z ρ,
        HasFDerivAt
          (fun y : Fin n → ℂ => g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹)
          (a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)) y := by
      refine Filter.Eventually.of_forall (fun a y _ => ?_)
      have h1 : HasFDerivAt (fun y : Fin n → ℂ => y + Function.update (0 : Fin n → ℂ) j a)
          (ContinuousLinearMap.id ℝ (Fin n → ℂ)) y := (hasFDerivAt_id y).add_const _
      have h2 : HasFDerivAt
          (fun y : Fin n → ℂ => g (y + Function.update (0 : Fin n → ℂ) j a))
          (fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a)) y := by
        have h := (hg_diff.differentiableAt (x := y + Function.update (0 : Fin n → ℂ) j a)).hasFDerivAt.comp y h1
        rwa [ContinuousLinearMap.comp_id] at h
      exact h2.mul_const a⁻¹
    have hdiff : HasFDerivAt
        (fun y : Fin n → ℂ =>
          ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ)
        (∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ) z :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (α := ℂ) (E := ℂ)
        (H := Fin n → ℂ) (μ := μ)
        (F := fun y a => g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹)
        (F' := fun y a => a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a))
        (bound := fun a => M * ‖a‖ ^ (-1 : ℝ))
        (s := Metric.ball z ρ) (x₀ := z) (Metric.ball_mem_nhds z hρ)
        (Filter.Eventually.of_forall hmeasF) hF_int hF'_meas h_bound hbound_int h_diff
    have hfd : fderiv ℝ (fun y : Fin n → ℂ =>
          ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ) z
        = ∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ :=
      hdiff.fderiv
    have hInt : Integrable
        (fun a : ℂ => a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)) μ :=
      hbound_int.mono' hF'_meas
        (h_bound.mono (fun a ha => ha z (Metric.mem_ball_self hρ)))
    have hsmul_apply : ∀ (a : ℂ) (e : Fin n → ℂ),
        (a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)) e
          = a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) e := by
      intro a e
      rw [smul_apply, smul_eq_mul]
    have hAint : Integrable (fun a : ℂ =>
        a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) (Pi.single k 1)) μ :=
      (hInt.apply_continuousLinearMap (Pi.single k (1 : ℂ))).congr
        (Filter.Eventually.of_forall fun a => hsmul_apply a (Pi.single k 1))
    have hBint : Integrable (fun a : ℂ =>
        a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) (Pi.single k Complex.I)) μ :=
      (hInt.apply_continuousLinearMap (Pi.single k Complex.I)).congr
        (Filter.Eventually.of_forall fun a => hsmul_apply a (Pi.single k Complex.I))
    have hL1 : (∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ)
          (Pi.single k (1 : ℂ))
        = ∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) (Pi.single k 1) ∂μ := by
      rw [ContinuousLinearMap.integral_apply hInt]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => hsmul_apply a (Pi.single k 1))
    have hL2 : (∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ)
          (Pi.single k Complex.I)
        = ∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) (Pi.single k Complex.I) ∂μ := by
      rw [ContinuousLinearMap.integral_apply hInt]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => hsmul_apply a (Pi.single k Complex.I))
    have hLHS : dbarCoord k (fun y : Fin n → ℂ =>
          ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ) z
        = (1 / 2) * ((∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) (Pi.single k 1) ∂μ)
            + Complex.I * (∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) (Pi.single k Complex.I) ∂μ)) := by
      rw [dbarCoord, hfd, hL1, hL2]
    have hptR : ∀ w : ℂ, dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) * w⁻¹
        = (1 / 2) * (w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w) (Pi.single k 1))
          + (1 / 2) * (Complex.I * (w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w) (Pi.single k Complex.I))) := by
      intro w
      rw [dbarCoord]
      ring
    have hRHS : (∫ w in Metric.ball (0 : ℂ) ρ,
          dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) / w)
        = (1 / 2) * ((∫ w, w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w) (Pi.single k 1) ∂μ)
            + Complex.I * (∫ w, w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w) (Pi.single k Complex.I) ∂μ)) := by
      rw [show (∫ w in Metric.ball (0 : ℂ) ρ,
            dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) / w)
          = ∫ w in Metric.ball (0 : ℂ) ρ,
              ((1 / 2) * (w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w) (Pi.single k 1))
                + (1 / 2) * (Complex.I * (w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w) (Pi.single k Complex.I)))) from by
            apply integral_congr_ae
            filter_upwards with w
            rw [div_eq_mul_inv]
            exact hptR w]
      rw [integral_add (hAint.const_mul (1 / 2)) ((hBint.const_mul Complex.I).const_mul (1 / 2))]
      simp only [MeasureTheory.integral_const_mul]
      ring
    have hGfun : (fun y : Fin n → ℂ => ∫ w in Metric.ball (0 : ℂ) ρ,
          g (y + Function.update (0 : Fin n → ℂ) j w) / w)
        = fun y : Fin n → ℂ => ∫ w, g (y + Function.update (0 : Fin n → ℂ) j w) * w⁻¹ ∂μ := by
      funext y
      apply integral_congr_ae
      filter_upwards with w
      rw [div_eq_mul_inv]
    rw [hGfun, hLHS, hRHS]

end Work.CR.Flat.Cauchy
