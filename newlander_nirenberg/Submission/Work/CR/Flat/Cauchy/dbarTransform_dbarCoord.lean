import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- `∂̄` commutes with multiplication by a constant, with no regularity hypothesis: `fderiv` is
`0` at a point where the function is not differentiable, and multiplication by a nonzero constant
preserves (non-)differentiability. -/
lemma dbarCoord_const_mul_aux {n : ℕ} (j : Fin n) (c : ℂ) (g : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) :
    dbarCoord j (fun w => c * g w) z = c * dbarCoord j g z := by
  by_cases hg : DifferentiableAt ℝ g z
  · have h2 : fderiv ℝ (fun w => c * g w) z = c • fderiv ℝ g z := fderiv_const_mul hg c
    rw [dbarCoord, h2, dbarCoord]
    simp only [smul_apply, smul_eq_mul]
    ring
  · rcases eq_or_ne c 0 with hc | hc
    · subst hc
      have hzero : (fun w => (0 : ℂ) * g w) = Function.const (Fin n → ℂ) (0 : ℂ) := by
        funext w; rw [zero_mul]; rfl
      rw [hzero, dbarCoord, dbarCoord, fderiv_const, fderiv_zero_of_not_differentiableAt hg]
      simp
    · have h2 : ¬ DifferentiableAt ℝ (fun w => c * g w) z := by
        intro h
        refine hg ?_
        have h3 : DifferentiableAt ℝ (fun w => c⁻¹ * (c * g w)) z := h.const_mul c⁻¹
        convert h3 using 1
        ext w
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [dbarCoord, dbarCoord, fderiv_zero_of_not_differentiableAt h2,
        fderiv_zero_of_not_differentiableAt hg]
      simp

/-- Differentiation under the integral sign in the `∂̄`-direction for the Cauchy-type integral
taken in the `j`-th coordinate, with the necessary bound on `‖fderiv ℝ g‖` produced *internally*
by compactness (no support hypothesis on `g`).

The point is that only values of `fderiv ℝ g` on a *bounded* set are needed, so `C¹` `g` suffices:
`dbarCoord k (fun y => ∫_{‖w‖<ρ} g (y + w e_j)/w) z = ∫_{‖w‖<ρ} ∂̄_k g (z + w e_j)/w` for `0 < ρ`.

This is `Work.CR.Flat.Cauchy.dbarCoord_setIntegral_shift` with the global bound hypothesis `hM`
replaced by a local compactness argument, which is what `dbarTransform` needs (there `g` need not
be supported). -/
theorem dbarCoord_setIntegral_shift_local {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {j : Fin n}
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) (k : Fin n) (z : Fin n → ℂ) :
    dbarCoord k (fun y : Fin n → ℂ =>
        ∫ w in Metric.ball (0 : ℂ) ρ, g (y + Function.update (0 : Fin n → ℂ) j w) / w) z
      = ∫ w in Metric.ball (0 : ℂ) ρ,
          dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) / w := by
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
  have hgle : ∀ a : ℂ, ‖a‖ < ρ → ‖g (z + Function.update (0 : Fin n → ℂ) j a)‖ ≤ Cg := by
    intro a ha
    refine hCg _ ?_
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
  have hbound_int : Integrable (fun a : ℂ => C * ‖a‖ ^ (-1 : ℝ)) μ :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul C
  have hF_int : Integrable
      (fun a : ℂ => g (z + Function.update (0 : Fin n → ℂ) j a) * a⁻¹) μ := by
    have hmaj : Integrable (fun a : ℂ => Cg * ‖a‖ ^ (-1 : ℝ)) μ :=
      (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul Cg
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
            congr 1
            abel
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
      (fun y : Fin n → ℂ =>
        ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ)
      (∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ) z :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (α := ℂ) (E := ℂ)
      (H := Fin n → ℂ) (μ := μ)
      (F := fun y a => g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹)
      (F' := fun y a => a⁻¹ • fderiv ℝ g (y + Function.update (0 : Fin n → ℂ) j a))
      (bound := fun a => C * ‖a‖ ^ (-1 : ℝ))
      (s := Metric.ball z 1) (x₀ := z) (Metric.ball_mem_nhds z one_pos)
      (Filter.Eventually.of_forall hmeasF) hF_int hF'_meas h_bound hbound_int h_diff
  have hfd : fderiv ℝ (fun y : Fin n → ℂ =>
        ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ) z
      = ∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ :=
    hdiff.fderiv
  have hInt : Integrable
      (fun a : ℂ => a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)) μ :=
    hbound_int.mono' hF'_meas
      (h_bound.mono (fun a ha => ha z (Metric.mem_ball_self one_pos)))
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
      a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)
        (Pi.single k Complex.I)) μ :=
    (hInt.apply_continuousLinearMap (Pi.single k Complex.I)).congr
      (Filter.Eventually.of_forall fun a => hsmul_apply a (Pi.single k Complex.I))
  have hL1 : (∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ)
        (Pi.single k (1 : ℂ))
      = ∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)
          (Pi.single k 1) ∂μ := by
    rw [ContinuousLinearMap.integral_apply hInt]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => hsmul_apply a (Pi.single k 1))
  have hL2 : (∫ a, a⁻¹ • fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a) ∂μ)
        (Pi.single k Complex.I)
      = ∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)
          (Pi.single k Complex.I) ∂μ := by
    rw [ContinuousLinearMap.integral_apply hInt]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun a => hsmul_apply a (Pi.single k Complex.I))
  have hLHS : dbarCoord k (fun y : Fin n → ℂ =>
        ∫ a, g (y + Function.update (0 : Fin n → ℂ) j a) * a⁻¹ ∂μ) z
      = (1 / 2) * ((∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)
              (Pi.single k 1) ∂μ)
          + Complex.I * (∫ a, a⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j a)
              (Pi.single k Complex.I) ∂μ)) := by
    rw [dbarCoord, hfd, hL1, hL2]
  have hptR : ∀ w : ℂ, dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) * w⁻¹
      = (1 / 2) * (w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w)
            (Pi.single k 1))
        + (1 / 2) * (Complex.I * (w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w)
            (Pi.single k Complex.I))) := by
    intro w
    rw [dbarCoord]
    ring
  have hRHS : (∫ w in Metric.ball (0 : ℂ) ρ,
        dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      = (1 / 2) * ((∫ w, w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w)
              (Pi.single k 1) ∂μ)
          + Complex.I * (∫ w, w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w)
              (Pi.single k Complex.I) ∂μ)) := by
    rw [show (∫ w in Metric.ball (0 : ℂ) ρ,
          dbarCoord k g (z + Function.update (0 : Fin n → ℂ) j w) / w)
        = ∫ w in Metric.ball (0 : ℂ) ρ,
            ((1 / 2) * (w⁻¹ * fderiv ℝ g (z + Function.update (0 : Fin n → ℂ) j w)
                (Pi.single k 1))
              + (1 / 2) * (Complex.I * (w⁻¹ * fderiv ℝ g
                  (z + Function.update (0 : Fin n → ℂ) j w)
                (Pi.single k Complex.I)))) from by
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

/-- The Cauchy-type transform `dbarTransform` commutes with `∂̄` in the direction of another
(or the same) coordinate: `∂̄_k (T_j g) = T_j (∂̄_k g)`, where `T_j g z = -(1/π)∫_{‖w‖<ρ} g(z+w e_j)/w`.

Equivalently: the differentiation under the integral sign for `dbarTransform` does not see the
translation, since translating the argument of `g` shifts the differential by the identity, and
`∂̄_k` is sensitive only to the differential. -/
theorem dbarTransform_dbarCoord {n : ℕ} {ρ : ℝ} (j k : Fin n) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (z : Fin n → ℂ) :
    dbarCoord k (dbarTransform ρ j g) z
      = dbarTransform ρ j (fun y => dbarCoord k g y) z := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · have hempty : Metric.ball (0 : ℂ) ρ = ∅ := Metric.ball_eq_empty.mpr hρ
    have h1 : dbarTransform ρ j g = fun _ : Fin n → ℂ => 0 := by
      funext y
      simp [dbarTransform, hempty]
    have h2 : dbarTransform ρ j (fun y => dbarCoord k g y) z = 0 := by
      simp [dbarTransform, hempty]
    rw [h1, h2]
    simp [dbarCoord]
  · have h1 : dbarCoord k (dbarTransform ρ j g) z
        = -((Real.pi : ℂ))⁻¹ * dbarCoord k (fun y : Fin n → ℂ =>
            ∫ w in Metric.ball (0 : ℂ) ρ,
              g (y + Function.update (0 : Fin n → ℂ) j w) / w) z := by
      rw [show dbarTransform ρ j g = fun y : Fin n → ℂ =>
          -((Real.pi : ℂ))⁻¹ * (∫ w in Metric.ball (0 : ℂ) ρ,
            g (y + Function.update (0 : Fin n → ℂ) j w) / w) from rfl]
      exact dbarCoord_const_mul_aux k _ _ z
    rw [h1, dbarCoord_setIntegral_shift_local hρ hg k z]
    rfl

end Work.CR.Flat.Cauchy
