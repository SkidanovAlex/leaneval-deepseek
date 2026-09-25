import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.cauchyTransform_eq_unsub
import Submission.Work.CR.Flat.Cauchy.cauchyGreen_origin
import Submission.Work.CR.Flat.Cauchy.dbarC_integral_translate

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- `∂̄` of a constant multiple: `∂̄(c · g) = c · ∂̄g`.

No differentiability hypothesis is needed: `fderiv` is `0` at a point where the function is not
differentiable, and multiplication by a nonzero constant preserves (non-)differentiability. -/
lemma dbarC_const_mul (c : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    dbarC (fun z => c * g z) z = c * dbarC g z := by
  by_cases hc : c = 0
  · subst hc
    simp [dbarC]
  · by_cases hg : DifferentiableAt ℝ g z
    · unfold dbarC
      rw [fderiv_const_mul hg c]
      simp only [smul_apply, smul_eq_mul]
      ring
    · have h2 : ¬ DifferentiableAt ℝ (fun z => c * g z) z := by
        intro h
        refine hg ?_
        have h3 : DifferentiableAt ℝ (fun z => c⁻¹ * (c * g z)) z := h.const_mul c⁻¹
        convert h3 using 1
        ext w
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      simp only [dbarC, fderiv_zero_of_not_differentiableAt h2,
        fderiv_zero_of_not_differentiableAt hg, zero_apply, mul_zero, add_zero]

/-- Translation is `∂̄`-invariant: `∂̄(f ∘ (z + ·)) = (∂̄f) ∘ (z + ·)`. -/
lemma dbarC_shift {f : ℂ → ℂ} (z w : ℂ) :
    dbarC (fun w : ℂ => f (z + w)) w = dbarC f (z + w) := by
  simp only [dbarC, fderiv_comp_add_left]

/-- `∂̄f` is continuous when `f` is `C¹`. -/
lemma continuous_dbarC {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dbarC f) := by
  have h1 : Continuous (fun z : ℂ => fderiv ℝ f z) := hf.continuous_fderiv one_ne_zero
  have h2 : Continuous (fun z : ℂ => fderiv ℝ f z (1 : ℂ)) := h1.clm_apply continuous_const
  have h3 : Continuous (fun z : ℂ => fderiv ℝ f z Complex.I) := h1.clm_apply continuous_const
  rw [show dbarC f = fun z : ℂ =>
      (1 / 2 : ℂ) * (fderiv ℝ f z (1 : ℂ) + Complex.I * fderiv ℝ f z Complex.I) from rfl]
  exact continuous_const.mul (h2.add (continuous_const.mul h3))

/-- Integrability of `ζ ↦ g ζ / ζ` on a disc for continuous `g`: the `1/ζ` singularity is
integrable in the plane, so `‖g ζ / ζ‖ ≤ C ‖ζ‖ ^ (-1)` with `C` a bound for `‖g‖` on the closed
disc. -/
lemma integrableOn_div_of_continuous {g : ℂ → ℂ} (hg : Continuous g) (ρ : ℝ) :
    IntegrableOn (fun ζ : ℂ => g ζ / ζ) (Metric.ball (0 : ℂ) ρ) := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [Metric.ball_eq_empty.mpr hρ]
    simp
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    hg.continuousOn
  have hbound : IntegrableOn (fun ζ : ℂ => C * ‖ζ‖ ^ (-1 : ℝ)) (Metric.ball (0 : ℂ) ρ) :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul C
  refine hbound.mono' ((hg.measurable.div measurable_id).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with ζ hζ
  rw [norm_div, Real.rpow_neg_one, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hC ζ (Metric.ball_subset_closedBall hζ))
    (inv_nonneg.mpr (norm_nonneg ζ))

/-- The shifted Cauchy–Green (Pompeiu) formula in the "subtracted" form used by the Cauchy
potential: for `f` supported in the disc of radius `ρ/2` and `‖z‖ < ρ/2`,
`-(1/π) ∫_{‖ζ‖<ρ} (∂̄f (z+ζ) - ∂̄f z)/ζ dA(ζ) = f z`.

This is `cauchyGreen_origin` applied to `w ↦ f (z + w)` (whose support radius is at most
`ρ/2 + ‖z‖ < ρ`), using `∂̄(f ∘ (z + ·)) = (∂̄f) ∘ (z + ·)` and the symmetry
`∫_{‖ζ‖<ρ} ζ⁻¹ = 0` to remove the constant part `∂̄f z / ζ`. -/
lemma cauchyGreen_shift {ρ : ℝ} (hρ : 0 < ρ) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : SupportedInBall (ρ / 2) f) {z : ℂ} (hz : ‖z‖ < ρ / 2) :
    -((Real.pi : ℂ))⁻¹ *
        ∫ ζ in Metric.ball (0 : ℂ) ρ, (dbarC f (z + ζ) - dbarC f z) / ζ = f z := by
  have hgsupp : SupportedInBall ρ (fun w : ℂ => f (z + w)) := by
    intro w hw
    refine hfsupp (z + w) ?_
    have h1 : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
      have : w = (z + w) - z := by ring
      conv_lhs => rw [this]
      exact norm_sub_le _ _
    linarith
  have hg : ContDiff ℝ 1 (fun w : ℂ => f (z + w)) := hf.comp (contDiff_const.add contDiff_id)
  have h := cauchyGreen_origin hρ hg hgsupp
  simp only [add_zero] at h
  rw [setIntegral_congr_fun measurableSet_ball
    (fun ζ (_ : ζ ∈ Metric.ball (0 : ℂ) ρ) => by rw [dbarC_shift])] at h
  have hzero : ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f z / ζ = 0 := by
    rw [show (fun ζ : ℂ => dbarC f z / ζ) = fun ζ : ℂ => dbarC f z * ζ⁻¹ by
      funext ζ; rw [div_eq_mul_inv]]
    rw [integral_const_mul, integral_inv_ball ρ, mul_zero]
  have hBint : IntegrableOn (fun ζ : ℂ => dbarC f z / ζ) (Metric.ball (0 : ℂ) ρ) := by
    rw [show (fun ζ : ℂ => dbarC f z / ζ) = fun ζ : ℂ => dbarC f z * ζ⁻¹ by
      funext ζ; rw [div_eq_mul_inv]]
    exact (integrableOn_inv_ball ρ).const_mul (dbarC f z)
  have hAint : IntegrableOn (fun ζ : ℂ => (dbarC f (z + ζ) - dbarC f z) / ζ)
      (Metric.ball (0 : ℂ) ρ) := by
    have hc : IntegrableOn (fun ζ : ℂ => dbarC f (z + ζ) / ζ) (Metric.ball (0 : ℂ) ρ) :=
      integrableOn_div_of_continuous (g := fun ζ : ℂ => dbarC f (z + ζ))
        ((continuous_dbarC hf).comp (by fun_prop)) ρ
    have h2 : (fun ζ : ℂ => dbarC f (z + ζ) / ζ - dbarC f z / ζ)
        = fun ζ : ℂ => (dbarC f (z + ζ) - dbarC f z) / ζ := by
      funext ζ
      rw [sub_div]
    rw [← h2]
    exact hc.sub hBint
  have hsplit : ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f (z + ζ) / ζ
      = ∫ ζ in Metric.ball (0 : ℂ) ρ, (dbarC f (z + ζ) - dbarC f z) / ζ := by
    have h1 : ∫ ζ in Metric.ball (0 : ℂ) ρ, dbarC f (z + ζ) / ζ
        = ∫ ζ in Metric.ball (0 : ℂ) ρ,
            ((dbarC f (z + ζ) - dbarC f z) / ζ + dbarC f z / ζ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro ζ _
      show dbarC f (z + ζ) / ζ = (dbarC f (z + ζ) - dbarC f z) / ζ + dbarC f z / ζ
      rw [← add_div, sub_add_cancel]
    rw [h1, integral_add hAint hBint, hzero, add_zero]
  rw [hsplit] at h
  exact h

/-- The Cauchy potential solves the `∂̄`-equation: `∂̄(T f) = f`.

For a `C¹` function `f` supported in the disc of radius `ρ/2` and `‖z‖ < ρ/2`,
differentiating `T f z = -(1/π) ∫_{‖w‖<ρ} f (z+w)/w` under the integral sign
(`cauchyTransform_eq_unsub`) gives
`∂̄ (T f) z = -(1/π) ∫_{‖w‖<ρ} (∂̄f)(z+w)/w dw
          = -(1/π) ∫_{ball 0 ρ} (∂̄f)(ζ)/(ζ-z) dA = f z`
by Pompeiu's formula; the change of variables `ζ = z+w` is legitimate because
`∂̄f` is supported in `ball 0 (ρ/2) ⊆ ball z ρ`.

Here `dbarC u z = (1/2)(∂_x u z + i ∂_y u z)` and
`cauchyTransform ρ f z = -(1/π) ∫_{‖w‖<ρ} (f (z+w) - f z)/w`. -/
theorem dbarC_cauchyTransform {ρ : ℝ} (hρ : 0 < ρ) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : SupportedInBall (ρ / 2) f) {z : ℂ} (hz : ‖z‖ < ρ / 2) :
    dbarC (cauchyTransform ρ f) z = f z := by
  -- Step 1: pull the normalisation constant `-(1/π)` out of `∂̄`.
  have h1 : dbarC (cauchyTransform ρ f) z
      = -((Real.pi : ℂ))⁻¹ *
          dbarC (fun z : ℂ => ∫ w in Metric.ball (0 : ℂ) ρ, (f (z + w) - f z) / w) z :=
    dbarC_const_mul _ _ _
  -- Step 2: differentiate under the integral sign.
  rw [h1, dbarC_integral_translate hf z]
  -- Steps 3 and 4: the shifted Cauchy–Green formula.
  exact cauchyGreen_shift hρ hf hfsupp hz

end Work.CR.Flat.Cauchy
