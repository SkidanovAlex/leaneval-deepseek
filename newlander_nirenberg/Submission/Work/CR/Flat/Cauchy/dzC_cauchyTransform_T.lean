import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.dzC_integral_translate

namespace Work.CR.Flat.Cauchy

open MeasureTheory Set

/-- `∂_z` of a constant multiple: `∂_z(c · g) = c · ∂_z g`.

No differentiability hypothesis is needed: `fderiv` is `0` at a point where the function is not
differentiable, and multiplication by a nonzero constant preserves (non-)differentiability. -/
private lemma dzC_const_mul_aux (c : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    dzC (fun z => c * g z) z = c * dzC g z := by
  by_cases hc : c = 0
  · subst hc
    simp [dzC]
  · by_cases hg : DifferentiableAt ℝ g z
    · unfold dzC
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
      simp only [dzC, fderiv_zero_of_not_differentiableAt h2,
        fderiv_zero_of_not_differentiableAt hg, zero_apply, mul_zero, sub_zero]

/-- The `∂_z`-derivative of the Cauchy potential is the Cauchy potential of `∂_z f`:
`∂_z(T f) = T(∂_z f)`, i.e. the Cauchy transform `T` commutes with the flat `∂_z` operator.

Both sides equal `-(1/π) ∫_{‖w‖<ρ} (∂_zf (z+w) - ∂_zf z)/w`: the constant `-(1/π)` is pulled out
of `∂_z` (`dzC_const_mul_aux`) and differentiation under the integral sign is
`Work.CR.Flat.Cauchy.dzC_integral_translate`. -/
theorem dzC_cauchyTransform_T {ρ : ℝ} {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (z : ℂ) :
    dzC (cauchyTransform ρ f) z = cauchyTransform ρ (fun w => dzC f w) z := by
  have h1 : dzC (cauchyTransform ρ f) z
      = -((Real.pi : ℂ))⁻¹ *
          dzC (fun z : ℂ => ∫ w in Metric.ball (0 : ℂ) ρ, (f (z + w) - f z) / w) z :=
    dzC_const_mul_aux _ _ _
  rw [h1, dzC_integral_translate hf z]
  rfl

end Work.CR.Flat.Cauchy
