import Mathlib

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

/-- Pointwise (in `x`) bound of the convolution error by the `L¹`-difference against the
translated function: since `∫ v = 1`, the identity
`h x - (h ⋆ v) x = ∫ y, (h x - h (x - y)) * v y` (Bochner integral against Lebesgue measure)
and `‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ` give the claim.  Needed for `Work.KMTAreas.A4.offConvMoment`. -/
theorem convPointwiseEnormLe (h v : SchwartzMap ℝ ℂ) (hv1 : ∫ y : ℝ, v y = 1) (x : ℝ) :
    ‖h x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v x‖ₑ
      ≤ ∫⁻ y : ℝ, ‖h x - h (x - y)‖ₑ * ‖v y‖ₑ := by
  -- `(h ⋆ v) x` is the integral of `h (x - y) * v y` (Bochner integral against Lebesgue measure).
  have hconv : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v x
      = ∫ y : ℝ, h (x - y) * v y := by
    rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    simpa using integral_sub_left_eq_self (fun z : ℝ => h (x - z) * v z) volume x
  -- The `∫ v = 1` normalisation turns `h x` into the integral of the constant `h x` against `v`.
  have hx1 : (∫ y : ℝ, h x * v y) = h x := by
    rw [MeasureTheory.integral_const_mul, hv1, mul_one]
  -- Integrability of the two integrands whose difference is the convolution error.
  have h1 : Integrable (fun y : ℝ => h x * v y) volume := v.integrable.const_mul (h x)
  have h2 : Integrable (fun y : ℝ => h (x - y) * v y) volume := by
    refine v.integrable.bdd_mul (c := (SchwartzMap.seminorm ℝ 0 0) h)
      (h.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
    filter_upwards with y
    exact SchwartzMap.norm_le_seminorm ℝ h (x - y)
  -- The pointwise identity of the docstring.
  have hdiff : h x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h v x
      = ∫ y : ℝ, (h x - h (x - y)) * v y := by
    rw [hconv]
    calc h x - ∫ y : ℝ, h (x - y) * v y
        = (∫ y : ℝ, h x * v y) - ∫ y : ℝ, h (x - y) * v y := by
            conv_lhs => rw [← hx1]
      _ = ∫ y : ℝ, (h x * v y - h (x - y) * v y) := (MeasureTheory.integral_sub h1 h2).symm
      _ = ∫ y : ℝ, (h x - h (x - y)) * v y := by simp only [sub_mul]
  rw [hdiff]
  simpa only [enorm_mul] using
    enorm_integral_le_lintegral_enorm (fun y : ℝ => (h x - h (x - y)) * v y)

end Work.KMTAreas.A4
