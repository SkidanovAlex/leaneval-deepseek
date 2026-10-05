import Mathlib
import Submission.Work.RPB.B1.PolarDefs

/-!
# The radial slice of the polar integrand

For `‖a‖ < R` and a fixed angle `φ`, the radial slice `r ↦ 1_{polarTarget}(r, φ) ·
polarIntegrand a C R (r, φ)` of the polar integrand is the step function

`r ↦ 1_{0 < r < radial a R φ} · (C e^{-iφ}).im`,

which integrates to `(C e^{-iφ}).im · radial a R φ`.  Since `polarTarget` additionally forces
`φ ∈ (-π, π)`, the slice is identically zero off that interval; this is the statement proved here:

`∫ r, (polarTarget.indicator (polarIntegrand a C R)) (r, φ)
   = 1_{(-π,π)}(φ) · ((C e^{-iφ}).im · radial a R φ)`.

The only analytic input is the positivity `0 < radial a R φ` of the radial extent, which follows
from `‖a‖ < R` (the disc `ball a R` contains the origin in its interior).
-/

namespace Work.RPB.B1

open MeasureTheory Set Complex Real
open scoped Real

noncomputable section

/-- Positivity of the radial extent of the disc `ball a R` in the direction `φ`, for `‖a‖ < R`:
writing `z = a e^{-iφ}` one has `z.re ^ 2 + z.im ^ 2 = ‖a‖ ^ 2 < R ^ 2`, so
`|z.re| < sqrt (R ^ 2 - z.im ^ 2)` and `radial a R φ = z.re + sqrt (R ^ 2 - z.im ^ 2) > 0`. -/
theorem radial_pos_of_norm_lt (a : ℂ) {R : ℝ} (hR : ‖a‖ < R) (φ : ℝ) :
    0 < radial a R φ := by
  have hnorm : ‖a * Complex.exp (-(φ : ℂ) * Complex.I)‖ = ‖a‖ := by
    rw [norm_mul, Complex.norm_exp]; simp
  have hsq : (a * Complex.exp (-(φ : ℂ) * Complex.I)).re ^ 2
      + (a * Complex.exp (-(φ : ℂ) * Complex.I)).im ^ 2 = ‖a‖ ^ 2 := by
    have h1 := Complex.normSq_apply (a * Complex.exp (-(φ : ℂ) * Complex.I))
    rw [Complex.normSq_eq_norm_sq, hnorm] at h1
    nlinarith [h1]
  set z := a * Complex.exp (-(φ : ℂ) * Complex.I) with hz
  have hsq' : z.re ^ 2 + z.im ^ 2 = ‖a‖ ^ 2 := by rw [hz]; exact hsq
  have him2 : z.im ^ 2 ≤ ‖a‖ ^ 2 := by nlinarith [hsq', sq_nonneg z.re]
  have hpos : 0 < R ^ 2 - z.im ^ 2 := by nlinarith [hR, norm_nonneg a, him2]
  simp only [radial, ← hz]
  rcases le_total 0 z.re with hx | hx
  · have := Real.sqrt_pos.2 hpos
    linarith
  · have hre2 : z.re ^ 2 < R ^ 2 - z.im ^ 2 := by nlinarith [hR, norm_nonneg a, hsq']
    have hsqrt : Real.sqrt (z.re ^ 2) < Real.sqrt (R ^ 2 - z.im ^ 2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) hre2
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos hx] at hsqrt
    linarith

/-- The radial slice of the polar integrand at an angle `φ ∈ (-π, π)` is the step function
`1_{0 < r < radial a R φ} · (C e^{-iφ}).im`. -/
private theorem slice_eq (a C : ℂ) (R : ℝ) {φ : ℝ} (hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi) :
    (fun r : ℝ => (polarTarget.indicator (polarIntegrand a C R)) (r, φ))
      = Set.indicator (Set.Ioo (0 : ℝ) (radial a R φ))
          (fun _ => (C * Complex.exp (-(φ : ℂ) * Complex.I)).im) := by
  funext r
  simp only [Set.indicator_apply, polarTarget, Complex.polarCoord_target, Set.mem_prod,
    Set.mem_Ioi, Set.mem_Ioo, polarIntegrand]
  by_cases hr : 0 < r
  · by_cases hr2 : r < radial a R φ <;> simp [hφ.1, hφ.2, hr, hr2]
  · simp [hφ.1, hφ.2, hr]

/-- Off the angular interval `(-π, π)` the radial slice is identically zero, because
`(r, φ) ∉ polarTarget` for every `r`. -/
private theorem slice_eq_zero (a C : ℂ) (R : ℝ) {φ : ℝ} (hφ : φ ∉ Set.Ioo (-Real.pi) Real.pi) :
    (fun r : ℝ => (polarTarget.indicator (polarIntegrand a C R)) (r, φ)) = fun _ => (0 : ℝ) := by
  funext r
  exact Set.indicator_of_notMem (s := polarTarget) (a := (r, φ))
    (fun h => hφ h.2) (polarIntegrand a C R)

theorem polarIntegrand_slice (a C : ℂ) {R : ℝ} (hR : ‖a‖ < R) (φ : ℝ) :
    ∫ r : ℝ, (polarTarget.indicator (polarIntegrand a C R)) (r, φ)
      = (Set.Ioo (-Real.pi) Real.pi).indicator
          (fun φ => (C * Complex.exp (-(φ : ℂ) * Complex.I)).im * radial a R φ) φ := by
  classical
  by_cases hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi
  · rw [Set.indicator_of_mem hφ]
    rw [slice_eq a C R hφ, MeasureTheory.integral_indicator measurableSet_Ioo,
      MeasureTheory.setIntegral_const, Real.volume_real_Ioo, sub_zero,
      max_eq_left (le_of_lt (radial_pos_of_norm_lt a hR φ)), smul_eq_mul, mul_comm]
  · rw [Set.indicator_of_notMem hφ, slice_eq_zero a C R hφ, MeasureTheory.integral_zero]

end

end Work.RPB.B1
