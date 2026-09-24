import Mathlib

/-!
# Basic API for the punctured-disc logarithmic estimate

This module collects the small definitions and easy lemmas used by
`Submission.Work.Potential.punctured_log_estimate`.

* `Work.Potential.grad u` is the *analytic gradient* `u_x - i u_y` of a function
  `u : ℂ → ℝ`; for a harmonic `u` it is complex analytic (Mathlib's
  `HarmonicAt.analyticAt_complex_partial`).  It is the derivative of any local
  holomorphic function whose real part is `u`.
* `Work.Potential.angMean u r` is the angular mean of `u` over the circle of
  radius `r`; it equals `2 * π * Real.circleAverage u 0 r`.
-/

noncomputable section

open scoped Real
open Complex

namespace Work.Potential

/-- The *analytic gradient* `u_x - i·u_y` of `u : ℂ → ℝ`. -/
def grad (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ u z) (1 : ℂ) : ℂ) - Complex.I * ((fderiv ℝ u z) Complex.I : ℂ)

/-- The angular mean of `u` over the circle of radius `r` centred at `0`. -/
def angMean (u : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I))

/-- The angular mean is `2π` times Mathlib's `circleAverage`. -/
theorem angMean_eq (u : ℂ → ℝ) (r : ℝ) :
    angMean u r = 2 * Real.pi * Real.circleAverage u 0 r := by
  rw [angMean, Real.circleAverage_def]
  simp only [circleMap_zero]
  rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul,
    mul_comm]

/-- The analytic gradient of a harmonic function is complex analytic. -/
theorem grad_analyticAt {u : ℂ → ℝ} {z : ℂ} (hu : InnerProductSpace.HarmonicAt u z) :
    AnalyticAt ℂ (grad u) z :=
  HarmonicAt.analyticAt_complex_partial hu

/-- `grad` is additive (pointwise sum). -/
theorem grad_add {u v : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    grad (u + v) z = grad u z + grad v z := by
  have h1 : fderiv ℝ (u + v) z = fderiv ℝ u z + fderiv ℝ v z := fderiv_add hu hv
  simp only [grad, h1, add_apply]
  push_cast
  ring

/-- `grad` is homogeneous. -/
theorem grad_const_mul (c : ℝ) (u : ℂ → ℝ) {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    grad (fun w => c * u w) z = (c : ℂ) * grad u z := by
  have h1 : fderiv ℝ (fun w => c * u w) z = c • fderiv ℝ u z := by
    rw [fderiv_const_mul hu]
  simp only [grad, h1, smul_apply, smul_eq_mul]
  push_cast
  ring

end Work.Potential
