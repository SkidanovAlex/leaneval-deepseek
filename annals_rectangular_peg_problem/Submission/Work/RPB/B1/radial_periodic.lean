import Mathlib
import Submission.Work.RPB.B1.PolarDefs

/-!
# `Work.RPB.B1.radial_periodic`

The angular kernel `θ ↦ (C e^{-iθ}).im` and the radial extent `radial a R θ = Re (a e^{-iθ}) +
√(R² - Im (a e^{-iθ})²)` are both `2π`-periodic in the angle `θ`, because `θ ↦ e^{-iθ}` is.

This is used to push the integrand `(C e^{-iθ}).im · radial a R θ` down to the circle.
-/

namespace Work.RPB.B1

open Complex

noncomputable section

/-- The exponential `θ ↦ e^{-iθ}` is periodic of period `2π`. -/
lemma exp_neg_mul_I_periodic :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I)) (2 * Real.pi) := by
  intro θ
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-1, ?_⟩
  push_cast
  ring

/-- The radial extent `radial a R` is periodic of period `2π`. -/
lemma radial_periodic_radial (a : ℂ) (R : ℝ) :
    Function.Periodic (radial a R) (2 * Real.pi) := by
  intro θ
  have hE := exp_neg_mul_I_periodic θ
  simp only [radial, hE]

/-- The angular kernel `θ ↦ (C e^{-iθ}).im` is periodic of period `2π`. -/
lemma kernel_periodic (C : ℂ) :
    Function.Periodic (fun θ : ℝ => (C * Complex.exp (-(θ : ℂ) * Complex.I)).im) (2 * Real.pi) := by
  intro θ
  have hE := exp_neg_mul_I_periodic θ
  simp only [hE]

theorem radial_periodic (a C : ℂ) (R : ℝ) : Function.Periodic (fun θ : ℝ => (C * Complex.exp (-(θ : ℂ) * Complex.I)).im * radial a R θ) (2 * Real.pi) := by
  intro θ
  have hE := exp_neg_mul_I_periodic θ
  simp only [radial, hE]

end

end Work.RPB.B1
