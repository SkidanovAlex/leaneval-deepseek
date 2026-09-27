import Mathlib

namespace Work.EKLC6Core

open MeasureTheory ProbabilityTheory

/-- For a probability measure `ν` and `g ∈ L²(ν)`, the absolute value of `∫ g` is bounded by
the square root of `∫ g²`. This is a form of Cauchy–Schwarz (equivalently, `(∫ g)² ≤ ∫ g²`),
obtained here from the nonnegativity of the variance and `variance_eq_sub`. -/
theorem abs_integral_le_sqrt_integral_sq {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (g : X → ℝ) (hg : MeasureTheory.MemLp g 2 ν) :
    |∫ x, g x ∂ν| ≤ Real.sqrt (∫ x, (g x)^2 ∂ν) := by
  have hv := variance_nonneg g ν
  rw [variance_eq_sub hg] at hv
  simp only [Pi.pow_apply] at hv
  have hsq : (∫ x, g x ∂ν)^2 ≤ ∫ x, (g x)^2 ∂ν := by linarith
  calc |∫ x, g x ∂ν| = Real.sqrt ((∫ x, g x ∂ν)^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∫ x, (g x)^2 ∂ν) := Real.sqrt_le_sqrt hsq

end Work.EKLC6Core
