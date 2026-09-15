import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Measure.EuclideanSpace

open MeasureTheory Metric Filter Set
open scoped Topology RealInnerProductSpace

/-- **Translation invariance of the integral along a line.** For a unit vector `y`, a point `x₀`
perpendicular to `y` and a real `s`, the integral of `t ↦ f (x₀ + s • y + t • y)` equals the
integral of `t ↦ f (x₀ + t • y)` (substitute `u = s + t`; Lebesgue measure on `ℝ` is translation
invariant). -/
theorem integral_line_shift {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x₀ y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ = 1) (hperp : inner ℝ x₀ y = 0) (s : ℝ) :
    (∫ t : ℝ, f (x₀ + s • y + t • y)) = ∫ t : ℝ, f (x₀ + t • y) := by
  have hfun : (fun t : ℝ => f (x₀ + s • y + t • y))
      = fun t : ℝ => (fun u : ℝ => f (x₀ + u • y)) (s + t) := by
    funext t
    congr 1
    rw [add_assoc, ← add_smul]
  rw [hfun]
  exact integral_add_left_eq_self (fun u : ℝ => f (x₀ + u • y)) s

end Commons.Measure.EuclideanSpace