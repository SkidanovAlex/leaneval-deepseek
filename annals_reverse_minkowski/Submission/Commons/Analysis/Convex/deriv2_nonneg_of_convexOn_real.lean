import Mathlib.Analysis.Convex.Deriv

namespace Commons.Analysis.Convex

open Set

/-- A convex differentiable real function has nonnegative second derivative everywhere: the
derivative of a convex function is monotone (`ConvexOn.monotoneOn_deriv`), and a monotone function
has nonnegative derivative (`Monotone.deriv_nonneg`). -/
theorem deriv2_nonneg_of_convexOn_real {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hfd : ∀ x, DifferentiableAt ℝ f x) : ∀ x, 0 ≤ deriv (deriv f) x := by
  intro x
  have hmonoOn : MonotoneOn (deriv f) Set.univ :=
    hconv.monotoneOn_deriv fun y _ => hfd y
  have hmono : Monotone (deriv f) := monotoneOn_univ.mp hmonoOn
  exact hmono.deriv_nonneg

end Commons.Analysis.Convex
