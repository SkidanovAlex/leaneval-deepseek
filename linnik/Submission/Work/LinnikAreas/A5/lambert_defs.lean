import Mathlib

namespace Work.LinnikAreas.A5

/-- The smoothed partial-summation weight used in HB §13.3:
`t ↦ t^{-(1-λ/log q)} · f(log t / log q)`.  The exponent `σ = 1 - λ/log q` is the
real point at which the von Mangoldt sum is evaluated, and `f` is a test function
supported in `[0,x₀]`. -/
noncomputable def lamWeight (q lam : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q)

end Work.LinnikAreas.A5
