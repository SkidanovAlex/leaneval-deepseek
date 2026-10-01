import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

/-- Taylor-type upper bound for `√(1-u)` valid on `[0,1]`:
`√(1-u) ≤ 1 - u/2 - u^2/8 - u^3/16`. -/
theorem sqrt_one_sub_le_cubic_sum {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.sqrt (1 - u) ≤ 1 - u/2 - u^2/8 - u^3/16 := by
  have hA : 0 ≤ 1 - u/2 - u^2/8 - u^3/16 := by
    nlinarith [hu0, hu1, sq_nonneg u, sq_nonneg (1 - u)]
  rw [Real.sqrt_le_left hA]
  nlinarith [hu0, sq_nonneg u, sq_nonneg (u^2)]

end Commons.Analysis.Real