import Mathlib

namespace Commons.Analysis.Real

/-- For `0 ≤ u`, the crude quadratic `u - u^2/2` is a lower bound for `log (1 + u)`.
Here `u₀ < 1` and `u ≤ u₀` are unused extra hypotheses supplied by the caller. -/
theorem log_one_add_lower {u₀ u : ℝ} (hu₀ : u₀ < 1) (hu0 : 0 ≤ u) (huu₀ : u ≤ u₀) :
    u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  calc
    u - u ^ 2 / 2 ≤ 2 * u / (u + 2) := by
      have hx2 : 0 < u + 2 := by linarith
      rw [le_div_iff₀ hx2]
      nlinarith [mul_nonneg hu0 (sq_nonneg u)]
    _ ≤ Real.log (1 + u) := Real.le_log_one_add_of_nonneg hu0

end Commons.Analysis.Real
