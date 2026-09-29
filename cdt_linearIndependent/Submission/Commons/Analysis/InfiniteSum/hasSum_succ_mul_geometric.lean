import Mathlib.Analysis.SpecificLimits.Normed

namespace Commons.Analysis.InfiniteSum

/-- `Σₙ (n+1)·xⁿ = 1/(1−x)²` for real `x` with `‖x‖ < 1`.

This is the case `k = 1` of the binomial-geometric series
`Σₙ (n+k choose k)·xⁿ = 1/(1−x)^(k+1)`, together with `(n+1).choose 1 = n+1`. -/
theorem hasSum_succ_mul_geometric {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * x ^ n) (1 / (1 - x) ^ 2) := by
  simpa [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    (hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := x) hx)

end Commons.Analysis.InfiniteSum