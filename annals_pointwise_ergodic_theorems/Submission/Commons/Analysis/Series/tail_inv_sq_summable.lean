import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries

namespace Commons.Analysis.Series

/-- The tail `∑_{n ≥ N} 1/n²` is summable: the terms are dominated by `1/n²`,
which is summable. -/
theorem tail_inv_sq_summable (N : ℕ) :
    Summable (fun n : ℕ => (if N ≤ n then 1 / (n : ℝ)^2 else 0)) := by
  have hg : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^2)
    (g := fun n : ℕ => (if N ≤ n then 1 / (n : ℝ)^2 else 0)) ?_ ?_ hg
  · intro n
    by_cases h : N ≤ n
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
  · intro n
    by_cases h : N ≤ n
    · rw [if_pos h]
    · rw [if_neg h]
      positivity

end Commons.Analysis.Series