import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Inequalities

/-- The tail of the geometric series `∑ 2^{-d}` starting at `r + 2` is at most
`2^{-(r+1)}`; equivalently the geometric series is bounded by twice its first
term. -/
theorem sum_Icc_pow_half_le (r n : ℕ) :
    (∑ d ∈ Finset.Icc (r + 2) n, ((1 / 2 : ℝ)) ^ d) ≤ ((1 / 2 : ℝ)) ^ (r + 1) := by
  by_cases hn : n < r + 2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hn' : r + 2 ≤ n := by omega
    -- Key invariant: for `m ≥ r + 2`, the partial sum equals `2^{-(r+1)} - 2^{-m}`.
    have key : ∀ m, r + 2 ≤ m →
        (∑ d ∈ Finset.Icc (r + 2) m, ((1 / 2 : ℝ)) ^ d) ≤ ((1 / 2 : ℝ)) ^ (r + 1) - ((1 / 2 : ℝ)) ^ m := by
      intro m hm
      refine Nat.le_induction ?_ ?_ m hm
      · rw [Finset.Icc_self, Finset.sum_singleton]
        have : ((1 / 2 : ℝ)) ^ (r + 1) - ((1 / 2 : ℝ)) ^ (r + 2) = ((1 / 2 : ℝ)) ^ (r + 2) := by
          rw [pow_succ]; ring
        rw [this]
      · intro k hk ih
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hb : ((1 / 2 : ℝ)) ^ k = 2 * ((1 / 2 : ℝ)) ^ (k + 1) := by
          rw [pow_succ]; ring
        linarith [ih]
    have hkey := key n hn'
    have hpos : (0 : ℝ) ≤ ((1 / 2 : ℝ)) ^ n := by positivity
    linarith [hkey, hpos]

end Commons.Analysis.Inequalities