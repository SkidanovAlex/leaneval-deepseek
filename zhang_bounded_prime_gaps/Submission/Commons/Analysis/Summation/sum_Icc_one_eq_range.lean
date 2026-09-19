import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Submission.Commons.Analysis.Summation.abel_prefix_bound

namespace Commons.Analysis.Summation

/-- Reindex a sum over `Icc 1 q` as a sum over `range q` of the shifted argument. -/
theorem sum_Icc_one_eq_range (q : ℕ) (h : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 q, h a) = ∑ k ∈ Finset.range q, h (k + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (f := h) (Nat.le_add_left 1 q), ih,
      Finset.sum_range_succ]

end Commons.Analysis.Summation