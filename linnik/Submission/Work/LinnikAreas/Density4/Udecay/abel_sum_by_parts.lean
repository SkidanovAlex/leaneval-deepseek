import Mathlib
import Submission.Work.LinnikAreas.Density4.Udecay.mellin_defs

namespace Work.LinnikAreas.Density4.Udecay

/-- Finite Abel summation by parts. With `A m = Σ_{n ≤ m} a n` the partial sums of `a`, the
Abel-weighted sum against the differences `g m - g (m+1)` equals the plain weighted sum minus the
boundary term `A M * g (M+1)`. -/
theorem abel_sum_by_parts (a g : ℕ → ℝ) (M : ℕ) :
    (∑ m ∈ Finset.range (M + 1),
        (∑ n ∈ Finset.range (m + 1), a n) * (g m - g (m + 1)))
      = (∑ n ∈ Finset.range (M + 1), a n * g n)
        - (∑ n ∈ Finset.range (M + 1), a n) * g (M + 1) := by
  induction M with
  | zero => simp; ring
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ (fun n => a n * g n) (M + 1),
        Finset.sum_range_succ (fun n => a n) (M + 1)]
    ring

end Work.LinnikAreas.Density4.Udecay
