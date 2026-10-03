import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.R6.polarBox_tau3_inner_le

namespace Work.FIArea2.R6

/-- `Finset.range (X+1)` and `Finset.Icc 0 X` are the same set of naturals. -/
private lemma range_succ_eq_Icc_zero (X : ℕ) : Finset.range (X + 1) = Finset.Icc 0 X := by
  ext n
  simp [Finset.mem_range, Finset.mem_Icc]

/-- The second moment of the ternary divisor function `τ₃` over `n ≤ X`:

  `∑_{n ≤ X} τ₃(n)² ≤ C·(X+1)·(log X + 2)^16`.

Immediate from `Work.FIArea2.R6.sum_tau3_sq_Icc_le`, the corresponding bound for the interval
`Icc 0 X`, once one identifies `range (X+1) = Icc 0 X`. -/
theorem sum_tau3_sq_range_le :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.range (X + 1), ((Work.FIArea2.R6.tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ := Work.FIArea2.R6.sum_tau3_sq_Icc_le
  refine ⟨C, hC, fun X => ?_⟩
  rw [range_succ_eq_Icc_zero X]
  exact hbound X

end Work.FIArea2.R6
