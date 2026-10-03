import Mathlib

namespace Work.Pert

/-- `exp (1/64) ≤ 1.02`.  Taylor's estimate `Real.exp_bound'` at order `2` gives
`exp x ≤ 1 + x + x^2/2 + 3x^2/4`, and at `x = 1/64` the right-hand side is `< 1.02`. -/
theorem exp_inv_64_le : Real.exp (1 / 64) ≤ 1.02 := by
  have h := Real.exp_bound' (x := (1 / 64 : ℝ)) (by norm_num) (by norm_num) (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

end Work.Pert
