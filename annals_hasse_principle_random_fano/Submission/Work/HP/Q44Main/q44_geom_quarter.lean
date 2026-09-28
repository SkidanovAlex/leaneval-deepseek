import Mathlib

namespace Work.HP.Q44Main

/-- The partial sums of the geometric series with ratio `1/4` are bounded by
its limit `4/3`. -/
theorem q44_geom_quarter (n : ℕ) :
    (∑ i ∈ Finset.range n, ((1 : ℝ) / 4) ^ i) ≤ 4 / 3 := by
  rw [geom_sum_eq (by norm_num : ((1 : ℝ) / 4) ≠ 1)]
  have h : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ n := by positivity
  rw [div_le_iff_of_neg (by norm_num : ((1 : ℝ) / 4 - 1) < 0)]
  ring_nf
  linarith

end Work.HP.Q44Main
