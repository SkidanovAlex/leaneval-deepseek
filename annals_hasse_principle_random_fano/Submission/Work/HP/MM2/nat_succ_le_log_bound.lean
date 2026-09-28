import Mathlib

namespace Work.HP.MM2

/-- If `2^J ≤ T` with `T ≥ 1`, then `J + 1 ≤ 4 (1 + log T)`. -/
theorem nat_succ_le_log_bound (T : ℝ) (J : ℕ) (hT : 1 ≤ T) (hJ : (2:ℝ)^J ≤ T) :
    (J : ℝ) + 1 ≤ 4 * (1 + Real.log T) := by
  have hpowpos : 0 < (2:ℝ)^J := by positivity
  have hlog := Real.log_le_log hpowpos hJ
  rw [Real.log_pow] at hlog
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hJ2 : (J:ℝ) * (1/2:ℝ) ≤ Real.log T := by
    have : (0:ℝ) ≤ (J:ℝ) := Nat.cast_nonneg J
    nlinarith
  have hTlog : 0 ≤ Real.log T := Real.log_nonneg hT
  nlinarith

end Work.HP.MM2
