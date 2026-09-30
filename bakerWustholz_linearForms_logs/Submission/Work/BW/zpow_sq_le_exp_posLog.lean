import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For a positive real `b`, the positive part of the logarithm of `b ^ 2`
equals `2 * log (max b 1)`. -/
lemma posLog_sq_eq {b : ℝ} (hb : 0 < b) :
    Real.posLog (b ^ 2) = 2 * Real.log (max b 1) := by
  rcases le_or_gt 1 b with hb1 | hb1
  · have hmax1 : max b 1 = b := max_eq_left hb1
    have hmax2 : max (1 : ℝ) (b ^ 2) = b ^ 2 := max_eq_right (one_le_pow₀ hb1)
    rw [Real.posLog_eq_log_max_one (by positivity), hmax2, hmax1, Real.log_pow]
    push_cast
    ring
  · have hmax1 : max b 1 = 1 := max_eq_right hb1.le
    have hb2le : b ^ 2 ≤ 1 := by nlinarith [hb, hb1]
    have hmax2 : max (1 : ℝ) (b ^ 2) = 1 := max_eq_left hb2le
    rw [Real.posLog_eq_log_max_one (by positivity), hmax2, hmax1, Real.log_one, mul_zero]

theorem zpow_sq_le_exp_posLog {a b : ℝ} (hb : 0 < b) (hba : b ^ 2 = a) (N : ℤ) (t : ℝ)
    (hN : 0 ≤ N) (ht : (N : ℝ) / 2 ≤ t) :
    b ^ N ≤ Real.exp (t * a.posLog) := by
  rw [← hba, posLog_sq_eq hb]
  set m := max b 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hbm : b ≤ m := le_max_left _ _
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm1
  rw [show t * (2 * Real.log m) = Real.log m * (2 * t) by ring]
  rw [← Real.rpow_def_of_pos hmpos (2 * t)]
  calc b ^ N ≤ m ^ N := zpow_le_zpow_left₀ hN hb.le hbm
    _ = m ^ (N : ℝ) := (Real.rpow_intCast m N).symm
    _ ≤ m ^ (2 * t) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

end Work.BW
