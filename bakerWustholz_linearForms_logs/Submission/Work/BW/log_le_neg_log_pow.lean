import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem log_le_neg_log_pow {a x : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) {n : ℕ}
    (h : a ^ n * x ≤ 1) : Real.log x ≤ (n : ℝ) * (- Real.log a) := by
  have hlog : Real.log a ≤ 0 := Real.log_nonpos ha0.le ha1
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- x = 0
    rw [← hx0, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg n) (neg_nonneg.mpr hlog)
  · -- 0 < x
    have hap : 0 < a ^ n := pow_pos ha0 n
    have hle : x ≤ (a ^ n)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hap]
      linarith [h]
    calc Real.log x ≤ Real.log ((a ^ n)⁻¹) := Real.log_le_log hxpos hle
      _ = - Real.log (a ^ n) := Real.log_inv _
      _ = - ((n : ℝ) * Real.log a) := by rw [Real.log_pow]
      _ = (n : ℝ) * (- Real.log a) := by ring

end Work.BW
