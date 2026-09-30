import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For real `x ≥ 1`, the logarithm is dominated by the square root: `log x ≤ √x`.

Since `log x = 4 * log (x ^ (1/4))` and `log y ≤ y - 1` on `y > 0`, we get
`log x ≤ 4 (x^{1/4} - 1) = 4m - 4` with `m = x^{1/4}`, and `4m - 4 ≤ m² = √x`
because `(m - 2)² ≥ 0`. -/
lemma log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hx' : (0 : ℝ) < x := zero_lt_one.trans_le hx
  set m : ℝ := x ^ ((1 : ℝ) / 4) with hm
  have hm_pos : 0 < m := by rw [hm]; exact Real.rpow_pos_of_pos hx' _
  have hlog : Real.log x = 4 * Real.log m := by
    have h4 : m ^ 4 = x := by
      rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul hx'.le]
      norm_num
    rw [← h4, Real.log_pow]
    norm_num
  have hsq : m ^ 2 = Real.sqrt x := by
    rw [hm, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx'.le]
    norm_num
  calc Real.log x = 4 * Real.log m := hlog
    _ ≤ 4 * (m - 1) := by linarith [Real.log_le_sub_one_of_pos hm_pos]
    _ ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 2)]
    _ = Real.sqrt x := hsq

theorem log_le_sqrt (n : ℕ) (hn : 1 ≤ n) : Real.log n ≤ Real.sqrt n :=
  log_le_sqrt_of_one_le n (by exact_mod_cast hn)

end Work.BMF
