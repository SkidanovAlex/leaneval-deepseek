import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `0 < B ≤ 1` and `n ≤ M`, `1 / B ^ n ≤ exp (M * |log B|)`; used to convert the
2-adic integrality bound at a finite place into an exponential bound. -/
theorem one_div_pow_le_exp {B : ℝ} (h0 : 0 < B) (h1 : B ≤ 1) {n : ℕ} {M : ℝ}
    (hM : (n : ℝ) ≤ M) :
    1 / B ^ n ≤ Real.exp (M * |Real.log B|) := by
  have hlog : Real.log B ≤ 0 := Real.log_nonpos (le_of_lt h0) h1
  have habs : |Real.log B| = -Real.log B := abs_of_nonpos hlog
  have hpos : 0 < B ^ n := pow_pos h0 n
  -- `1 / B ^ n = exp (n * |log B|)` since `B = exp (log B)` and `log B ≤ 0`.
  have key : 1 / B ^ n = Real.exp ((n : ℝ) * |Real.log B|) := by
    rw [one_div, ← Real.exp_log hpos, ← Real.exp_neg,
      show -Real.log (B ^ n) = (n : ℝ) * |Real.log B| from by
        rw [Real.log_pow, habs]; ring]
  rw [key]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hM (abs_nonneg _))

end Work.BW
