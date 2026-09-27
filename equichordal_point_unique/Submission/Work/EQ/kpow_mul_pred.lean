import Mathlib

namespace Work.EQ

/-- For `0 < κ < 1` and `n : ℕ`, `n * κ ^ (n - 1) ≤ 1 / (1 - κ)`.
This follows from Bernoulli's inequality applied with `a = κ` and `b = 1 - κ`. -/
theorem kpow_mul_pred {κ : ℝ} (h0 : 0 < κ) (h1 : κ < 1) (n : ℕ) :
    (n : ℝ) * κ ^ (n - 1) ≤ 1 / (1 - κ) := by
  have hκ1 : 0 < 1 - κ := by linarith
  have hb := pow_add_mul_le_add_pow (a := κ) (b := 1 - κ) h0.le (by linarith) n
  rw [add_sub_cancel, one_pow] at hb
  have hle : (n : ℝ) * κ ^ (n - 1) * (1 - κ) ≤ 1 :=
    le_trans (le_add_of_nonneg_left (pow_nonneg h0.le n)) hb
  rwa [le_div_iff₀ hκ1]

end Work.EQ
