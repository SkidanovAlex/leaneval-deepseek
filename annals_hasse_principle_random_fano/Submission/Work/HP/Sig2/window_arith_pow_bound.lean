import Mathlib

namespace Work.HP.Sig2

/-- Auxiliary arithmetic fact: for `0 < a` and `1 ≤ d`, raising `2` to the real power
`k * logb 2 (a * (d + 1))` is at most `(2 * a)^k * d^k`. -/
lemma pow_logb_le (a d : ℝ) (ha : 0 < a) (hd : 1 ≤ d) (k : ℕ) :
    (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 (a * (d + 1))) ≤ (2 * a) ^ k * d ^ k := by
  have hlog : (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 (a * (d + 1))) = (a * (d + 1)) ^ k := by
    rw [mul_comm (k : ℝ) (Real.logb 2 (a * (d + 1))),
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
        Real.rpow_natCast]
  rw [hlog]
  have hbase : a * (d + 1) ≤ 2 * a * d := by
    have h1 : d + 1 ≤ 2 * d := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt ha)]
  calc (a * (d + 1)) ^ k ≤ (2 * a * d) ^ k := pow_le_pow_left₀ (by positivity) hbase k
    _ = (2 * a) ^ k * d ^ k := by rw [mul_pow]

theorem window_arith_pow_bound (n r : ℕ) (hn : 2 ≤ n)
    (Kmink Δ : ℝ) (hKmink : 1 ≤ Kmink) (hΔ : 1 ≤ Δ) :
    (2 : ℝ) ^ (((n + 1) - 2 : ℕ) * Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1)))
      ≤ ((2 * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1)) * Δ ^ (n - 1) := by
  have hm : (n + 1) - 2 = n - 1 := by omega
  rw [hm]
  exact pow_logb_le ((2 : ℝ) ^ r * Kmink) Δ (by positivity) hΔ (n - 1)

end Work.HP.Sig2
