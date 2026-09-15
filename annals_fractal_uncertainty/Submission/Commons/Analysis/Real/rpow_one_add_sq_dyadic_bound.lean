import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- Dyadic large-`t` bound for `(1 + t²)^((1-b)/2)`.  For `1 ≤ k`, `b ≤ 3` and
`2^(k-1) ≤ t ≤ 2^(k+1)`, we have
`(1 + t²)^((1-b)/2) ≤ 4 · 2^(k(1-b))`. -/
theorem rpow_one_add_sq_dyadic_bound (k b : ℕ) (t : ℝ) (hk : 1 ≤ k) (hb : b ≤ 3)
    (hlo : (2 : ℝ) ^ (k - 1) ≤ t) (hhi : t ≤ (2 : ℝ) ^ (k + 1)) :
    (1 + t ^ 2) ^ ((1 - (b : ℝ)) / 2) ≤ 4 * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ))) := by
  have ht1 : (1 : ℝ) ≤ t :=
    le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hlo
  have ht0 : 0 ≤ t := le_trans zero_le_one ht1
  have htsq1 : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht1
  have htsq_pos : 0 < t ^ 2 := lt_of_lt_of_le zero_lt_one htsq1
  -- squared upper bound for `t`
  have hS : t ^ 2 ≤ (2 : ℝ) ^ (2 * k + 2) := by
    have h1 : t ^ 2 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := pow_le_pow_left₀ ht0 hhi 2
    have h2 : ((2 : ℝ) ^ (k + 1)) ^ 2 = (2 : ℝ) ^ ((k + 1) * 2) := by rw [← pow_mul]
    have h3 : (k + 1) * 2 = 2 * k + 2 := by ring
    rw [h2, h3] at h1
    exact h1
  -- rewrite the right-hand side as a single power of two
  have hRHS : 4 * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ))) =
      (2 : ℝ) ^ (2 + (k : ℝ) * (1 - (b : ℝ))) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
    rw [h4, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2) ((2 : ℕ) : ℝ)
        ((k : ℝ) * (1 - (b : ℝ)))]
    congr 1
  rw [hRHS]
  by_cases hb1 : b ≤ 1
  · -- exponent `(1-b)/2 ≥ 0`
    have hbR : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
    have hb0R : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have hE0 : 0 ≤ (1 - (b : ℝ)) / 2 := div_nonneg (by linarith) (by norm_num)
    have hle1 : 1 + t ^ 2 ≤ (2 : ℝ) ^ (2 * k + 3) := by
      have h1 : 1 + t ^ 2 ≤ 2 * t ^ 2 := by nlinarith [htsq1]
      have h2 : 2 * t ^ 2 ≤ 2 * (2 : ℝ) ^ (2 * k + 2) :=
        mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ) ≤ 2)
      have h3 : 2 * (2 : ℝ) ^ (2 * k + 2) = (2 : ℝ) ^ (2 * k + 3) := by
        have heq : (2 : ℝ) ^ (2 * k + 3) = 2 * (2 : ℝ) ^ (2 * k + 2) := by
          rw [show 2 * k + 3 = 1 + (2 * k + 2) by omega, pow_add, pow_one]
        rw [heq]
      linarith
    have step1 : (1 + t ^ 2) ^ ((1 - (b : ℝ)) / 2) ≤
        ((2 : ℝ) ^ (2 * k + 3)) ^ ((1 - (b : ℝ)) / 2) :=
      Real.rpow_le_rpow (by positivity) hle1 hE0
    have step2 : ((2 : ℝ) ^ (2 * k + 3)) ^ ((1 - (b : ℝ)) / 2) =
        (2 : ℝ) ^ (((2 * k + 3 : ℕ) : ℝ) * ((1 - (b : ℝ)) / 2)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (2 * k + 3),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hexp : (((2 * k + 3 : ℕ) : ℝ)) * ((1 - (b : ℝ)) / 2) ≤
        2 + (k : ℝ) * (1 - (b : ℝ)) := by
      push_cast
      nlinarith [hb0R]
    have step3 : (2 : ℝ) ^ (((2 * k + 3 : ℕ) : ℝ) * ((1 - (b : ℝ)) / 2)) ≤
        (2 : ℝ) ^ (2 + (k : ℝ) * (1 - (b : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    calc (1 + t ^ 2) ^ ((1 - (b : ℝ)) / 2)
        ≤ ((2 : ℝ) ^ (2 * k + 3)) ^ ((1 - (b : ℝ)) / 2) := step1
      _ = (2 : ℝ) ^ (((2 * k + 3 : ℕ) : ℝ) * ((1 - (b : ℝ)) / 2)) := step2
      _ ≤ (2 : ℝ) ^ (2 + (k : ℝ) * (1 - (b : ℝ))) := step3
  · -- exponent `(1-b)/2 ≤ 0`
    have hb2 : 2 ≤ b := by omega
    have hbR2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
    have hbR3 : (b : ℝ) ≤ 3 := by exact_mod_cast hb
    have hE0 : 1 - (b : ℝ) ≤ 0 := by linarith
    have hEhalf : (1 - (b : ℝ)) / 2 ≤ 0 := by linarith
    have step1 : (1 + t ^ 2) ^ ((1 - (b : ℝ)) / 2) ≤ (t ^ 2) ^ ((1 - (b : ℝ)) / 2) :=
      Real.rpow_le_rpow_of_nonpos htsq_pos (by linarith) hEhalf
    have step2 : (t ^ 2) ^ ((1 - (b : ℝ)) / 2) = t ^ (1 - (b : ℝ)) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0]
      congr 1
      ring
    have step3 : t ^ (1 - (b : ℝ)) ≤ ((2 : ℝ) ^ (k - 1)) ^ (1 - (b : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlo hE0
    have step4 : ((2 : ℝ) ^ (k - 1)) ^ (1 - (b : ℝ)) =
        (2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) * (1 - (b : ℝ))) := by
      rw [← Real.rpow_natCast (2 : ℝ) (k - 1),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hexp : (((k - 1 : ℕ) : ℝ)) * (1 - (b : ℝ)) ≤
        2 + (k : ℝ) * (1 - (b : ℝ)) := by
      have hkc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk, Nat.cast_one]
      rw [hkc]
      nlinarith [hbR3]
    have step5 : (2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) * (1 - (b : ℝ))) ≤
        (2 : ℝ) ^ (2 + (k : ℝ) * (1 - (b : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    calc (1 + t ^ 2) ^ ((1 - (b : ℝ)) / 2)
        ≤ (t ^ 2) ^ ((1 - (b : ℝ)) / 2) := step1
      _ = t ^ (1 - (b : ℝ)) := step2
      _ ≤ ((2 : ℝ) ^ (k - 1)) ^ (1 - (b : ℝ)) := step3
      _ = (2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) * (1 - (b : ℝ))) := step4
      _ ≤ (2 : ℝ) ^ (2 + (k : ℝ) * (1 - (b : ℝ))) := step5

end Commons.Analysis.Real