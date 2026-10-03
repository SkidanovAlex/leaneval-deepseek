import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt

namespace Commons.Analysis.Real

theorem X2Y4_prime_pow_sqrt_bound {p e : ℕ} (hp : 2 ≤ p) (he : 2 ≤ e) :
    (p : ℝ) ^ (e / 2 + (e - (e + 3) / 4)) + 2 * (p : ℝ) ^ (e + (e + 3) / 4 - 1)
      ≤ 3 * (p : ℝ) ^ (e - 1) * Real.sqrt ((p : ℝ) ^ e) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := le_trans zero_le_one hp1
  have hpR : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  set M : ℕ := (e - 1) + e / 2 with hM
  have hn1 : e / 2 + (e - (e + 3) / 4) ≤ M := by rw [hM]; omega
  have hn2 : e + (e + 3) / 4 - 1 ≤ M := by rw [hM]; omega
  have hle1 : (p : ℝ) ^ (e / 2 + (e - (e + 3) / 4)) ≤ (p : ℝ) ^ M :=
    pow_le_pow_right₀ hp1 hn1
  have hle2 : (p : ℝ) ^ (e + (e + 3) / 4 - 1) ≤ (p : ℝ) ^ M :=
    pow_le_pow_right₀ hp1 hn2
  have hsqrt : (p : ℝ) ^ (e / 2) ≤ Real.sqrt ((p : ℝ) ^ e) := by
    rw [Real.le_sqrt' (pow_pos hpR _)]
    rw [← pow_mul]
    exact pow_le_pow_right₀ hp1 (by omega : e / 2 * 2 ≤ e)
  have hMexp : (p : ℝ) ^ M = (p : ℝ) ^ (e - 1) * (p : ℝ) ^ (e / 2) := by
    rw [hM, pow_add]
  have hRHS : 3 * (p : ℝ) ^ (e - 1) * (p : ℝ) ^ (e / 2)
      ≤ 3 * (p : ℝ) ^ (e - 1) * Real.sqrt ((p : ℝ) ^ e) := by
    have hpe : (0 : ℝ) ≤ (p : ℝ) ^ (e - 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hpe]
  calc
    (p : ℝ) ^ (e / 2 + (e - (e + 3) / 4))
        + 2 * (p : ℝ) ^ (e + (e + 3) / 4 - 1)
        ≤ (p : ℝ) ^ M + 2 * (p : ℝ) ^ M := by
          have h : 2 * (p : ℝ) ^ (e + (e + 3) / 4 - 1) ≤ 2 * (p : ℝ) ^ M :=
            mul_le_mul_of_nonneg_left hle2 (by norm_num)
          linarith
    _ = 3 * (p : ℝ) ^ M := by ring
    _ = 3 * (p : ℝ) ^ (e - 1) * (p : ℝ) ^ (e / 2) := by rw [hMexp]; ring
    _ ≤ 3 * (p : ℝ) ^ (e - 1) * Real.sqrt ((p : ℝ) ^ e) := hRHS

end Commons.Analysis.Real