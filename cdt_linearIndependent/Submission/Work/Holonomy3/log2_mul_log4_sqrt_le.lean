import Mathlib

namespace Work.Holonomy3

/-- Elementary two-sided growth bound: for every natural `n`, the base-2 logarithm of `n`
multiplied by `log 4 · √n` is at most `4 √(n+1) (1 + log (n+1))`. -/
theorem log2_mul_log4_sqrt_le (n : ℕ) :
    (Nat.log 2 n : ℝ) * (Real.log 4 * Real.sqrt n)
      ≤ 4 * Real.sqrt (n + 1) * (1 + Real.log (n + 1)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    norm_num [Real.log_one]
  · have h1 : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
      have := Real.natLog_le_logb n 2
      simpa [Real.logb] using this
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      have h : (4:ℝ) = 2^2 := by norm_num
      rw [h, Real.log_pow]; norm_num
    have hfac_nonneg : 0 ≤ Real.log 4 * Real.sqrt n := by
      rw [hlog4]; exact mul_nonneg (by positivity) (Real.sqrt_nonneg n)
    have step1 : (Nat.log 2 n : ℝ) * (Real.log 4 * Real.sqrt n)
        ≤ (Real.log n / Real.log 2) * (Real.log 4 * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right h1 hfac_nonneg
    have step2 : (Real.log n / Real.log 2) * (Real.log 4 * Real.sqrt n)
        = 2 * Real.log n * Real.sqrt n := by
      rw [hlog4]; field_simp
    have hlogn_nonneg : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hlogle : Real.log n ≤ Real.log (n + 1) := by
      apply Real.log_le_log (by exact_mod_cast hn)
      linarith
    have hlog1_nonneg : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
    have hsqrtle : Real.sqrt n ≤ Real.sqrt (n + 1) := by
      apply Real.sqrt_le_sqrt; linarith
    have hsqrt1_pos : 0 < Real.sqrt (n + 1) := by
      apply Real.sqrt_pos.2; linarith
    have step3a : 2 * Real.log n * Real.sqrt n ≤ 2 * Real.log (n + 1) * Real.sqrt (n + 1) :=
      mul_le_mul (by linarith) hsqrtle (Real.sqrt_nonneg n) (by linarith)
    have step3b : 2 * Real.log (n + 1) * Real.sqrt (n + 1)
        ≤ 4 * Real.sqrt (n + 1) * (1 + Real.log (n + 1)) := by
      have h2 : 2 * Real.log (n + 1) ≤ 4 * (1 + Real.log (n + 1)) := by linarith
      calc (2 * Real.log (n + 1)) * Real.sqrt (n + 1)
          ≤ (4 * (1 + Real.log (n + 1))) * Real.sqrt (n + 1) :=
            mul_le_mul_of_nonneg_right h2 hsqrt1_pos.le
        _ = 4 * Real.sqrt (n + 1) * (1 + Real.log (n + 1)) := by ring
    calc (Nat.log 2 n : ℝ) * (Real.log 4 * Real.sqrt n)
        ≤ (Real.log n / Real.log 2) * (Real.log 4 * Real.sqrt n) := step1
      _ = 2 * Real.log n * Real.sqrt n := step2
      _ ≤ 2 * Real.log (n + 1) * Real.sqrt (n + 1) := step3a
      _ ≤ 4 * Real.sqrt (n + 1) * (1 + Real.log (n + 1)) := step3b

end Work.Holonomy3
