/-
# ZeroFreeTables/Rep9/primeFactorSum_le_sqrt_log_proof

For `j ≤ 3` and every `q ≥ 1`,

  `∑_{p | q} (log p)^j / p ≤ D · (1 + √(log q))`.

The input `P9.primeFactors_logPow_div_le` gives the bound `≤ C (log log q)^{j+1}` for `q ≥ 3`;
the elementary inequality `(log y)^{j+1} ≤ 4096 √y` (from `log y ≤ 8 y^{1/8}` and `y ≥ 1`)
converts it into `≤ 4096 C √(log q)`.  The cases `q = 1, 2` are bounded directly.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le

open scoped BigOperators

namespace Work.ZeroFreeTables.Rep9

/-- `(log y)^{j+1} ≤ 4096 √y` for `y ≥ 1`, `j ≤ 3`. -/
private lemma log_pow_le_sqrt (j : ℕ) (hj : j ≤ 3) {y : ℝ} (hy : 1 ≤ y) :
    (Real.log y) ^ (j + 1) ≤ 4096 * Real.sqrt y := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hb : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : Real.log y ≤ 8 * y ^ ((1 : ℝ) / 8) := by
    have h := Real.log_le_rpow_div (le_of_lt hypos) (show (0 : ℝ) < (1 : ℝ) / 8 by norm_num)
    calc Real.log y ≤ y ^ ((1 : ℝ) / 8) / ((1 : ℝ) / 8) := h
      _ = 8 * y ^ ((1 : ℝ) / 8) := by norm_num; ring
  have h2 : (Real.log y) ^ (j + 1) ≤ (8 * y ^ ((1 : ℝ) / 8)) ^ (j + 1) :=
    pow_le_pow_left₀ hb h1 (j + 1)
  have h3 : (8 * y ^ ((1 : ℝ) / 8)) ^ (j + 1) = 8 ^ (j + 1) * (y ^ ((1 : ℝ) / 8)) ^ (j + 1) := by
    rw [mul_pow]
  have h4 : (y ^ ((1 : ℝ) / 8)) ^ (j + 1) = y ^ (((j : ℝ) + 1) / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hypos)]
    congr 1
    push_cast; ring
  have hjR : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  have h5 : y ^ (((j : ℝ) + 1) / 8) ≤ y ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hy (by push_cast; nlinarith [hjR])
  have h6 : y ^ ((1 : ℝ) / 2) = Real.sqrt y := by rw [Real.sqrt_eq_rpow]
  have h7 : (8 : ℝ) ^ (j + 1) ≤ 8 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
  calc (Real.log y) ^ (j + 1) ≤ (8 * y ^ ((1 : ℝ) / 8)) ^ (j + 1) := h2
    _ = 8 ^ (j + 1) * y ^ (((j : ℝ) + 1) / 8) := by rw [h3, h4]
    _ ≤ 8 ^ 4 * y ^ ((1 : ℝ) / 2) :=
        mul_le_mul h7 h5 (Real.rpow_nonneg (le_of_lt hypos) _) (by norm_num)
    _ = 4096 * Real.sqrt y := by rw [h6]; norm_num

theorem primeFactorSum_le_sqrt_log_proof (j : ℕ) (hj : j ≤ 3) :
    ∃ D : ℝ, 0 < D ∧ ∀ q : ℕ, 1 ≤ q →
      ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
        ≤ D * (1 + Real.sqrt (Real.log (q : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le j hj
  refine ⟨C * 4096 + 1, by positivity, ?_⟩
  intro q hq1
  rcases lt_or_ge q 3 with hq | hq
  · interval_cases q
    · simp [Nat.primeFactors_one]
      nlinarith [hCpos]
    · have hpf : (2 : ℕ).primeFactors = {2} := Nat.Prime.primeFactors (by norm_num)
      rw [hpf, Finset.sum_singleton]
      have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog2le1 : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      have hpj : (Real.log 2) ^ j ≤ 1 := pow_le_one₀ hlog2nn hlog2le1
      have hhalf : (Real.log 2) ^ j / 2 ≤ 1 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith
      have hD : (1 : ℝ) ≤ C * 4096 + 1 := by nlinarith [hCpos]
      have hsqrt : 0 ≤ Real.sqrt (Real.log 2) := Real.sqrt_nonneg _
      nlinarith [hhalf, hD, hsqrt]
  · have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    have hx1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
      have h3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
        exact le_of_lt Real.exp_one_lt_three
      exact le_trans h3 (Real.log_le_log (by norm_num) hq3)
    have hbound := hC q hq
    have hkey : (Real.log (Real.log (q : ℝ))) ^ (j + 1) ≤ 4096 * Real.sqrt (Real.log (q : ℝ)) :=
      log_pow_le_sqrt j hj hx1
    have hsqrt_nn : 0 ≤ Real.sqrt (Real.log (q : ℝ)) := Real.sqrt_nonneg _
    have hCnn : 0 ≤ C := hCpos.le
    calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
        ≤ C * (Real.log (Real.log (q : ℝ))) ^ (j + 1) := hbound
      _ ≤ C * (4096 * Real.sqrt (Real.log (q : ℝ))) := mul_le_mul_of_nonneg_left hkey hCnn
      _ ≤ (C * 4096 + 1) * (1 + Real.sqrt (Real.log (q : ℝ))) := by nlinarith [hCnn, hsqrt_nn]

end Work.ZeroFreeTables.Rep9
