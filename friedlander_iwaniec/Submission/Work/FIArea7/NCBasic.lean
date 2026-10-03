/-
# `Submission.Work.FIArea7.NCBasic`

Elementary real-variable estimates used by `Work.FIArea7.numeric_core_proof` (the proof of
`Work.FIArea7.NumericCore`) and by the four term bounds it is assembled from.

Nothing here mentions the *FI* analytic apparatus: these are the standard facts that a power of a
logarithm is eventually dominated by any positive power of the argument, that `log (N+2) ≤ 2 log N`
for `N ≥ 2`, and the elementary monotonicity/`rpow` manipulations.
-/
import Mathlib
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

set_option autoImplicit false

namespace Work.FIArea7

open scoped BigOperators

/-! ## 1. Elementary logarithmic comparisons -/

/-- `1 ≤ log N` for `N ≥ 3`. -/
lemma one_le_log_of_three_le {N : ℝ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have h3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  exact le_trans h3.le (Real.log_le_log (by norm_num) hN)

/-- `log (N + 2) ≤ 2 log N` for `N ≥ 2`. -/
lemma log_add_two_le_two_mul_log {N : ℝ} (hN : 2 ≤ N) :
    Real.log (N + 2) ≤ 2 * Real.log N := by
  have hN0 : 0 < N := by linarith
  have h1 : Real.log (N + 2) ≤ Real.log (2 * N) := Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (by linarith)
  have h3 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  linarith

/-- The same comparison with the sum written the other way round. -/
lemma log_two_add_le_two_mul_log {N : ℝ} (hN : 2 ≤ N) :
    Real.log (2 + N) ≤ 2 * Real.log N := by
  rw [add_comm]
  exact log_add_two_le_two_mul_log hN

/-! ## 2. A power of a logarithm is eventually smaller than any power of `N` -/

/-- For every `m : ℕ` and `ε > 0` there is a threshold `N₀ ≥ 3` beyond which both
`(log N)^m ≤ N^ε` and `(log (N+2))^m ≤ N^ε`. -/
lemma exists_log_pow_le_rpow (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (Real.log N) ^ m ≤ N ^ ε ∧ (Real.log (N + 2)) ^ m ≤ N ^ ε := by
  obtain ⟨X₁, hX₁, h₁⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := (1 : ℝ))
      zero_le_one (n := m) hε
  obtain ⟨X₂, hX₂, h₂⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := (2 : ℝ) ^ m)
      (by positivity) (n := m) hε
  refine ⟨max (max X₁ X₂) 3, le_max_right _ _, ?_⟩
  intro N hN
  have hNX₁ : X₁ ≤ N := le_trans (le_trans (le_max_left X₁ X₂) (le_max_left _ 3)) hN
  have hNX₂ : X₂ ≤ N := le_trans (le_trans (le_max_right X₁ X₂) (le_max_left _ 3)) hN
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right (max X₁ X₂) 3) hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog2 : Real.log (N + 2) ≤ 2 * Real.log N := log_add_two_le_two_mul_log (by linarith)
  constructor
  · simpa using h₁ N hNX₁
  · calc (Real.log (N + 2)) ^ m ≤ (2 * Real.log N) ^ m := by
          apply pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog2
      _ = (2 : ℝ) ^ m * (Real.log N) ^ m := by rw [mul_pow]
      _ ≤ N ^ ε := by simpa using h₂ N hNX₂

/-! ## 3. `rpow` monotonicity helpers -/

/-- Comparison of `rpow`s with a base `≥ 1`. -/
lemma rpow_le_rpow_of_le {N a b : ℝ} (hN : 1 ≤ N) (hab : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN hab

/-- If `X^8 ≤ N^δ` with `X ≥ 0`, `N > 0`, then `X ≤ N^{δ/8}`. -/
lemma le_rpow_div_eight_of_pow_eight_le {X N δ : ℝ} (hX : 0 ≤ X) (hN : 0 < N)
    (h : X ^ 8 ≤ N ^ δ) : X ≤ N ^ (δ / 8) := by
  have h8 : (X ^ 8) ^ ((1 : ℝ) / 8) ≤ (N ^ δ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  have e1 : (X ^ 8) ^ ((1 : ℝ) / 8) = X := by
    rw [show X ^ 8 = X ^ ((8 : ℝ)) from (Real.rpow_natCast X 8).symm, ← Real.rpow_mul hX,
      show (8 : ℝ) * ((1 : ℝ) / 8) = 1 by norm_num, Real.rpow_one]
  have e2 : (N ^ δ) ^ ((1 : ℝ) / 8) = N ^ (δ / 8) := by
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [e1, e2] at h8
  exact h8

/-- From `X ≤ N^a` (`X ≥ 0`, `N > 0`) deduce `X^n ≤ N^{a*n}`. -/
lemma pow_le_rpow_of_le_rpow {X N a : ℝ} (hX : 0 ≤ X) (hN : 0 < N) (h : X ≤ N ^ a)
    (n : ℕ) : X ^ n ≤ N ^ (a * n) := by
  have h1 : X ^ n ≤ (N ^ a) ^ n := pow_le_pow_left₀ hX h n
  have h2 : (N ^ a) ^ n = N ^ (a * n) := by
    rw [← Real.rpow_natCast (N ^ a) n, ← Real.rpow_mul hN.le]
  rwa [h2] at h1

/-- From `X ≤ N^a` (`X > 0`, `N > 0`) deduce `N^{-a} ≤ X⁻¹`. -/
lemma inv_le_inv_of_le_rpow {X N a : ℝ} (hX : 0 < X) (hN : 0 < N) (h : X ≤ N ^ a) :
    N ^ (-a) ≤ X⁻¹ := by
  have h1 : (N ^ a)⁻¹ ≤ X⁻¹ := inv_anti₀ hX h
  have h2 : (N ^ a)⁻¹ = N ^ (-a) := by
    rw [← Real.rpow_neg hN.le]
  rwa [h2] at h1

/-! ## 4. A couple of numerical constants -/

lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  rw [Real.sqrt_le_iff]
  norm_num

lemma two_rpow_three_halves_le_three : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 3 := by
  have h3 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [show ((3 : ℝ) / 2) = (3 : ℝ) * (1 / 2) by norm_num, Real.rpow_mul (by norm_num), h3,
    ← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  norm_num

end Work.FIArea7
