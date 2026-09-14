import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.SpecialFunctions

/-- Quantitative form of `e < 3`: for `1 ≤ n`, `(1 + n⁻¹)^n ≤ 3`, which unwinds to
`(n + 1) ^ n ≤ 3 * n ^ n` over the reals. -/
theorem add_one_pow_le_three_mul_pow (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ n ≤ 3 * (n : ℝ) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact ne_of_gt this
  have h := Real.one_add_inv_pow_le_exp (n := n)
  have h3 : (1 + (n : ℝ)⁻¹) ^ n ≤ 3 := h.trans (le_of_lt Real.exp_one_lt_three)
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) ^ n := pow_nonneg (by positivity) n
  have hmul : (n : ℝ) ^ n * (1 + (n : ℝ)⁻¹) ^ n ≤ (n : ℝ) ^ n * 3 :=
    mul_le_mul_of_nonneg_left h3 hnnonneg
  rw [← mul_pow] at hmul
  have hsimp : (n : ℝ) * (1 + (n : ℝ)⁻¹) = (n : ℝ) + 1 := by
    field_simp
  rw [hsimp] at hmul
  rw [mul_comm ((n : ℝ) ^ n) 3] at hmul
  exact hmul

/-- Natural-number form of `add_one_pow_le_three_mul_pow`. -/
theorem nat_add_one_pow_le_three_mul_pow (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) ^ n ≤ 3 * n ^ n := by
  exact_mod_cast add_one_pow_le_three_mul_pow n hn

/-- For `1 ≤ n`, `n ^ (n - 1) ≤ 3 ^ (n - 1) * (n - 1)!`. This is the precise form of
"the factorial dominates the power": iterating it gives `(n / 3) ^ (n - 1) ≤ (n - 1)!`. -/
theorem pow_pred_le_three_pow_mul_factorial (n : ℕ) (hn : 1 ≤ n) :
    n ^ (n - 1) ≤ 3 ^ (n - 1) * (n - 1).factorial := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [Nat.add_sub_cancel]
    have hsub : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hm_pow : m ^ m = m ^ (m - 1) * m := by
      calc m ^ m = m ^ (m - 1 + 1) := by rw [hsub]
        _ = m ^ (m - 1) * m := pow_succ m (m - 1)
    have hm_fact : m.factorial = m * (m - 1).factorial := by
      calc m.factorial = ((m - 1) + 1).factorial := by rw [hsub]
        _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ (m - 1)
        _ = m * (m - 1).factorial := by rw [hsub]
    have h3pow : 3 * 3 ^ (m - 1) = 3 ^ m := by
      rw [← pow_succ' 3 (m - 1), hsub]
    have h3 : 3 * m * (3 ^ (m - 1) * (m - 1).factorial) = 3 ^ m * m.factorial := by
      rw [hm_fact, ← h3pow]
      ring
    calc (m + 1) ^ m ≤ 3 * m ^ m := nat_add_one_pow_le_three_mul_pow m hm
      _ = 3 * m * m ^ (m - 1) := by rw [hm_pow]; ring
      _ ≤ 3 * m * (3 ^ (m - 1) * (m - 1).factorial) := Nat.mul_le_mul_left (3 * m) ih
      _ = 3 ^ m * m.factorial := h3

theorem pow_two_mul_pred_le_factorial (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℝ)) ^ (n - 1) ≤ 6 ^ (n - 1) * (((n - 1).factorial : ℕ) : ℝ) := by
  have h := pow_pred_le_three_pow_mul_factorial n hn
  have h2 : (2 * n) ^ (n - 1) ≤ 6 ^ (n - 1) * (n - 1).factorial := by
    calc (2 * n) ^ (n - 1) = 2 ^ (n - 1) * n ^ (n - 1) := by rw [mul_pow]
      _ ≤ 2 ^ (n - 1) * (3 ^ (n - 1) * (n - 1).factorial) := Nat.mul_le_mul_left _ h
      _ = 6 ^ (n - 1) * (n - 1).factorial := by
            rw [← mul_assoc, ← mul_pow]; norm_num
  have h3 : ((2 * n : ℕ) : ℝ) ^ (n - 1) ≤ ((6 ^ (n - 1) * (n - 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast h2
  simpa using h3

end Commons.Analysis.SpecialFunctions