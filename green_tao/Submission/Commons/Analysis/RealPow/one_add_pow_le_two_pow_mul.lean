import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.RealPow

/-- Sharper Bernoulli-type upper bound: for `0 ≤ x ≤ 1` and `q : ℕ`,
`(1 + x)^q ≤ 1 + (2^q - 1) * x`. -/
theorem one_add_pow_le_one_add_mul_sub_one (q : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ q ≤ 1 + ((2:ℝ)^q - 1) * x := by
  induction q with
  | zero => simp
  | succ n ih =>
    have h1x : (0:ℝ) ≤ 1 + x := by linarith
    have h2n : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    have ha : (0:ℝ) ≤ (2:ℝ)^n - 1 := by linarith
    have hsq : x ^ 2 ≤ x := by nlinarith
    have hmul : ((2:ℝ)^n - 1) * x ^ 2 ≤ ((2:ℝ)^n - 1) * x :=
      mul_le_mul_of_nonneg_left hsq ha
    have hpow : (2:ℝ) ^ (n + 1) = 2 * (2:ℝ) ^ n := by rw [pow_succ]; ring
    calc (1 + x) ^ (n + 1)
        = (1 + x) ^ n * (1 + x) := by rw [pow_succ]
      _ ≤ (1 + ((2:ℝ)^n - 1) * x) * (1 + x) :=
            mul_le_mul_of_nonneg_right ih h1x
      _ ≤ 1 + ((2:ℝ)^(n+1) - 1) * x := by
            rw [hpow]; nlinarith [hmul]

theorem one_add_pow_le_two_pow_mul (q : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ q ≤ 1 + (2:ℝ)^q * x := by
  have h := one_add_pow_le_one_add_mul_sub_one q x hx0 hx1
  have h2 : ((2:ℝ)^q - 1) * x ≤ (2:ℝ)^q * x := by
    apply mul_le_mul_of_nonneg_right _ hx0
    linarith
  linarith

end Commons.Analysis.RealPow