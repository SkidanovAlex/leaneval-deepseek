import Mathlib

namespace Work.HP

/-- If a product of powers of `2` is at most `M` then the sum of the exponents is at most
`⌈logb 2 M⌉`. -/
theorem sum_le_ceil_logb_of_prod {r : ℕ} {k : Fin r → ℕ} {M : ℝ} (hM : 1 ≤ M)
    (h : ∏ j : Fin r, (2 : ℝ) ^ k j ≤ M) : (∑ j : Fin r, k j) ≤ ⌈Real.logb 2 M⌉₊ := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  -- convert the product of powers into a single power
  have hpow : (2 : ℝ) ^ (∑ j : Fin r, k j) = ∏ j : Fin r, (2 : ℝ) ^ k j := by
    rw [Finset.prod_pow_eq_pow_sum]
  have h2n : (2 : ℝ) ^ (∑ j : Fin r, k j) ≤ M := by rw [hpow]; exact h
  -- take `logb 2` of both sides
  have hle : ((∑ j : Fin r, k j : ℕ) : ℝ) ≤ Real.logb 2 M := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hM0]
    rwa [Real.rpow_natCast]
  have hlog : Real.logb 2 M ≤ (⌈Real.logb 2 M⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast le_trans hle hlog

end Work.HP
