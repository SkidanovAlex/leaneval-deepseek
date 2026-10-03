import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube

namespace Work.FIArea7

/-- `(x ^ (1/8)) ^ 4 = x ^ (1/2)` for `x ≥ 0`: the two exponents multiply. -/
private lemma rpow_eighth_pow_four (x : ℝ) (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 8)) ^ 4 = x ^ ((1 : ℝ) / 2) := by
  rw [← Real.rpow_mul_natCast hx ((1 : ℝ) / 8) 4]
  norm_num

/-- `τ(c)^4 · √c ≪ c`, from the divisor bound `τ(c) ≤ C c^{1/8}` at `eps = 1/8`
(`Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow`, already imported by
`Submission.Work.FIArea7.S2Imports`). -/
theorem t2psi_S2_tauFour_sqrt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ cc : ℕ,
      (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt cc ≤ C * (cc : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ((1 : ℝ) / 8) (by norm_num)
  refine ⟨C₀ ^ 4, by positivity, ?_⟩
  intro cc
  rcases Nat.eq_zero_or_pos cc with h0 | hpos
  · subst h0
    simp
  have hccpos : (0 : ℝ) < (cc : ℝ) := by exact_mod_cast hpos
  have hccnn : (0 : ℝ) ≤ (cc : ℝ) := le_of_lt hccpos
  have hτnn : (0 : ℝ) ≤ ((cc.divisors.card : ℕ) : ℝ) := by positivity
  -- raise the divisor bound to the fourth power
  have h1 : (((cc.divisors.card : ℕ) : ℝ)) ^ 4 ≤ (C₀ * (cc : ℝ) ^ ((1 : ℝ) / 8)) ^ 4 :=
    pow_le_pow_left₀ hτnn (hC₀ cc) 4
  have h2 : (C₀ * (cc : ℝ) ^ ((1 : ℝ) / 8)) ^ 4 = C₀ ^ 4 * (cc : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [mul_pow, rpow_eighth_pow_four _ hccnn]
  have h4 : (((cc.divisors.card : ℕ) : ℝ)) ^ 4 ≤ C₀ ^ 4 * (cc : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← h2]; exact h1
  have h5 := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg (cc : ℝ))
  rw [Real.sqrt_eq_rpow] at h5
  rw [Real.sqrt_eq_rpow]
  have hsq : (cc : ℝ) ^ ((1 : ℝ) / 2) * (cc : ℝ) ^ ((1 : ℝ) / 2) = (cc : ℝ) := by
    rw [← Real.rpow_add hccpos]
    norm_num
  calc (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * (cc : ℝ) ^ ((1 : ℝ) / 2)
      ≤ (C₀ ^ 4 * (cc : ℝ) ^ ((1 : ℝ) / 2)) * (cc : ℝ) ^ ((1 : ℝ) / 2) := h5
    _ = C₀ ^ 4 * ((cc : ℝ) ^ ((1 : ℝ) / 2) * (cc : ℝ) ^ ((1 : ℝ) / 2)) := by ring
    _ = C₀ ^ 4 * (cc : ℝ) := by rw [hsq]

end Work.FIArea7
