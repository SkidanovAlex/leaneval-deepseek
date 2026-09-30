import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The number of distinct prime divisors of `k ≥ 1` is at most `log₂ k`.

Proof: the product of the distinct prime factors of `k` divides `k`
(`Nat.prod_primeFactors_dvd`), each factor is `≥ 2`, so `2 ^ ω ≤ k` with
`ω = k.primeFactors.card`; applying the monotone `Real.logb 2` and
`Real.logb_pow`/`Real.logb_self_eq_one` gives the claim. -/
theorem primeFactors_card_le_logb (k : ℕ) (hk : 0 < k) :
    (k.primeFactors.card : ℝ) ≤ Real.logb 2 (k : ℝ) := by
  -- `2 ^ ω ≤ ∏ p ∈ k.primeFactors, p ≤ k` in ℕ
  have h2card : 2 ^ k.primeFactors.card ≤ k := by
    have hprod : ∏ p ∈ k.primeFactors, (2 : ℕ) ≤ ∏ p ∈ k.primeFactors, p := by
      apply Finset.prod_le_prod
      intro p hp
      exact (Nat.mem_primeFactors.mp hp).1.two_le
    rw [Finset.prod_const] at hprod
    exact le_trans hprod (Nat.le_of_dvd hk (Nat.prod_primeFactors_dvd k))
  have hcast : (2 : ℝ) ^ k.primeFactors.card ≤ (k : ℝ) := by exact_mod_cast h2card
  have hlogb : Real.logb 2 ((2 : ℝ) ^ k.primeFactors.card) = (k.primeFactors.card : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hmono := Real.logb_le_logb_of_le (show (1 : ℝ) < 2 by norm_num)
    (by positivity : (0 : ℝ) < 2 ^ k.primeFactors.card) hcast
  rwa [hlogb] at hmono

end Work.BW
