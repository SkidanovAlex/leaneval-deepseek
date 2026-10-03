import Mathlib

namespace Work.FIArea6V

/-- The number-of-divisors function `τ(n) = #n.divisors` is bounded by
`2 ^ Ω(n)`, where `Ω(n) = n.factorization.sum (fun _ e => e)` is the number of
prime factors of `n` counted with multiplicity.

This is the elementary bound `∏ (e_p + 1) ≤ ∏ 2 ^ e_p`
(using `e + 1 ≤ 2 ^ e`), the right-hand product being `2 ^ ∑ e_p`. -/
theorem tau_le_two_pow_cardFactors (n : ℕ) :
    n.divisors.card ≤ 2 ^ n.factorization.sum (fun _ e => e) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [Nat.card_divisors hn]
    calc ∏ p ∈ n.primeFactors, (n.factorization p + 1)
        ≤ ∏ p ∈ n.primeFactors, 2 ^ n.factorization p :=
          Finset.prod_le_prod' fun p _ => Nat.succ_le_of_lt Nat.lt_two_pow_self
      _ = 2 ^ ∑ p ∈ n.primeFactors, n.factorization p :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ = 2 ^ n.factorization.sum (fun _ e => e) := by
          rw [Finsupp.sum, Nat.support_factorization]

end Work.FIArea6V
