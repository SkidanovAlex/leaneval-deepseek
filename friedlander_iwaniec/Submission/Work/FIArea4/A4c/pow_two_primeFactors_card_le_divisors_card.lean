import Mathlib

namespace Work.FIArea4.A4c

/-- The number of divisors of a nonzero natural number is at least `2` to the number of its
distinct prime factors: each prime factor `p` contributes a factor `m.factorization p + 1 ≥ 2`
to `#m.divisors = ∏ p ∈ m.primeFactors, (m.factorization p + 1)`. -/
theorem pow_two_primeFactors_card_le_divisors_card (m : ℕ) (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors hm]
  refine Finset.pow_card_le_prod _ _ _ ?_
  intro p hp
  have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h1 : 1 ≤ m.factorization p := (hpp.dvd_iff_one_le_factorization hm).mp hpdvd
  omega

end Work.FIArea4.A4c
