import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem two_pow_card_primeFactors_le_card_divisors {d : ℕ} (hd : 0 < d) :
    2 ^ (Nat.primeFactors d).card ≤ (Nat.divisors d).card := by
  have hd0 : d ≠ 0 := hd.ne'
  rw [Nat.card_divisors hd0]
  calc 2 ^ (Nat.primeFactors d).card
      = ∏ _p ∈ Nat.primeFactors d, (2 : ℕ) := (Finset.prod_const (2 : ℕ)).symm
    _ ≤ ∏ p ∈ Nat.primeFactors d, (d.factorization p + 1) := by
        refine Finset.prod_le_prod' fun p hp ↦ ?_
        have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
        have := hprime.factorization_pos_of_dvd hd0 hdvd
        omega

end Commons.NumberTheory.FriedlanderIwaniec