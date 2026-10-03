import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FITop4.Red5

/-- The number of divisors of a squarefree natural number `n` is `2` raised to the
number of distinct prime factors of `n`. -/
theorem sqfree_divisors_card (n : ℕ) (h : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors h.ne_zero]
  rw [show n.primeFactors.prod (fun p => n.factorization p + 1)
        = n.primeFactors.prod (fun _ => 2) from
    Finset.prod_congr rfl (fun p hp => by
      rw [Nat.factorization_eq_one_of_squarefree h
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)])]
  exact Finset.prod_const 2

end Work.FITop4.Red5
