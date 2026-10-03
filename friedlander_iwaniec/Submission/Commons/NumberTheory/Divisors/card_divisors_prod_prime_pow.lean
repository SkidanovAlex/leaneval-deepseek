import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Submission.Commons.Data.Nat.factorization_prod_prime_pow_apply

open scoped BigOperators

namespace Commons.NumberTheory.Divisors

theorem card_divisors_prod_prime_pow (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) (he : ∀ p ∈ S, 1 ≤ e p) :
    (Nat.divisors (∏ p ∈ S, p ^ e p)).card = ∏ p ∈ S, (e p + 1) := by
  classical
  have hN0 : (∏ p ∈ S, p ^ e p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)
  have hpf : (∏ p ∈ S, p ^ e p).primeFactors = S := by
    ext q
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hqprime, hqdvd, _⟩
      obtain ⟨a, ha, hqa⟩ :=
        (Prime.dvd_finsetProd_iff hqprime.prime (fun p => p ^ e p)).mp hqdvd
      have hadvd : q ∣ a := hqprime.dvd_of_dvd_pow hqa
      have haprime : a.Prime := hS a ha
      have hqea : q = a := (Nat.prime_dvd_prime_iff_eq hqprime haprime).mp hadvd
      rw [hqea]; exact ha
    · intro hq
      refine ⟨hS q hq, ?_, hN0⟩
      have heq : e q ≠ 0 := by have := he q hq; omega
      exact dvd_trans (dvd_pow_self q heq) (Finset.dvd_prod_of_mem (fun p => p ^ e p) hq)
  rw [Nat.card_divisors hN0, hpf]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Commons.Data.Nat.factorization_prod_prime_pow_apply S e hS p, if_pos hp]

end Commons.NumberTheory.Divisors