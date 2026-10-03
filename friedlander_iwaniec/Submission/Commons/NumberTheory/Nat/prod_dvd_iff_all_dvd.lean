import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.PrimeFin

namespace Commons.NumberTheory.Nat

open scoped BigOperators

theorem prod_dvd_iff_all_dvd {q x : ℕ} {S : Finset ℕ} (hS : S ⊆ q.primeFactors) :
    (∏ p ∈ S, p) ∣ x ↔ ∀ p ∈ S, p ∣ x := by
  classical
  -- Every element of `S` is prime, since `S ⊆ q.primeFactors`.
  have hprime : ∀ p ∈ S, p.Prime := fun p hpS => Nat.prime_of_mem_primeFactors (hS hpS)
  -- Distinct primes are coprime, so the elements of `S` are pairwise coprime.
  have hpair : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro p hpS q hqS hpq
    change Nat.Coprime p q
    exact (Nat.Prime.coprime_iff_not_dvd (hprime p hpS)).mpr (by
      intro hpdvd
      exact hpq ((Nat.Prime.dvd_iff_eq (hprime q hqS) (hprime p hpS).ne_one).mp hpdvd).symm)
  constructor
  · intro hprod p hpS
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : ℕ => p) hpS) hprod
  · intro hx
    rw [← Finset.lcm_eq_prod hpair]
    exact Finset.lcm_dvd_iff.mpr hx

end Commons.NumberTheory.Nat
