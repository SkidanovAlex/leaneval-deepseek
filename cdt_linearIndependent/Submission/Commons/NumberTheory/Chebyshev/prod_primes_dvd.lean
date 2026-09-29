import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Defs

namespace Commons.NumberTheory.Chebyshev

theorem prod_primes_dvd {s : Finset ℕ} {q : ℕ} (hp : ∀ p ∈ s, p.Prime) (hd : ∀ p ∈ s, p ∣ q) :
    Finset.prod s (fun p => p) ∣ q := by
  exact Finset.prod_primes_dvd q (fun p hps => Nat.prime_iff.mp (hp p hps)) hd

end Commons.NumberTheory.Chebyshev