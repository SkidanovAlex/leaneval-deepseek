import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace Commons.NumberTheory.Primes

theorem prime_dvd_of_prime_pow_not_coprime {q n p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k)
    (hn : p ^ k = n) (h : ¬ Nat.Coprime n q) : p ∣ q := by
  rw [← hn] at h
  by_contra hpq
  exact h ((Nat.coprime_pow_left_iff hk p q).2 ((hp.coprime_iff_not_dvd).2 hpq))

end Commons.NumberTheory.Primes