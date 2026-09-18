import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace Commons.NumberTheory.Nat

theorem coprime_prime_pow_right_iff_not_dvd (p k a : ℕ) (hp : Nat.Prime p)
    (hk : 0 < k) : Nat.Coprime a (p ^ k) ↔ ¬ p ∣ a := by
  rw [Nat.coprime_pow_right_iff hk a p]
  rw [Nat.coprime_comm]
  exact Nat.Prime.coprime_iff_not_dvd hp

end Commons.NumberTheory.Nat