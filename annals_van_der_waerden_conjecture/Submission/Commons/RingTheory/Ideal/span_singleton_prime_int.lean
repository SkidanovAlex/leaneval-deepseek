import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Int.Basic

namespace Commons.RingTheory.Ideal

theorem span_singleton_prime_int {p : ℕ} (hp : Nat.Prime p) :
    (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime := by
  exact Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp)

end Commons.RingTheory.Ideal
