import Mathlib.Data.Nat.Totient

namespace Commons.NumberTheory.Totient

/-- `φ(mn) · φ(gcd m n) = φ m · φ n · gcd m n`, the Euler-totient form of
the identity `mn · gcd(m,n) = m · n` after removing repeated prime factors. -/
theorem totient_mul_gcd (m n : ℕ) :
    Nat.totient (m * n) * Nat.totient (Nat.gcd m n) =
      Nat.totient m * Nat.totient n * Nat.gcd m n := by
  rw [Nat.mul_comm]
  exact Nat.totient_gcd_mul_totient_mul m n

end Commons.NumberTheory.Totient
