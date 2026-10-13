import Mathlib

namespace Work.DSM7p

/-- Arithmetic of the Krull exponent bump: if `2 * K ≤ p ^ K` and `2 ≤ p` then
`3 * K ≤ 2 * p ^ (K + 1)`. -/
theorem three_mul_le_two_mul_pow (p K : ℕ) (hp : 2 ≤ p) (hK : 2 * K ≤ p ^ K) :
    3 * K ≤ 2 * p ^ (K + 1) := by
  have h1 : 3 * K ≤ 4 * K := by omega
  have h2 : 4 * K ≤ 2 * p ^ K := by
    calc 4 * K = 2 * (2 * K) := by ring
      _ ≤ 2 * p ^ K := Nat.mul_le_mul_left 2 hK
  have h3 : 2 * p ^ K ≤ 2 * p ^ (K + 1) := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by omega) (by omega)
  linarith [h1, h2, h3]

end Work.DSM7p
