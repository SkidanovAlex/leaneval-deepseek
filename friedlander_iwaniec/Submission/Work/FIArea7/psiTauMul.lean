import Mathlib

namespace Work.FIArea7

/-- The divisor-count function is submultiplicative: `τ(m n) ≤ τ(m) τ(n)`.
(From `Nat.divisors_mul : (m*n).divisors = m.divisors * n.divisors` and
`Finset.card_mul_le`.) -/
theorem psiTauMul (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

end Work.FIArea7
