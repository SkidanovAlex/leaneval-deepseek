import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Commons.Data.Nat

open scoped BigOperators

/-- The divisor-count function `τ(n) = n.divisors.card` is multiplicative on
coprime factors: for `(m,n) = 1`, `τ(m·n) = τ(m)·τ(n)`. -/
theorem card_divisors_mul_of_coprime (m n : ℕ) (hcop : Nat.Coprime m n) :
    (m * n).divisors.card = m.divisors.card * n.divisors.card := by
  exact Nat.Coprime.card_divisors_mul hcop

end Commons.Data.Nat
