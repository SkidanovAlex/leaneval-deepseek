import Mathlib

namespace Work.C17

theorem cb_lower (n : ℕ) : 4 ^ n ≤ (n + 1) * Nat.centralBinom n := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [Nat.centralBinom, Nat.choose]
  · have h1 := Nat.four_pow_lt_mul_centralBinom n h
    have h2 : n * Nat.centralBinom n ≤ (n + 1) * Nat.centralBinom n :=
      Nat.mul_le_mul_right _ (Nat.le_succ n)
    linarith

end Work.C17
