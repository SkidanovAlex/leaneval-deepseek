import Mathlib

namespace Commons.Algebra.Eberlein

theorem eberlein_formula (k ℓ i : ℕ) (hiℓ : i ≤ ℓ) (hik : i ≤ k - ℓ) :
    ((2 ^ (ℓ - i) - 1) * (2 ^ (k - ℓ + 1) - 2) : ℤ) -
        ((2 ^ (ℓ + 1 - i) - 1) * (2 ^ i - 1) : ℤ) =
      (2 ^ (i + 1) * (2 ^ (ℓ - i) - 1) * (2 ^ (k - ℓ - i) - 1) : ℤ) -
        (2 ^ i - 1) := by
  have hL : ℓ + 1 - i = ℓ - i + 1 := by omega
  have hK : k - ℓ + 1 = i + (k - ℓ - i) + 1 := by omega
  rw [hL, hK]
  rw [pow_succ, pow_add]
  ring

end Commons.Algebra.Eberlein
