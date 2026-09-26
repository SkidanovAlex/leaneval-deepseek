import Mathlib.Data.Nat.Digits.Defs

namespace Commons.Data.List

/-!
# An encoded digit list is smaller than the base to its length

`Nat.ofDigits B d < B ^ d.length` as soon as every digit of `d` is `< B`
(with `1 < B`).  This is the "the positional energy is monotone in length"
inequality: a word of length `ℓ` has energy `< B^ℓ`, hence any word of
strictly smaller length has strictly smaller energy.
-/
theorem ofDigits_lt_pow_base {B : ℕ} (hB : 1 < B) :
    ∀ {d : List ℕ}, (∀ x ∈ d, x < B) → Nat.ofDigits B d < B ^ d.length := by
  intro d hd
  exact Nat.ofDigits_lt_base_pow_length hB hd

end Commons.Data.List