import Mathlib

namespace Work.Transform

/-- Bit-length is submultiplicative: `size (a*b) ≤ size a + size b`.
(`Nat.size n` is the number of binary digits of `n`, i.e. `0.size = 0` and
`n.size = ⌊log₂ n⌋ + 1` for `n > 0`.) -/
theorem ztpSizeMul (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le]
  calc a * b < 2 ^ a.size * 2 ^ b.size :=
        Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ = 2 ^ (a.size + b.size) := (Nat.pow_add ..).symm

end Work.Transform
