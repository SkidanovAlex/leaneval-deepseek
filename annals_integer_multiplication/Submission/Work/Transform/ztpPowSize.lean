import Mathlib

namespace Work.Transform

/-- For every positive `t`, the highest power of two dividing the *length* of the binary
expansion of `t` is at most `t` itself: `2 ^ (t.size - 1) ≤ t`.

(Equivalently: `t.size - 1` is the number of bits below the leading bit of `t`.) -/
theorem ztpPowSize (t : ℕ) (h : 0 < t) : 2 ^ (t.size - 1) ≤ t := by
  exact Nat.lt_size.mp (by have := Nat.size_pos.mpr h; omega)

end Work.Transform
