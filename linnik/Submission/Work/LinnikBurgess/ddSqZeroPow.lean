import Mathlib

namespace Work.LinnikBurgess

/-- In a commutative ring, if `x ^ 2 = 0` then `(1 + x) ^ m = 1 + m * x`:
the binomial expansion of `(1+x)^m` terminates after the linear term. -/
theorem ddSqZeroPow {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0) (m : ℕ) :
    (1 + x) ^ m = 1 + (m : R) * x := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    have hx2 : x * x = 0 := by rw [← pow_two]; exact hx
    calc (1 + ↑n * x) * (1 + x) = 1 + ↑n * x + (↑n * x * x + x) := by ring
      _ = 1 + ↑n * x + x := by rw [mul_assoc, hx2, mul_zero, zero_add]
      _ = 1 + (↑n + 1) * x := by ring

end Work.LinnikBurgess
