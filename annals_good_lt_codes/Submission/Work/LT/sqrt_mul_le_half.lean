import Mathlib

namespace Work.LT

/-- Arithmetic–geometric mean inequality for two nonnegative reals:
the geometric mean of `A` and `B` is at most their arithmetic mean. -/
lemma sqrt_mul_le_half {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A * B) ≤ (A + B) / 2 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg (A - B)]

end Work.LT
