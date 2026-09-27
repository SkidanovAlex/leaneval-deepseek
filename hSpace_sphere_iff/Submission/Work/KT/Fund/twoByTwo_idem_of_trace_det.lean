import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT.Fund

/-- A 2×2 matrix over a commutative ring whose trace is `1` and whose determinant
vanishes (written multiplicatively as `h 0 0 * h 1 1 = h 0 1 * h 1 0`) is idempotent. -/
theorem twoByTwo_idem_of_trace_det {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R)
    (htr : h 0 0 + h 1 1 = 1) (hdet : h 0 0 * h 1 1 = h 0 1 * h 1 0) : h * h = h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · show h 0 0 * h 0 0 + h 0 1 * h 1 0 = h 0 0
    rw [← hdet, ← mul_add, htr, mul_one]
  · show h 0 0 * h 0 1 + h 0 1 * h 1 1 = h 0 1
    rw [mul_comm (h 0 0) (h 0 1), ← mul_add, htr, mul_one]
  · show h 1 0 * h 0 0 + h 1 1 * h 1 0 = h 1 0
    rw [mul_comm (h 1 1) (h 1 0), ← mul_add, htr, mul_one]
  · show h 1 0 * h 0 1 + h 1 1 * h 1 1 = h 1 1
    rw [mul_comm (h 1 0) (h 0 1), ← hdet, ← add_mul, htr, one_mul]

end Work.KT.Fund
