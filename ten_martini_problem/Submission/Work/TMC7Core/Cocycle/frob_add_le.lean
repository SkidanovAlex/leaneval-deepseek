import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le

/-!
# The triangle inequality for the Frobenius norm on 2×2 complex matrices

`frob` is Mathlib's Frobenius norm on matrices restricted to `Fin 2` (see
`frob_eq_norm` in `Submission.Work.TMC7Core.Cocycle.frob_mul_le`), so the triangle
inequality is the triangle inequality of that norm.
-/

open scoped Matrix.Norms.Frobenius

namespace Work.TMC7Core.Cocycle

theorem frob_add_le (A B : Matrix (Fin 2) (Fin 2) ℂ) : frob (A + B) ≤ frob A + frob B := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact norm_add_le A B

end Work.TMC7Core.Cocycle
