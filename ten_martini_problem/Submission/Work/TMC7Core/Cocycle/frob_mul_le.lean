import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle

/-!
# Submultiplicativity of the Frobenius norm on 2×2 complex matrices

`frob` (as defined in `Submission.Work.TMC7Core.Defs`) is Mathlib's Frobenius norm on
matrices, with the instance `Matrix.Norms.Frobenius`; over `ℝ` or `ℂ` that norm is
submultiplicative, see `Matrix.frobenius_norm_mul`.  The two lemmas below record the
identification and the resulting submultiplicativity in terms of `frob`.
-/

open scoped Matrix.Norms.Frobenius

namespace Work.TMC7Core.Cocycle

/-- `frob` agrees with Mathlib's Frobenius norm on matrices (the scoped instance
`Matrix.Norms.Frobenius`), i.e. `frob A = ‖A‖` for that norm. -/
theorem frob_eq_norm (A : Matrix (Fin 2) (Fin 2) ℂ) : frob A = ‖A‖ := by
  rw [frob, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, Real.rpow_two]
  ring

theorem frob_mul_le (A B : Matrix (Fin 2) (Fin 2) ℂ) : frob (A * B) ≤ frob A * frob B := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Work.TMC7Core.Cocycle
