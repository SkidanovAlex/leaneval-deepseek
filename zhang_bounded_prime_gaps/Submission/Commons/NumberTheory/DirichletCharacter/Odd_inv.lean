import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Submission.Commons.NumberTheory.DirichletCharacter.L_lower_re_two_explicit

namespace Commons.NumberTheory.DirichletCharacter

/-- Odd characters have odd inverse. -/
theorem Odd_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) : (χ⁻¹).Odd := by
  change (χ⁻¹) (-1) = -1
  rw [MulChar.inv_apply_eq_inv' χ (-1), hχ]
  norm_num

end Commons.NumberTheory.DirichletCharacter