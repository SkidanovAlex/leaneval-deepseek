import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.DirichletCharacter

/-- Odd characters have odd inverse. -/
theorem Odd_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) : (χ⁻¹).Odd := by
  change (χ⁻¹) (-1) = -1
  rw [MulChar.inv_apply_eq_inv' χ (-1), hχ]
  norm_num

end Commons.NumberTheory.DirichletCharacter