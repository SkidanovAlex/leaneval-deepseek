import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace Commons.NumberTheory.DirichletCharacter

theorem Even_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Even) : (χ⁻¹).Even := by
  change χ⁻¹ (-1) = 1
  rw [MulChar.inv_apply_eq_inv']
  rw [hχ]
  simp

end Commons.NumberTheory.DirichletCharacter