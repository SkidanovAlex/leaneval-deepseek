import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace Commons.NumberTheory.DirichletCharacter

/-- The inverse of a primitive Dirichlet character is primitive. -/
theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rw [DirichletCharacter.conductor_inv]
  exact hχ

end Commons.NumberTheory.DirichletCharacter
