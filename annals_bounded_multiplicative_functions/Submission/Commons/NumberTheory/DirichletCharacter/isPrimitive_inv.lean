import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.DirichletCharacter

/-- The inverse of a primitive Dirichlet character is primitive. -/
theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rw [DirichletCharacter.conductor_inv]
  exact hχ

end Commons.NumberTheory.DirichletCharacter
