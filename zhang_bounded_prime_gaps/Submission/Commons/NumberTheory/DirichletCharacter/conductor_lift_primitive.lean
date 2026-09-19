import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace Commons.NumberTheory.DirichletCharacter

/-- Lifting a primitive Dirichlet character of level `c` to a multiple level `q`
does not change its conductor: `changeLevel` preserves the conductor, and a
primitive character has conductor equal to its level. -/
theorem conductor_lift_primitive {q : ℕ} [NeZero q] {c : ℕ} (h : c ∣ q)
    (ψ : DirichletCharacter ℂ c) (hprim : ψ.IsPrimitive) :
    (DirichletCharacter.changeLevel h ψ).conductor = c := by
  rw [DirichletCharacter.conductor_changeLevel ψ h]
  exact hprim

end Commons.NumberTheory.DirichletCharacter