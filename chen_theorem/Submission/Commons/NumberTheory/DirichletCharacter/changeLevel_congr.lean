import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace Commons.NumberTheory.DirichletCharacter

/-- Extending a Dirichlet character to a multiple of its level does not depend on the
particular proof that the levels divide one another. -/
theorem changeLevel_congr {n m : ℕ} {h₁ h₂ : n ∣ m} (χ : DirichletCharacter ℂ n) :
    DirichletCharacter.changeLevel h₁ χ = DirichletCharacter.changeLevel h₂ χ := by
  -- `changeLevel h χ` only depends on `ZMod.unitsMap h`, and `ZMod.unitsMap h` only
  -- depends on the map underlying `ZMod.castHom h`, which is `ZMod.cast` regardless of `h`.
  have hunits : ZMod.unitsMap h₁ = ZMod.unitsMap h₂ := by
    refine MonoidHom.ext (fun a => ?_)
    exact Units.ext rfl
  exact congrArg (fun g : (ZMod m)ˣ →* (ZMod n)ˣ => MulChar.ofUnitHom (χ.toUnitHom.comp g)) hunits

end Commons.NumberTheory.DirichletCharacter