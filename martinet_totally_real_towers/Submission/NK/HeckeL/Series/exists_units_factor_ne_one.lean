import Mathlib
import Submission.NK.HeckeL.Zeta

namespace NK.HeckeL.Series

/-- Every (nontrivial) complex-valued character of a finite group factors through the units of
`ℂ`: its values are roots of unity, hence invertible. -/
theorem exists_units_factor_ne_one {G : Type*} [Group G] [Finite G] {χ : G →* ℂ}
    (hχ : χ ≠ 1) :
    ∃ ψ : G →* ℂˣ, ψ ≠ 1 ∧ (Units.coeHom ℂ).comp ψ = χ := by
  refine ⟨χ.toHomUnits, fun h => hχ ?_, ?_⟩
  · have h1 : (Units.coeHom ℂ).comp χ.toHomUnits = χ := by ext g; simp
    have := congrArg (fun f => (Units.coeHom ℂ).comp f) h
    rw [h1] at this
    simpa using this
  · ext g; simp

end NK.HeckeL.Series
