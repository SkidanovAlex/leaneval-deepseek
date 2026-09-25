import Mathlib
import Submission.NK.RankTheoryDeep.ResidualsDerived
import Submission.NK.Mine.ClassicalChaptersDeep

/-!
# The wall `NK.Mine.ClassicalChaptersDeep` has no instances

`NK.Mine.ClassicalChaptersDeep` offers the complete classical-input wall of the Neukirch–Uchida
endgame as a single structure, but its rank field
`residuals : ∀ (ℓ : ℕ) [Fact ℓ.Prime], NK.Mine.ResidualsDerived K₁ K₁' ℓ` is unsatisfiable:
`NK.RankTheoryDeep.not_residualsDerived` (from
`NK.RankTheoryDeep.not_gammaTFRankFinite_prime`, whose content is that for `K = ℚ` the
torsion-free quotient of Shimizu's `Γ_K` has infinite `ℤ_ℓ`-rank) refutes `ResidualsDerived K K' ℓ`
at every prime `ℓ`.  Specialising to `ℓ = 2` kills the wall, so its capstones
`NK.Mine.neukirch_uchida_of_deepChapters` and `NK.Mine.challenge_of_deepChapters` are vacuous.

The repaired wall (with `NK.RankTheoryDeep.CorrectedResidualsDerived` in place of the refuted
`ResidualsDerived`) lives in `Submission/Work/EndgameRepair/Wall.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.EndgameRepair

/-- **The wall `NK.Mine.ClassicalChaptersDeep` is unsatisfiable**: its rank field demands
`NK.Mine.ResidualsDerived K₁ K₁' ℓ` at every prime `ℓ`, which is false already at `ℓ = 2`. -/
theorem not_classicalChaptersDeep (K₁ K₂ K₁' K₂' : Type) [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] :
    ¬ NK.Mine.ClassicalChaptersDeep K₁ K₂ K₁' K₂' := fun h =>
  NK.RankTheoryDeep.not_residualsDerived K₁ K₁' 2 (h.residuals 2)

end NK.EndgameRepair
