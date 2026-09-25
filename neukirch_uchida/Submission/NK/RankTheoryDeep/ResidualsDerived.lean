import Submission.NK.RankTheoryDeep.Unconditional
import Submission.NK.Mine.NeukirchUchidaOfResiduals
import Submission.NK.Mine.ClassicalChapters

/-!
# The residual of the live route `<X> is unsatisfiable</X>` — in the vocabulary of its consumers

`Unconditional.lean` proves that `NK.ShimizuRank.Residuals Ω ℓ` — hence the rank input of the live
Shimizu route — is unsatisfiable for every prime `ℓ`.  This file restates that in the *derived*
vocabulary in which the endgame actually consumes it, so that a caller holding one of those
hypotheses can discharge it directly:

* `NK.RankTheoryDeep.not_residualsDerived` — `NK.Mine.ResidualsDerived K K' ℓ` (the
  `ℚ`-structure-free form of `Residuals K' ℓ` used by
  `NK.Mine.neukirch_uchida_of_localStructureData_residuals`) is **false**;
* `NK.RankTheoryDeep.not_classicalChapters` — hence so is the complete classical-input wall
  `NK.Mine.ClassicalChapters K₁ K₂ K₁' K₂'` (`Submission/Work/Mine/ClassicalChapters.lean`), whose
  field `residuals` demands `ResidualsDerived K₁ K₁' ℓ` at *every* prime `ℓ`
  (refuted at `ℓ = 2`).

The failure is a genuine mathematical one and not a gap in the formalisation: the field
`rankFinite : GammaTFRankFinite Ω ℓ` of `Residuals` asserts that the *torsion-free* quotient of
Shimizu's `Γ_K` has finite `ℤ_ℓ`-rank, whereas the honest invariant `r_ℓ(K)` is the rank of the
*Hausdorff* quotient `Γ_K ⧸ invisible` (equivalently, of the idèle-class-group character module
`Hom_cts(C_K, ℤ_ℓ)`); for `K = ℚ` the two differ, and the torsion-free quotient has rank `ℵ₀`.
The repair is `NK.RankTheoryDeep.CorrectedResiduals Ω ℓ` (see `Corrected.lean` and `README.md`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.RankTheoryDeep

universe u

/-- **`NK.Mine.ResidualsDerived K K' ℓ` is unsatisfiable** for every prime `ℓ`, because its
`GammaTFRankFinite` field is (`NK.RankTheoryDeep.not_gammaTFRankFinite_prime`, witnessed by
`K = ℚ`). -/
theorem not_residualsDerived (K : Type) [Field K] [NumberField K] (K' : Type) [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] :
    ¬ NK.Mine.ResidualsDerived K K' ℓ := by
  intro h
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  exact not_gammaTFRankFinite_prime ℓ K' h.rankFinite

/-- **The complete classical-input wall of the Shimizu route is unsatisfiable.**

`NK.Mine.ClassicalChapters K₁ K₂ K₁' K₂'` bundles the five classical chapters that the live route
needs; its fourth field `residuals` demands the (false) rank structure at every prime.  So the
"one name for the wall" theorem `NK.Mine.neukirch_uchida_of_classicalChapters` cannot be applied:
the wall has no instances. -/
theorem not_classicalChapters (K₁ K₂ K₁' K₂' : Type) [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] :
    ¬ NK.Mine.ClassicalChapters K₁ K₂ K₁' K₂' := fun h =>
  not_residualsDerived K₁ K₁' 2 (h.residuals 2)

end NK.RankTheoryDeep
