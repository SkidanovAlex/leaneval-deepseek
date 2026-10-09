import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.NK.ResidueFrob.Main
import Submission.NK.FrobeniusBridge.Main
import Submission.NK.LocalTame.Inputs
import Submission.NK.TameStructureDeep.Tame.Unconditional
import Submission.NK.TameData.Main
import Submission.NK.LocalKW.Setup
import Submission.NK.Mine.AdjoinLocalGalois
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary vocabulary for `Work.SSGRoute.local_tame_lifting`

This module only collects the imports (the local-structure library `NK.*`) and two definitions
used by the lemmas `Work.SSGRoute.local_tame_lifting` is built from:

* `Work.SSGRoute.IsTrivialAtLevelQBar A L g` — `g` acts trivially on the residue field of the finite
  normal level `L` at the place below `A` (the unfolded form of
  `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel`, kept here because the library's version needs
  extra instance arguments that are awkward to synthesise in a statement over `ℚ`);
* `Work.SSGRoute.residueChar A` — the residue characteristic of the place `A` of `ℚ̄` (the prime
  `ℓ` below `A`).
-/

open SSGRoute

namespace Work.SSGRoute

/-- `ℚ̄ = AlgebraicClosure ℚ` is an algebraic closure of `ℚ`. -/
instance (priority := 100) instIsAlgClosureQBar : IsAlgClosure ℚ SSGRoute.QBar :=
  AlgebraicClosure.instIsAlgClosure ℚ

/-- `ℚ̄ = AlgebraicClosure ℚ` is a separable closure of `ℚ`. -/
instance (priority := 100) instIsSepClosureQBar : IsSepClosure ℚ SSGRoute.QBar :=
  IsSepClosure.of_isAlgClosure_of_perfectField ℚ SSGRoute.QBar

/-- **`g` acts trivially on the residue field of the level `L` at the place below `A`.**

This is the unfolded form of `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel`. -/
def IsTrivialAtLevelQBar (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [Normal ℚ L]
    [NumberField ↥L] (g : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) : Prop :=
  ∀ x : NumberField.RingOfIntegers ↥L,
    galRestrict (NumberField.RingOfIntegers ℚ) ℚ ↥L (NumberField.RingOfIntegers ↥L)
      (AlgEquiv.restrictNormalHom L g) x - x ∈
      (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)).asIdeal

/-- **The residue characteristic of a finite place of `ℚ̄`**: the (prime) cardinality of the
residue field of `ℚ` at the prime below `A`. -/
noncomputable def residueChar (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) : ℕ :=
  Nat.card (NumberField.RingOfIntegers ℚ ⧸
    (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal)

end Work.SSGRoute
