import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.BrauerTwist.Basic
import Submission.NK.ChebotarevGeneral.Main
import Submission.NK.HassePrinciple.Norm
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.RankTheoryDeep.CorrectedPackage
import Submission.NK.ReconstructEndgame.Basic
import Submission.NK.ResidueFrob.LocalStructureInputs
import Submission.NK.WeakNU.decompositionSubgroup_eq_zpowers_of_isFrobAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corrected residual, in the **derived** vocabulary of the live route

`NK.Mine.ResidualsDerived K K' ℓ` (`Submission/Work/Mine/NeukirchUchidaOfResiduals.lean`) is
*definitionally* `NK.ShimizuRank.Residuals K' ℓ` with the `ℚ`-algebra structure on `K'` derived
from `[NumberField K] [Algebra K K'] [IsSepClosure K K']`; it is the rank hypothesis of the endgame
theorem `NK.Mine.neukirch_uchida_of_localStructureData_residuals`, and it is **false**
(`NK.RankTheoryDeep.not_residualsDerived`).

This file provides, in the same vocabulary, the **corrected** structure
`NK.RankTheoryDeep.CorrectedResidualsDerived K K' ℓ`, together with the three rank statements the
endgame needs, all *proved* from it:

* `hausQuotRankFinite_of_correctedResidualsDerived` (CoNF (10.3.20) for the Hausdorff quotient),
* `hausRankStrictMono_of_correctedResidualsDerived` (Shimizu's Lemma 4f.2),
* `resRankInputHaus_of_correctedResidualsDerived` (the rank step of Proposition 4f.5).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NumberField

namespace NK.RankTheoryDeep

universe u

/-- **The corrected residual in the derived `ℚ`-algebra form**: the same transport as
`NK.Mine.ResidualsDerived`, applied to the corrected structure
`NK.RankTheoryDeep.CorrectedResidualsDeep`. -/
def CorrectedResidualsDerived (K : Type u) (K' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  CorrectedResidualsDeep K' ℓ

/-- **The rank finiteness, transported**: `HausQuotRankFinite K' ℓ` with the `ℚ`-algebra structure
on `K'` derived from `[NumberField K] [Algebra K K'] [IsSepClosure K K']`, in the same way as
`NK.Mine.ResidualsDerived`. -/
def HausQuotRankFiniteDerived (K : Type u) (K' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  HausQuotRankFiniteTop K' ℓ

/-- **Shimizu's Lemma 4f.2, transported.** -/
def HausRankStrictMonoDerived (K : Type u) (K' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  HausRankStrictMono K' ℓ

/-- **The rank step of Shimizu's Proposition 4f.5, transported.** -/
def ResRankInputHausDerived (K : Type u) (K' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  ResRankInputHaus K' ℓ

/-- **The rank finiteness, from the corrected residual, in the derived vocabulary.** -/
theorem hausQuotRankFinite_derived_of_corrected {K K' : Type u} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDerived K K' ℓ) : HausQuotRankFiniteDerived K K' ℓ := by
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  exact hausQuotRankFiniteTop_of_correctedResidualsDeep h

/-- **Shimizu's Lemma 4f.2, from the corrected residual, in the derived vocabulary.** -/
theorem hausRankStrictMono_derived_of_corrected {K K' : Type u} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDerived K K' ℓ) : HausRankStrictMonoDerived K K' ℓ := by
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  exact hausRankStrictMono_of_correctedResidualsDeep h

/-- **The rank step of Proposition 4f.5, from the corrected residual, in the derived vocabulary.** -/
theorem resRankInputHaus_derived_of_corrected {K K' : Type u} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDerived K K' ℓ) : ResRankInputHausDerived K K' ℓ := by
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  exact resRankInputHaus_of_correctedResidualsDeep h

end NK.RankTheoryDeep
