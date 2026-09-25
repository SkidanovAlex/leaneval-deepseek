import Submission.NK.Reconstruct.levelPairData
import Submission.NK.RankTheoryDeep.CorrectedFourf5
import Submission.NK.RankTheoryDeep.CorrectedResidualsDerived
import Submission.NK.ReconstructEndgame.Basic

/-!
# The level-pair bridge of the Shimizu endgame, with the **corrected** rank hypothesis

`NK.Reconstruct.LevelIsoInputOfLocalData` and
`NK.Reconstruct.LevelIsoInputOfLocalCorrespondence` are the interfaces through which the
Shimizu §4 machinery turns

* the σ-free local correspondence (a) `NK.Reconstruct.LocalCorrespondence ψ`,
* the σ-free Frobenius correspondence (b) `NK.Reconstruct.FrobeniusCorrespondencePlace ψ hψ a`,
* the three **rank inputs** `HausRankInput`, `RankStrictMonoLevelInputGen`, `ResRankInputGen`,
* and Čebotarev `NK.Reconstruct.ChebotarevInput ℚ Ω`

into the weak-Neukirch–Uchida level input `NK.ReconstructField.LevelIsoInput ψ hψ`.

The three rank inputs are used **only** through Shimizu's Proposition 4f.5,
`NK.Reconstruct.fourf5_gen_of_rankInputs : HausRankInput → RankStrictMonoLevelInputGen →
ResRankInputGen → Fourf5InputGen`.  Since (i) `NK.RankTheoryDeep` has *refuted*
`HausRankInput` (`not_hausRankInput`) and `ResRankInputGen` is stated on the degenerate invariant
`rankGamma = Module.finrank`, while (ii) the *satisfiable* replacement
`NK.RankTheoryDeep.CorrectedResidualsDeep Ω ℓ` already implies
`Fourf5InputGen Ω ℓ` (`NK.RankTheoryDeep.fourf5Gen_of_correctedResidualsDeep`), the repair is to
state the interfaces directly against

`NK.Reconstruct.Fourf5InputGen Ω ℓ`,

i.e. Shimizu's Proposition 4f.5 itself.  This file defines the two interfaces.

## Contents

* `NK.EndgameRepair.LevelIsoInputOfFourf5` — the complex-prime form;
* `NK.EndgameRepair.LevelIsoInputOfCorrespondenceFourf5` — the general form (no complex prime);
* `NK.EndgameRepair.Fourf5InputGenDerived` — `Fourf5InputGen` in the derived `ℚ`-algebra
  vocabulary of `NK.ReconstructEndgame.ratAlgebra`/`NK.Mine.ResidualsDerived`.

The *statements* below (which are what the repaired endgame is built on) use neither the refuted
rank hypotheses nor the residual structures they came from: their rank hypothesis is
`Fourf5InputGen` alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.EndgameRepair

open NK.Reconstruct
open scoped NumberField

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

universe u

/-- **The level-pair bridge of the reconstruction step with the corrected rank hypothesis, with a
complex prime on `K₁`.**

This is `NK.Reconstruct.LevelIsoInputOfLocalData K₁ K₂ ℓ` with the three `rankGamma`-inputs
`HausRankInput Ω ℓ`, `RankStrictMonoLevelInputGen Ω ℓ`, `ResRankInputGen Ω ℓ` replaced by the single
corrected input `NK.Reconstruct.Fourf5InputGen Ω ℓ` (Shimizu's Proposition 4f.5), which is what
they were used for. -/
def LevelIsoInputOfFourf5 (K₁ K₂ : NumFieldIn ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ)
    (a : LocalCorrespondence ψ) (b : FrobeniusCorrespondencePlace ψ hψ a),
    (∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v) →
    Fourf5InputGen Ω ℓ → ChebotarevInput ℚ Ω → NK.ReconstructField.LevelIsoInput ψ hψ

/-- **The level-pair bridge of the reconstruction step with the corrected rank hypothesis, in full
generality** (no complex prime on `K₁`).

This is `NK.Reconstruct.LevelIsoInputOfLocalCorrespondence K₁ K₂ ℓ` with the three
`rankGamma`-inputs replaced by `NK.Reconstruct.Fourf5InputGen Ω ℓ`. -/
def LevelIsoInputOfCorrespondenceFourf5 (K₁ K₂ : NumFieldIn ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ)
    (a : LocalCorrespondence ψ) (b : FrobeniusCorrespondencePlace ψ hψ a),
    Fourf5InputGen Ω ℓ → ChebotarevInput ℚ Ω → NK.ReconstructField.LevelIsoInput ψ hψ

/-- **Shimizu's Proposition 4f.5 in the derived `ℚ`-algebra vocabulary.**

`NK.Reconstruct.Fourf5InputGen K' ℓ` with the `ℚ`-algebra structure on `K'` (and the instances
`IsSepClosure ℚ K'`, `IsGalois ℚ K'`) derived from `[NumberField K] [Algebra K K']
[IsSepClosure K K']`, in exactly the way `NK.Mine.ResidualsDerived` and
`NK.RankTheoryDeep.CorrectedResidualsDerived` derive them. -/
def Fourf5InputGenDerived (K : Type*) (K' : Type*) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  Fourf5InputGen K' ℓ

/-- **The corrected residual implies Shimizu's Proposition 4f.5 in the derived vocabulary.** -/
theorem fourf5GenDerived_of_correctedResidualsDerived {K K' : Type u} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : NK.RankTheoryDeep.CorrectedResidualsDerived K K' ℓ) :
    Fourf5InputGenDerived K K' ℓ := by
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  exact NK.RankTheoryDeep.fourf5Gen_of_correctedResidualsDeep ℓ h

/-- **The corrected residual (ambient `ℚ`-algebra form) implies Shimizu's Proposition 4f.5.** -/
theorem fourf5Gen_of_correctedResidualsDeep {ℓ : ℕ} [Fact ℓ.Prime]
    (h : NK.RankTheoryDeep.CorrectedResidualsDeep Ω ℓ) : Fourf5InputGen Ω ℓ :=
  NK.RankTheoryDeep.fourf5Gen_of_correctedResidualsDeep ℓ h

end NK.EndgameRepair
