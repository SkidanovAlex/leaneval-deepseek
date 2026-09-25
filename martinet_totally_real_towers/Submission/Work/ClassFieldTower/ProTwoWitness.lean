import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.ProTwo
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.hasGenusLevel_witness
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.unitTwoRank_eq_one_of_imaginaryQuadratic
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five

/-!
# `Work.ClassFieldTower.ProTwoWitness` -- the sound capstone for `Kc = ℚ(√-30030)`

For the concrete imaginary quadratic field `Kc = ℚ(√-30030)` the **numerical half** of
`ProTwoTowerInput Kc` is PROVED
(`Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five`:
`5 ≤ classGroupTwoRank Kc`, and `unitTwoRank Kc = 1`).  Hence

    `ProTwoTowerInput Kc` ⟺ `ProTwoPresentationData Kc`,

and the latter is the classical Golod--Shafarevich arithmetic for `Kc`: a finite presentation of
the abstract pro-`2` group of `G_∅` with `5` generators and at most `6` relators, residually a
finite `2`-group, whose finite `2`-quotients are realized by unramified extensions of `Kc`
(Shafarevich--Koch: `d(G_∅) = rank₂ Cl(Kc)`, `r - d ≤ d₂(O_K^×) = 1`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- `unitTwoRank Kc ≤ 1` (in fact `= 1`), proved via `unitTwoRank_eq_one_of_imaginaryQuadratic`. -/
theorem unitTwoRank_witness_le_one : unitTwoRank Kc ≤ 1 := by
  haveI : NumberField.IsTotallyComplex Kc := isTotallyComplex
  exact le_of_eq (unitTwoRank_eq_one_of_imaginaryQuadratic Kc finrank_eq_two)

/-- **The numerical half of the input for `Kc` is discharged.** -/
theorem proTwoTowerInput_witness_of_presentationData (h : ProTwoPresentationData Kc) :
    ProTwoTowerInput Kc :=
  ⟨h, five_le_classGroupTwoRank, unitTwoRank_witness_le_one⟩

/-- **THE SOUND CAPSTONE FOR `Kc`.**  From the Shafarevich--Koch presentation datum for `Kc`,
the maximal unramified pro-`2` extension of `Kc` is infinite -- `Kc` has an infinite Hilbert
`2`-class field tower. -/
theorem infiniteProTwoExtension_witness_of_presentationData (h : ProTwoPresentationData Kc) :
    InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_of_proTwoTowerInput (proTwoTowerInput_witness_of_presentationData h)

/-- **The wall of the chapter, in the sound formulation.**  There is an imaginary quadratic field
whose maximal unramified pro-`2` extension is infinite. -/
def HasInfiniteHilbertTwoClassFieldTower : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyComplex F)
    (_ : Module.finrank ℚ F = 2), InfiniteProTwoExtension F

/-- **THE WALL, from the explicit field `Kc`.** -/
theorem hasInfiniteHilbertTwoClassFieldTower_of_witness (h : ProTwoPresentationData Kc) :
    HasInfiniteHilbertTwoClassFieldTower :=
  ⟨Kc, inferInstance, inferInstance, isTotallyComplex, finrank_eq_two,
    infiniteProTwoExtension_witness_of_presentationData h⟩

/-- The tower consequence for `Kc`: unramified levels of unbounded degree with constant root
discriminant `rootDiscr Kc`. -/
theorem exists_unramifiedLevel_rootDiscr_witness_of_presentationData
    (h : ProTwoPresentationData Kc) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  exists_unramifiedNumberField_of_proTwoTowerInput (proTwoTowerInput_witness_of_presentationData h) N

/-- **THE REDUCED CAPSTONE FOR `Kc`.**  The single remaining class-field-theoretic input for the
concrete field `Kc = ℚ(√-30030)` is its *name* as the maximal unramified pro-`2` extension
(`ProTwoShafarevichKochInput Kc`: the Shafarevich--Koch relation bound `#rel ≤ #α + 1` plus a
description of `G_∅` by the finite `2`-quotients of an abstract group).  The bound `5 ≤ #α` comes
from the **genus level** (`HasGenusLevel Kc`, pure genus theory), which is the other hypothesis
of this theorem. -/
theorem infiniteProTwoExtension_witness_of_shafarevichKoch_and_genusLevel
    (h : ProTwoShafarevichKochInput Kc) (hgenus : HasGenusLevel Kc) :
    InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_of_shafarevichKoch_and_genusLevel h hgenus

/-- **THE REDUCED CAPSTONE FOR `Kc`, with the genus level discharged.**  The genus level of
`Kc = ℚ(√-30030)` -- an unramified exponent-`2` Galois extension of degree `32` -- is PROVED
(`Work.ClassFieldTower.hasGenusLevel_witness`).  Hence the single remaining input for the
infinitude of the maximal unramified pro-`2` extension of `Kc` is

    `Work.ClassFieldTower.ProTwoShafarevichKochInput Kc`,

i.e. a description of `G_∅` by the finite `2`-quotients of an abstract finitely presented group
`G` (`DescribesMaximalProTwo Kc G`) together with the Shafarevich--Koch relation bound
`#rel ≤ #α + 1`.  Nothing numerical is left: `5 ≤ #α` is derived from the genus level. -/
theorem infiniteProTwoExtension_witness_of_shafarevichKoch
    (h : ProTwoShafarevichKochInput Kc) : InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_witness_of_shafarevichKoch_and_genusLevel h hasGenusLevel_witness

/-- **THE WALL, from `Kc`, with only the Shafarevich--Koch input left.** -/
theorem hasInfiniteHilbertTwoClassFieldTower_of_shafarevichKoch
    (h : ProTwoShafarevichKochInput Kc) : HasInfiniteHilbertTwoClassFieldTower :=
  ⟨Kc, inferInstance, inferInstance, isTotallyComplex, finrank_eq_two,
    infiniteProTwoExtension_witness_of_shafarevichKoch h⟩

/-- **The tower over `Kc` with the genus level discharged.** -/
theorem exists_unramifiedLevel_rootDiscr_witness_of_shafarevichKoch
    (h : ProTwoShafarevichKochInput Kc) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc := by
  obtain ⟨M, hM⟩ := infiniteProTwoExtension_witness_of_shafarevichKoch h
  exact exists_unramifiedLevel_of_infinite M hM N

end Work.ClassFieldTower
