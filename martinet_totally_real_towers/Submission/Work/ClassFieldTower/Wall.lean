import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.ProTwo
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.ProTwoWitness
import Submission.Work.ClassFieldTower.ProTwoGeneratorRank
import Submission.Work.ClassFieldTower.ResiduallyFiniteGaloisGroup
import Submission.Work.ClassFieldTower.Bridge
import Submission.Work.ClassFieldTower.shafarevichKochBound_iff_deficiency
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five
import Submission.Work.ProPDeficiency.Deficiency

/-!
# `Work.ClassFieldTower.Wall` -- the single remaining input, and everything proved without it

This is the consumer-facing module of the class-field-tower chapter: **one import, one named
wall, and the complete list of unconditional results.**

## The wall

```lean
Work.ClassFieldTower.KcWall              : Prop := ProTwoShafarevichKochInput Kc
Work.ClassFieldTower.KcPresentationWall  : Prop := ProTwoPresentationData Kc
```

with `Kc = ℚ(√-30030)` (`WitnessField.lean`).  Either one implies the infinitude of the maximal
unramified pro-`2` extension of `Kc`, hence an unramified tower of unbounded degree with
constant root discriminant, hence (through `Bridge.lean`) the main agent's waves
`Submission.NumberField.UnramifiedPro2TowerWall` and
`Submission.NumberField.BoundedRdTowerWall`.

Both walls are *sound* (unlike the refuted `GolodShafarevichCertificate`, see `Vacuity.lean`)
and *satisfiable in principle* (take `G` to be the abstract group of a pro-`2` presentation of
`G_∅`); both say exactly the classical Golod--Shafarevich / Shafarevich--Koch input:

* `KcWall` = the pro-`2` presentation datum with `#rel ≤ #α + 1` (the deficiency bound
  `r - d ≤ d₂(O_K^×) = 1`) together with the description of `G_∅` by the finite `2`-quotients of
  `G`; the generator bound `5 ≤ #α` is DERIVED from the genus level of `Kc`
  (`hasGenusLevel_witness`), with no class field theory;
* `KcPresentationWall` = the same without the description, but with the generator number *pinned*
  to `rank₂ Cl(Kc)` (the Artin statement `d(G_∅) = rank₂ Cl(Kc)`), the numerical certificate
  `5 ≤ rank₂ Cl(Kc)` being proved in this chapter unconditionally.

## What is proved unconditionally (no class field theory)

* the objects: `F_∅` exists and is unramified pro-`2` (`exists_maximalUnramifiedProP`);
* `ResiduallyFiniteTwoGroup G_∅` (`ResiduallyFiniteGaloisGroup.lean`) -- one of the two structural
  hypotheses of the wall, for the genuine group;
* `G_∅ ↠ (𝔽₂)^5`, i.e. `d(G_∅) ≥ 5` (`ProTwoGeneratorRank.lean`) -- the generator half of the
  Golod--Shafarevich input, from genus theory;
* `rank₂ Cl(Kc) ≥ 5` (`exists_imaginaryQuadratic_classGroupTwoRank_ge_five`) -- the same bound on
  the class-group side, by exhibiting `2^5` independent `2`-torsion classes;
* `d₂(O_K^×) = 1` for `Kc` (`unitTwoRank_witness_le_one`);
* an unramified Galois extension of `Kc` of degree `2^5` with constant root discriminant
  (`exists_unramifiedLevel_rootDiscr_genusLevel_witness`);
* the whole Golod--Shafarevich reduction: wall ⟹ infinite tower ⟹ asymptotically good family.

The relation count `r ≤ d + 1` for the *maximal* group is the only missing ingredient; it is a
theorem of global class field theory (Koch, *Galois Theory of p-Extensions*, Ch. 11 Thm 11.3;
Neukirch--Schmidt--Wingberg Cor. 10.7.7, via `Sha_∅ ↪ C_∅ = (V_∅/K^{×2})^∨` with
`V_∅ = {x ∈ K^× : (x) = I²}`), and this workspace contains no global class field theory.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-! ## 1. The wall, named -/

/-- **THE WALL.**  The classical Shafarevich--Koch input for the explicit imaginary quadratic
field `Kc = ℚ(√-30030)`: an abstract group `G` with a minimal presentation by `#α` generators and
`rel` relators satisfying the deficiency bound `#rel ≤ #α + 1`, residually a finite `2`-group,
whose finite `2`-quotients are exactly the unramified pro-`2` Galois extensions of `Kc`.

Together with the genus level `hasGenusLevel_witness : HasGenusLevel Kc` (proved, no class field
theory) this gives the generator bound `5 ≤ #α`
(`infiniteProTwoExtension_of_shafarevichKoch_and_genusLevel`), and hence
`4 · #rel ≤ #α²` and an INFINITE Hilbert `2`-class field tower over `Kc`.

This is the single remaining input of the chapter; everything else is proved. -/
def KcWall : Prop := ProTwoShafarevichKochInput Kc

/-- **The wall, presentation form** (the assignment's "essential consumable form"): `G_∅` has a
minimal presentation with `d = rank₂ Cl(Kc)` generators and `r ≤ d + d₂(O_K^×)` relators, `G` is
residually a finite `2`-group and its finite `2`-quotients are realized by unramified extensions
of `Kc`.  The numerical certificate `5 ≤ rank₂ Cl(Kc) ≥ d` is proved in this chapter
(`five_le_classGroupTwoRank`), so this datum also gives `4 r ≤ d²`. -/
def KcPresentationWall : Prop := ProTwoPresentationData Kc

/-! ## 2. Consequences of the wall -/

/-- **The wall implies infinitude of the maximal unramified pro-`2` extension of `Kc`.** -/
theorem infiniteProTwoExtension_of_kcWall (h : KcWall) : InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_witness_of_shafarevichKoch h

/-- **The wall implies an unramified level of any prescribed degree over `Kc`**, with constant
root discriminant: for every `N` a finite Galois `L/Kc` with `[L : Kc] ≥ N`,
`differentIdeal (𝓞 Kc) (𝓞 L) = ⊤` and `rootDiscr L = rootDiscr Kc`. -/
theorem exists_unramifiedLevel_rootDiscr_of_kcWall (h : KcWall) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  exists_unramifiedLevel_rootDiscr_witness_of_shafarevichKoch h N

/-- **The wall implies the pointwise form** consumed by
`Submission.NumberField.boundedRdTowerWall_of_unbounded_unramified`. -/
theorem unbounded_unramified_of_kcWall (h : KcWall) :
    ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ := by
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, -⟩ := exists_unramifiedLevel_rootDiscr_of_kcWall h N
  exact ⟨L, iL, iNL, iAL, hfd, hdeg, hdiff⟩

/-- **THE BRIDGE TO THE MAIN AGENT'S WALL.** -/
theorem unramifiedPro2TowerWall_of_kcWall (h : KcWall) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_shafarevichKoch_witness h

/-- **The tower wall, in root-discriminant form.** -/
theorem boundedRdTowerWall_of_kcWall (h : KcWall) :
    Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_shafarevichKoch_witness h

/-- **The tower wall, in discriminant form.** -/
theorem boundedDiscrTowerWall_of_kcWall (h : KcWall) :
    Submission.NumberField.BoundedDiscrTowerWall :=
  Submission.NumberField.boundedDiscrTowerWall_of_boundedRdTowerWall
    (boundedRdTowerWall_of_kcWall h)

/-! ## 3. The same for the presentation form of the wall -/

/-- **The presentation wall implies infinitude of the maximal unramified pro-`2` extension.** -/
theorem infiniteProTwoExtension_of_kcPresentationWall (h : KcPresentationWall) :
    InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_witness_of_presentationData h

/-- **The presentation wall implies the main agent's wall.** -/
theorem unramifiedPro2TowerWall_of_kcPresentationWall (h : KcPresentationWall) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_infiniteProTwoExtension
    (infiniteProTwoExtension_of_kcPresentationWall h)

/-- **The presentation wall implies the root-discriminant tower wall.** -/
theorem boundedRdTowerWall_of_kcPresentationWall (h : KcPresentationWall) :
    Submission.NumberField.BoundedRdTowerWall :=
  Submission.NumberField.boundedRdTowerWall_of_unramifiedPro2TowerWall
    (unramifiedPro2TowerWall_of_kcPresentationWall h)

/-- **The presentation wall implies an unramified level of any prescribed degree**, with constant
root discriminant `rootDiscr Kc`. -/
theorem exists_unramifiedLevel_rootDiscr_of_kcPresentationWall (h : KcPresentationWall) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  exists_unramifiedLevel_rootDiscr_witness_of_presentationData h N

/-- **The presentation wall implies the discriminant-form tower wall.** -/
theorem boundedDiscrTowerWall_of_kcPresentationWall (h : KcPresentationWall) :
    Submission.NumberField.BoundedDiscrTowerWall :=
  Submission.NumberField.boundedDiscrTowerWall_of_boundedRdTowerWall
    (boundedRdTowerWall_of_kcPresentationWall h)

/-! ## 4. The unconditional certificate, in one statement -/

/-- **EVERYTHING PROVED UNCONDITIONALLY, IN ONE STATEMENT** (no class field theory, no relation
count):

* `rank₂ Cl(Kc) ≥ 5`;
* `d₂(O_K^×) = 1` (so the deficiency bound reads `r ≤ d + 1`);
* the genus level of `Kc` (an unramified exponent-`2` extension of degree `32`);
* `G_∅ ↠ (𝔽₂)^5` for a maximal unramified pro-`2` extension (i.e. `d(G_∅) ≥ 5`);
* an unramified Galois extension of `Kc` of degree `2^5` with constant root discriminant. -/
theorem kc_numericalCertificate :
    5 ≤ classGroupTwoRank Kc ∧ unitTwoRank Kc ≤ 1 ∧ HasGenusLevel Kc ∧
      (∃ M : MaximalUnramifiedProP.{0} Kc 2, HasFiveIndependentUnramifiedQuadratics M) ∧
      (∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
        (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
        Module.finrank Kc L = 2 ^ 5 ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
          NumberField.rootDiscr L = NumberField.rootDiscr Kc) ∧
      ∃ F : Type, ∃ (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyComplex F)
        (_ : Module.finrank ℚ F = 2), 5 ≤ classGroupTwoRank F :=
  ⟨five_le_classGroupTwoRank, unitTwoRank_witness_le_one, hasGenusLevel_witness,
    exists_hasFiveIndependentUnramifiedQuadratics_witness,
    exists_unramifiedLevel_rootDiscr_genusLevel_witness,
    exists_imaginaryQuadratic_classGroupTwoRank_ge_five⟩

/-! ## 5. The deficiency bound in the standard normalisation -/

/-- **The Shafarevich--Koch bound as a deficiency bound.**  `ShafarevichKochBound F d r` says
`r ≤ d + d₂(O_F^×)`, i.e. the deficiency `r - d` is at most `d₂(O_F^×)`; this is
`Work.ProPDeficiency.Deficiency d r (-(d₂(O_F^×)))`, the `Deficiency d r u := r + u ≤ d` of the
pro-`p` group theory chapter. -/
theorem shafarevichKochBound_iff_proPDeficiency {F : Type} [Field F] [NumberField F] {d r : ℕ} :
    ShafarevichKochBound F d r ↔
      Work.ProPDeficiency.Deficiency d r (-(unitTwoRank F : ℤ)) := by
  simp only [ShafarevichKochBound, Work.ProPDeficiency.Deficiency]
  omega

/-- **The deficiency form of the Shafarevich--Koch bound** (the literature's
`0 ≤ df(G_∅) ≤ d₂(O_K^×)`), through `shafarevichKochBound_iff_deficiency`. -/
theorem deficiency_le_unitTwoRank_of_shafarevichKochBound {F : Type} [Field F] [NumberField F]
    {d r : ℕ} (hdr : d ≤ r) (h : ShafarevichKochBound F d r) : deficiency d r ≤ unitTwoRank F :=
  (shafarevichKochBound_iff_deficiency hdr).mp h

end Work.ClassFieldTower
