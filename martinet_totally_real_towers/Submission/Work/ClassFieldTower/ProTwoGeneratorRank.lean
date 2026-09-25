import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Main
import Submission.Work.ClassFieldTower.Tower
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo
import Submission.Work.ClassFieldTower.hasGenusLevel_witness
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.exists_maximalUnramifiedProP
import Submission.Work.ClassFieldTower.exists_unramifiedLevel_of_infinite

/-!
# `Work.ClassFieldTower.ProTwoGeneratorRank` -- the generator half, unconditionally

The assignment for this chapter asks for the two arithmetic invariants of `G_∅` for an explicit
imaginary quadratic field,

* `d(G_∅) = rank₂ Cl(F)` (class field theory), and
* `r - d ≤ d₂(O_F^×) = 1` (the Shafarevich--Koch deficiency bound),

and says: if the full Artin correspondence is out of reach, at least get the direction
`dim_{F₂}(G_∅/Φ(G_∅)) = rank₂ Cl(F)`, i.e. the *numerical certificate* that `G_∅` has at least
`5` generators.

**This module establishes exactly that, with no class field theory at all**, for the explicit
field `Kc = ℚ(√-30030)` (`WitnessField.lean`):

* `hasFiveIndependentUnramifiedQuadratics_of_genusLevel`: for ANY number field `F` with a genus
  level (`HasGenusLevel F`, i.e. an unramified Galois extension of degree `2^5` with exponent-`2`
  Galois group), any maximal unramified pro-`2` extension `M = F_∅` of `F` carries a surjection
  `G_∅ ↠ (𝔽₂)^5`;
* `exists_hasFiveIndependentUnramifiedQuadratics_witness`: for `Kc` such an `M` EXISTS
  (unconditional: `exists_maximalUnramifiedProP` + `hasGenusLevel_witness`);
* `exists_surjective_galoisGroup_zmodTwo_five_witness`: the same in explicit surjection form;
* `exists_unramifiedLevel_rootDiscr_genusLevel_witness`: unconditionally, `Kc` has a finite
  unramified Galois extension of degree `2^5 = 32` with constant root discriminant
  `rootDiscr Kc` -- the first (and, without the Shafarevich--Koch bound, only available) level of
  the Hilbert `2`-class field tower.

The argument is the classical genus-theory one and uses neither the Artin map nor any relation
count: the genus field `wM = ℚ(√8,√-3,√5,√-7,√-11,√13)` of `Kc` is an unramified exponent-`2`
extension of degree `32` (`hasGenusLevel_witness`); by the universal property of `F_∅` it embeds
into `F_∅`, so restriction of automorphisms exhibits `Gal(wM/Kc) ≅ (𝔽₂)^5` as a quotient of
`G_∅` (`exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo`).

**What is NOT here.** The relation half, `r ≤ d + 1`, is the Shafarevich--Koch deficiency bound
and needs global class field theory; it is isolated as the single wall
`Work.ClassFieldTower.ProTwoShafarevichKochInput Kc` (`ProTwoGenus.lean`, see also `Wall.lean`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-! ## 1. The generator half from a genus level (any number field) -/

/-- **A genus level gives five independent unramified quadratic extensions.**

If `F` has an unramified Galois extension `L/F` of degree `2^5` with exponent-`2` Galois group
(`HasGenusLevel F`), then `L` is a finite unramified pro-`2` extension of `F`, so by the
universal property of the maximal unramified pro-`2` extension `M = F_∅` it embeds into `M.K`
and the restriction map `G_∅ = Gal(M.K/F) →* Gal(L/F)` is surjective; composing with
`Gal(L/F) ≅ (𝔽₂)^5` gives a surjection `G_∅ ↠ (𝔽₂)^5`.

Equivalently: `dim_{F₂}(G_∅/Φ(G_∅)) ≥ 5`, i.e. `G_∅` needs at least five generators -- the
numerical certificate of the Golod--Shafarevich input, with no class field theory. -/
theorem hasFiveIndependentUnramifiedQuadratics_of_genusLevel {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) (h : HasGenusLevel F) :
    HasFiveIndependentUnramifiedQuadratics M := by
  classical
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hunr, hexp, hcard⟩ := h
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  letI : IsGalois F L := hgal
  exact exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo M L hunr hexp hcard

/-! ## 2. The generator half for `Kc = ℚ(√-30030)`, unconditionally -/

/-- **There exists a maximal unramified pro-`2` extension of `Kc` with `G_∅ ↠ (𝔽₂)^5`.**

Unconditional: the genus level of `Kc` is `hasGenusLevel_witness`, and a maximal unramified
pro-`2` extension of `Kc` exists by `exists_maximalUnramifiedProP`. -/
theorem exists_hasFiveIndependentUnramifiedQuadratics_witness :
    ∃ M : MaximalUnramifiedProP.{0} Kc 2, HasFiveIndependentUnramifiedQuadratics M := by
  classical
  obtain ⟨M⟩ := exists_maximalUnramifiedProP Kc 2
  exact ⟨M, hasFiveIndependentUnramifiedQuadratics_of_genusLevel M hasGenusLevel_witness⟩

/-- **Five independent unramified quadratic extensions of `Kc`, in surjection form.**

For the concrete imaginary quadratic field `Kc = ℚ(√-30030)` and ANY maximal unramified pro-`2`
extension `F_∅` of `Kc`, the Galois group `G_∅` has a surjection onto `(𝔽₂)^5`; in particular
`G_∅` has at least `5` generators.  This is the CFT-free numerical certificate `d(G_∅) ≥ 5`
(and, on the class-group side, `rank₂ Cl(Kc) ≥ 5`,
`Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five`, proved
independently and unconditionally in this chapter). -/
theorem exists_surjective_galoisGroup_zmodTwo_five_witness
    (M : MaximalUnramifiedProP.{0} Kc 2) :
    ∃ φ : galoisGroup M →* (Fin 5 → Multiplicative (ZMod 2)), Function.Surjective φ :=
  hasFiveIndependentUnramifiedQuadratics_of_genusLevel M hasGenusLevel_witness

/-! ## 3. The first level of the tower, unconditionally -/

/-- **An unramified degree-`2^5` extension of `Kc` with constant root discriminant.**

Unconditional consequence of the genus level: `Kc` has a finite Galois extension `L` with
`differentIdeal (𝓞 Kc) (𝓞 L) = ⊤`, `[L : Kc] = 2^5 = 32` and `rootDiscr L = rootDiscr Kc`.

This is the genus-theory part of the deliverable's item 3 ("for every `N` a finite unramified
`L/Kc` with `[L : Kc] ≥ N` and constant root discriminant"): the case `N ≤ 32` is
unconditional, and the general case is exactly the infinite tower, needing the
Shafarevich--Koch input (`Wall.lean`). -/
theorem exists_unramifiedLevel_rootDiscr_genusLevel_witness :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      Module.finrank Kc L = 2 ^ 5 ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc := by
  classical
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hunr, hexp, hcard⟩ := hasGenusLevel_witness
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra Kc L := iAL
  letI : FiniteDimensional Kc L := hfd
  letI : IsGalois Kc L := hgal
  refine ⟨L, iL, iNL, iAL, hfd, hgal, ?_, hunr, rootDiscr_eq_of_differentIdeal_eq_top hunr⟩
  rw [← IsGalois.card_aut_eq_finrank Kc L]
  exact hcard

end Work.ClassFieldTower
