/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.HassePrinciple` — the Hasse principle for `H²(·, Z/p)`

Umbrella module of the `HassePrinciple` chapter: `import Submission.NK.HassePrinciple.All`.
See `Submission/Work/HassePrinciple/README.md` for the full account, including the sense in which
`NK.BrauerHasse.Sha2Vanishing` is and is not proved here.

## The headline for the requester

**THE DELIVERABLE — the theorem to call.**  `Submission/Work/HassePrinciple/Deliverable.lean`
(namespace `NK.HassePrinciple`) is the module written for the requester.  The single theorem:

```
NK.HassePrinciple.hassePrinciple_of_localH2Input
    (hLoc : NK.BrauerHasse.LocalH2Input p K K' κ κ')   -- owed by NK.LocalCFT
    (h    : NK.HassePrinciple.RankInput p K K' κ κ')   -- the chapter's one arithmetic input
    (H : Subgroup Gal(K'/K)) (hH : IsClosed H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0
```

i.e. under the local Brauer input together with one arithmetic input, every non-zero class of
`H²(H, Z/p)` (for `H ≤ Gal(K'/K)` closed, `H ≅ Gal(κ'/κ)`) has a non-zero local component at some
place of `K'` over a finite prime of `K`.  The bundle form is
`NK.HassePrinciple.exists_loc_ne_zero_of_consumerHypotheses` (with
`NK.HassePrinciple.ConsumerHypotheses`), and the endgame (Neukirch's criterion) is
`NK.HassePrinciple.neukirchCriterion_of_localH2Input`.

**The literal request cannot be met, and the two reasons are theorems of this chapter, not
excuses.**

1. **`NK.BrauerHasse.Sha2Vanishing p K K' κ κ'` is false as literally stated** — its hypotheses
   do not require `κ` to be `p`-adic.  Formally:
   `NK.HassePrinciple.not_sha2Vanishing_of_archimedeanDefect` /
   `NK.HassePrinciple.not_archimedeanDefect_of_sha2Vanishing` prove
   `ArchimedeanDefect E E' ↔ ¬ Sha2Vanishing 2 E E' E E'`, and classically the archimedean defect
   exists for every formally real `E` (the quaternion class `(-1,-1)` over `ℚ(√2)`: invariants `1/2`
   at the two real places, `0` at every finite place).  The κ-labelling is what removes it (a
   `p`-adic `Gal(κ'/κ)` is `2`-torsion-free): `NK.HassePrinciple.NoTwoTorsion`,
   `NK.HassePrinciple.noTwoTorsion_of_mulEquiv`.  README §13.1, §19.
2. **Modulo the local inputs, the target is *equivalent* to Neukirch's Theorem 1** — the core
   theorem of the paper: `NK.HassePrinciple.sha2Vanishing_iff_localCharacterisation`.  Hence no
   statement "about cyclic extensions of number fields and their norm groups" can imply it, and in
   particular the licensed cyclic input cannot: this is *proved* by
   `NK.HassePrinciple.le_stabSubgroup_iff_localInclHom_surjective` and
   `NK.HassePrinciple.iInf_sup_fixingSubgroup_eq_stabSubgroup`
   (`⋂_L D_A·Gal(K'/L) = D_A`), i.e. the level-wise local groups coincide with the global level
   groups cofinally if and only if `U` is already (contained in) a decomposition group.  README
   §14.6, §16.3, §17.

**What the licensed cyclic input *does* yield**: the finite-case Hasse–Brauer–Noether theorem
`NK.HassePrinciple.hbnUnits_of_cyclicInput` (Milne CFT VII.7.1, for all finite Galois extensions
of number fields) and the field axiom of the on-disk global class field theory
(`NK.HassePrinciple.fieldAxiom_of_cyclicHasseInput`).

**What the target is proved from** (each reduction proved; see the table in
`Deliverable.lean`): Neukirch's input `NK.HassePrinciple.RankInput` — under the canonical name
**`NK.HassePrinciple.sha2Vanishing`** (also `sha2Vanishing_of_rankInput`), its product form `NK.HassePrinciple.SurjInput`
(`rankInput_of_surjInput`), the localisation-to-local-groups form `NK.HassePrinciple.NSWSInput`
(`sha2Vanishing_of_nswsInput`, the form the sibling chapters carry as
`NK.HasseTwist.NeukirchH2modifiedsurj` / `NK.LocalDecomposition.IndecomposedPrime`), the
cohomology-free `NK.HassePrinciple.IndexInput` (`sha2Vanishing_of_indexInput`), the
κ-labelled limit form `NK.HassePrinciple.LimitPassage` (`sha2Vanishing_of_limitPassage`), and
Neukirch's local characterisation itself (`sha2Vanishing_of_localCharacterisation`, unconditional).

**The composition with the consumer's own chapter.**  `NK.LocalDecomposition` delivers
`NK.BrauerHasse.LocalDecompositionCriterion` under the self-normalising hypothesis; the chapter's
glue `NK.HassePrinciple.sha2Vanishing_of_localDecomposition` (`Deliverable.lean`) turns *that*,
together with the local Brauer input and Neukirch's (9.2.1) in the `NSWSInput` form, into the
target — the licence amendment in the exact shape of the consumer's code
(`NK.HassePrinciple.SelfNormalisingLabeled` is the self-normalising hypothesis, and
`NK.HassePrinciple.LocalCharacterisationSN` its characterisation-specialisation; the consumer
corollary is `NK.HassePrinciple.hassePrinciple_of_localDecomposition`).

## Main results

**THE PRIMARY INTERFACE (README §18).**  `NK.HassePrinciple.NSWSInput`
(`LocalGroupInputDefs.lean`) — Neukirch's **(9.2.1)** (the *surjectivity* of the localisation to the
local groups `U ⊓ D_A` over a prime `𝔭`, NSW (9.2.1), the same input that the sibling chapters carry
as `NK.HasseTwist.NeukirchH2modifiedsurj` and `NK.LocalDecomposition.IndecomposedPrime`)
together with the local computations of local class field theory — with the proved reductions

* `NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective` — the **rank count** of
  Neukirch's proof: the surjectivity forces all the local groups over `𝔭` to coincide;
* `NK.HassePrinciple.rankInput_of_nswsInput` — `NSWSInput → RankInput`;
* `NK.HassePrinciple.sha2Vanishing_of_nswsInput` — `NSWSInput → Sha2Vanishing`, **the target of
  the chapter**;
* `NK.HassePrinciple.nswsInput_of_le_stabSubgroup` — **satisfiability** of the input: it holds
  whenever each labelled `U` is contained in the decomposition group of every place over some prime
  (the configuration of Neukirch's theorem);
* `NK.HassePrinciple.localCharacterisation_of_nswsInput` and, in `NSWSConsumer.lean`,
  `NK.HassePrinciple.exists_loc_ne_zero_of_nswsInput_and_localH2Input` (the corollary in the
  vocabulary of the Neukirch–Uchida development: under the local Brauer input and (9.2.1), every
  non-zero class has a non-zero local component) and
  `NK.HassePrinciple.exists_decompositionGroup_of_nswsInput` (Neukirch's criterion with the
  Hasse-principle hypothesis discharged), bundled as `NK.HassePrinciple.ConsumerInputNSW`.

**THE HEADLINE OF §19.**  `NK.HassePrinciple.ArchimedeanDefect` (`ArchimedeanDefect.lean`) is the
non-zero locally-finite-trivial class over `E` that makes the *literal* statement
`NK.BrauerHasse.Sha2Vanishing 2 E E' E E'` false:
`NK.HassePrinciple.not_sha2Vanishing_of_archimedeanDefect` and its converse
`NK.HassePrinciple.not_archimedeanDefect_of_sha2Vanishing`.  The classical *existence* of such a
class over a formally real number field (the quaternion algebra `(-1,-1)`) is the ingredient that is
not in the library; README §19.

**THE HEADLINE OF §§17–18.**  `NK.HassePrinciple.sha2Vanishing_iff_localCharacterisation`
(`LocalCharacterisation.lean`) proves that, modulo the local Brauer input
`NK.BrauerHasse.LocalH2Input` and the local finishing step
`NK.BrauerHasse.LocalDecompositionCriterion`, the target is *equivalent* to Neukirch's local
characterisation of the decomposition groups (`NK.HassePrinciple.LocalCharacterisation`,
Neukirch, Invent. Math. **6** (1969), Theorem 1 = NSW (12.1.9)) — i.e. to the core theorem of the
paper.  Consequently the target can be neither deduced from the licensed cyclic input (§14.6,
§17.3) nor stated with an input "about cyclic extensions and their norm groups" (§17.1).


**The interface to use.**  For a caller in the Neukirch–Uchida development:
`Submission/Work/HassePrinciple/Deliverable.lean`
(`NK.HassePrinciple.hassePrinciple_of_localH2Input`,
`NK.HassePrinciple.hassePrinciple_of_localH2Input_of_nswsInput`,
`NK.HassePrinciple.hassePrinciple_of_localH2Input_of_surjInput`,
`NK.HassePrinciple.hassePrinciple_of_localH2Input_of_indexInput`,
`NK.HassePrinciple.exists_loc_ne_zero_of_localH2Input_and_localCharacterisation`,
`NK.HassePrinciple.neukirchCriterion_of_localH2Input`,
`NK.HassePrinciple.hassePrinciple_of_consumerHypotheses`) and, one level down, the canonical names
in `Main.lean` (`NK.HassePrinciple.exists_loc_ne_zero_of_localH2Input`,
`NK.HassePrinciple.exists_loc_ne_zero`, `NK.HassePrinciple.exists_decompositionGroup_of_localGalois`,
`NK.HassePrinciple.ConsumerHypotheses`) — all of which take the chapter's amended input
(`RankInput` / `NSWSInput` / `SurjInput` / `IndexInput` / `LocalCharacterisation`), **not** the
legacy level-wise `NK.HassePrinciple.Sha2Input`.

The inputs of `RankInput` are a *surjectivity* statement (Neukirch's `eq:NeukirchH2modifiedsurj`,
NSW (9.2.1)) together with the local computations of local class field theory: **the Hasse
principle itself is not assumed**.  Its product form is `NK.HassePrinciple.SurjInput` and the
derivation is `NK.HassePrinciple.rankInput_of_surjInput`; the version in which the product is
taken over the *local groups* (which is the form in which (9.2.1) can be true, the product over the
places of `K'` being infinite) is `NK.HassePrinciple.NSWSInput`.  The bundled corrected
specification is `NK.HassePrinciple.Sha2Spec` (`Spec.lean`) with
`NK.HassePrinciple.sha2Vanishing_of_spec`; its two fields are the archimedean condition and
`RankInput`, and **it has no `cyclic` field** — the licensed cyclic input plays no role in the
reduction and is consumed by `hbnUnits_from_cyclicInput` and `fieldAxiom_of_cyclicHasseInput`
(README §22).  The cohomology-free input is `NK.HassePrinciple.IndexInput` (`IndexInput.lean`): a
place whose local degree inside `U` is prime to `p` at every finite level, with the reduction
`sha2Vanishing_of_indexInput` and the satisfiability `indexInput_of_inert` (it is implied by
`∃A, U ≤ D_A`).  The legacy level-wise input `NK.HassePrinciple.Sha2Input` (`Inputs.lean`) and
the statements carrying it (`Main.lean`, names of the form `..._of_sha2Input`) are kept for the
record only, as is the κ-labelled `NK.HassePrinciple.LimitPassage` (the classical *injectivity*
route, with `sha2Vanishing_of_limitPassage` and the coherence
`limitPassage_of_rankInput` proved).  `NK.BrauerHasse.Sha2Vanishing` is false as literally stated
and the corrected target carries the archimedean condition — see §13.1 and README §14.

**Read `Submission/Work/HassePrinciple/README.md` §13 first**: it records that the requested target
`NK.BrauerHasse.Sha2Vanishing p K K' κ κ'` is *false* as a universally quantified statement (its
hypotheses do not require `κ` to be `p`-adic; the quaternion class of `ℚ(√2)` at `p = 2` is a
counterexample, README §13.1), states the corrected form, and gives the authoritative status of
every step of the reduction to the licensed cyclic input.

### The corrected statement and its inputs

* `NK.HassePrinciple.CyclicHasseInput` (`CyclicBase.lean`) — the **licensed** input: the Hasse
  norm result for cyclic extensions of number fields (index and norm form) together with the
  Herbrand quotient of the idèle class group for cyclic extensions;
* `NK.HassePrinciple.NoTwoTorsion` and `NK.HassePrinciple.Sha2Spec` (`Spec.lean`) — the
  corrected input structure of the Hasse principle, with two fields and **no unused field**: the
  archimedean condition on the labelling field `κ` (necessary, and true for `p`-adic `κ`;
  consumed by `NK.HassePrinciple.Sha2Spec.noTwoTorsion` and
  `NK.HassePrinciple.Sha2Spec.hp`/`exists_decompositionGroup_of_spec`) and Neukirch's rank count
  `Sha2Spec.rank : RankInput` (the operative field; see README §14 and §22).  There is **no
  `cyclic` field**: the licensed cyclic input cannot enter the reduction (proved, README §17);
* `NK.HassePrinciple.sha2Vanishing_of_spec` (`Spec.lean`) — `Sha2Spec → Sha2Vanishing`, proved as
  `sha2Vanishing_of_rankInput h.rank`; `NK.HassePrinciple.Sha2Spec.rank` is Neukirch's input
  `NK.HassePrinciple.RankInput` (`RankInput.lean`), whose fields are `hp`, `card_global` (local
  class field theory at `κ`) and `rank` (Neukirch's surjectivity at a place + the order comparison
  at the local group); **no Hasse-principle hypothesis is used by the reduction**;
* `NK.HassePrinciple.exists_loc_ne_zero_of_spec` (`Spec.lean`) — the corollary in the vocabulary
  of the Neukirch–Uchida development: a non-zero class has a non-zero local component at some place
  over a finite prime.

### Hasse–Brauer–Noether from the cyclic input (the substance of this stretch)

* `NK.HassePrinciple.hbnUnits_of_cyclicInput` / `hbnUnits_from_cyclicInput`
  (`HBNUnits_from_cyclic.lean`) — **the relative Hasse–Brauer–Noether result**
  `NK.HassePrinciple.HBNUnits K L`: `H²(Gal(L/K), Lˣ) → ∏_w H²(Γ_w, L_wˣ)` has trivial kernel,
  derived from the licensed cyclic input (Milne, *CFT*, VII.7.1);
* `NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all`
  (`subsingleton_groupCohomology_one_ideleClassGroup_all.lean`) — the classical second inequality,
  `H¹(Γ, C_E) = 0` for **every** finite Galois extension of number fields, from the licensed cyclic
  input;
* `NK.HassePrinciple.subsingleton_classGroupRep_one` — the same in the coefficient ring
  `CoeffInt = ULift ℤ`;
* `NK.HassePrinciple.hbnIdele` — Shapiro's result for the idèles:
  `H²(Γ, 𝕀_L) → ∏_w H²(Γ_w, L_wˣ)` has trivial kernel;
* `NK.HassePrinciple.locUnits_compatible`, `NK.HassePrinciple.HBNUnits`,
  `NK.HassePrinciple.HBNIdele`, `NK.HassePrinciple.LocUnitsCompatible` and the coefficient layer
  `localUnitsEquiv`, `localUnitsRep`, `unitsToLocalUnits`, `locUnits`, `ideleToLocalUnits`,
  `ideleLoc`, `unitsToIdeleH2` (`LocalUnits.lean`) — the localisation of `H²(Γ, Lˣ)` at a place.

### The earlier layer (levels, columns, local–global criteria)


* **Do not use this one.**  `NK.HassePrinciple.sha2Vanishing_of_sha2Input` (`Inputs.lean`) — the
  Hasse principle
  `NK.BrauerHasse.Sha2Vanishing` proved from the inputs `NK.HassePrinciple.Sha2Input`
  (the licensed Hasse norm theorem, its `p`-primary cohomological form at the finite levels, and the
  exhaustion of the kernel of the localisation by the finite levels);
* `NK.HassePrinciple.sha2Vanishing_iff_levelForm` (`Defs.lean`) — `Sha2Vanishing` is equivalent
  to its level-wise form `NK.HassePrinciple.LevelForm`;
* `NK.HassePrinciple.obstruction_trivial_of_pgroup`
  (`obstruction_trivial_of_pgroup.lean`) — the Sylow reduction: only the `p`-primary levels are
  needed for the level-wise Hasse principle;
* `NK.HassePrinciple.levelForm_of_pgroupLevel` (`levelForm_of_pgroupLevel.lean`) — the Sylow
  reduction in the colimit form, and `NK.HassePrinciple.levelForm_of_sha2Input`,
  `NK.HassePrinciple.level_kernel_dies_of_obstructionTrivial` — the reduction chain;
* `NK.HassePrinciple.loc_injective_of_le_stabSubgroup`
  (`loc_injective_of_le_stabSubgroup.lean`) — an unconditional instance: the localisation at a place
  whose decomposition group contains `U` is injective;
* `NK.HassePrinciple.sha2Vanishing_of_inert` (`Inert.lean`) — the Hasse principle holds as soon as
  every relevant subgroup lies in the decomposition group of some place;
* `NK.HassePrinciple.obstruction_trivial_of_coprime_index`,
  `NK.HassePrinciple.obstruction_trivial_of_bijective_localInclHom`,
  `NK.HassePrinciple.obstruction_trivial_of_le_stabSubgroup` (`LevelHasse.lean`) — the level-wise
  Hasse principle, proved unconditionally at levels with a place of prime-to-`p` local index;
* `NK.HassePrinciple.exists_loc_ne_zero`, `NK.HassePrinciple.exists_nonzero_class_with_loc_ne_zero`,
  `NK.HassePrinciple.exists_loc_ne_zero_of_localH2Input`,
  `NK.HassePrinciple.exists_loc_ne_zero_of_consumerHypotheses` (with the bundled interface
  `NK.HassePrinciple.ConsumerHypotheses`),
  `NK.HassePrinciple.exists_decompositionGroup_of_localGalois` and
  `NK.HassePrinciple.fieldAxiom_of_sha2Input` (`Main.lean`) — the corollaries in the vocabulary of
  the Neukirch–Uchida development;
* `NK.HassePrinciple.HasseNormTheorem` (`Norm.lean`) — the Hasse norm theorem for cyclic
  extensions of number fields, as a named input;
* `NK.HassePrinciple.H2_map_injective_of_coprime_index` — restriction on `H²(·, Z/p)` is injective
  for subgroups of prime-to-`p` index;
* `NK.HassePrinciple.levelGroupMulEquivLevelGalois` and
  `NK.HassePrinciple.levelGroupMulEquivFixingSubgroup` (`LevelDictionary.lean`, item 3 of the
  README's §8.4) — **the level dictionary**: the level group `LevelGroup V L` is the Galois group of
  the finite extension `L/(L ⊓ K'^V)` of number fields; together with
  `NK.HassePrinciple.sup_fixingSubgroup_eq_fixingSubgroup_inf` (the base field of the level
  extension) and `NK.HassePrinciple.natCard_levelGroup` (its degree);
* `NK.HassePrinciple.ArithmeticLevelHasse` and
  `NK.HassePrinciple.obstruction_trivial_of_arithmeticLevelHasse` (`ArithmeticForm.lean`) — the
  level-wise Hasse principle restated in the arithmetic vocabulary (finite Galois groups
  `V.map (levelRestrict L) ≤ Gal(L/K)` and the restrictions to the subgroups
  `(V ⊓ D_A).map (levelRestrict L)` cut out by the decomposition subgroups), and the *proved*
  reduction from it to the `p`-primary level-wise Hasse principle of `Sha2Input`; the input
  structure `NK.HassePrinciple.Sha2InputArith` (`Inputs.lean`) packages it with the licensed Hasse
  norm theorem;
* `NK.HassePrinciple.unitsLevelRep`, `NK.HassePrinciple.UnitsLevelH2`,
  `NK.HassePrinciple.unitsInclLinearMap`, `NK.HassePrinciple.unitsIncl_smul`,
  `NK.HassePrinciple.unitsLevelMap`, `NK.HassePrinciple.unitsLevelMap_refl`,
  `NK.HassePrinciple.unitsLevelMap_comp`, `NK.HassePrinciple.unitsLevelSystem` and
  **`NK.HassePrinciple.H2Units`** (`UnitsLevel.lean`, `unitsIncl_smul.lean`,
  `exists_unitsLevelMapCoeff.lean`, `unitsLevelMap_refl.lean`, `unitsLevelMap_comp.lean`,
  `UnitsColimit.lean`) — **the units level system and its colimit**: the representation of the level
  group on `Lˣ`, its level cohomology `H²(LevelGroup U L, Lˣ)`, the unit inclusion as a morphism of
  `CoeffInt`-modules with its equivariance, the transition morphisms with their two coherence laws,
  and the colimit `H2Units V = colim_L H²(LevelGroup V L, Lˣ)` with the universal property of
  `NK.BrauerTwist.LevelSystem`; this is the target of the Kummer map of README §10.4;
* `NK.HassePrinciple.muLevelRep`, `NK.HassePrinciple.MuLevelH2`,
  `NK.HassePrinciple.muLevelInclLinearMap`, `NK.HassePrinciple.muLevelIncl_smul`,
  `NK.HassePrinciple.muLevelMap`, `NK.HassePrinciple.muLevelMap_refl`,
  `NK.HassePrinciple.muLevelMap_comp`, `NK.HassePrinciple.muLevelSystem`,
  `NK.HassePrinciple.MuColim`, `NK.HassePrinciple.muToUnits`,
  `NK.HassePrinciple.kummerLevel`, `NK.HassePrinciple.kummerLevel_naturality` and
  **`NK.HassePrinciple.kummerColim`** (`MuLevel.lean`, `MuLevelEquivariance.lean`,
  `exists_muLevelMapCoeff.lean`, `MuLevelMap.lean`, `muLevelMap_refl.lean`, `muLevelMap_comp.lean`,
  `KummerLevel.lean`, `kummerLevel_naturality.lean`, `MuColimit.lean`) — **the `μ_p` level system
  in this chapter's vocabulary, its colimit, and the Kummer map on the colimits**
  `kummerColim : MuColim p V → H2Units V`; the injectivity of this map is item 1 of README §8.4;
* `NK.HassePrinciple.exists_addCommGroup_H2Units`, `NK.HassePrinciple.exists_addCommGroup_MuColim`
  (delegated, proved) — the **additive structure on the two colimits** `H2Units V` and `MuColim p V`,
  with `ofLevel` additive on each level (`LevelSystem.Colim` is a bare type, so this has to be built
  by descent from the level-wise additions; it is the prerequisite for stating the injectivity of
  `kummerColim`).  A named `instance` plus a `@[simp]` additivity lemma are the intended byproduct;
* `NK.HassePrinciple.levelInclHom_injective`, `NK.HassePrinciple.levelInclHom_locLevel_apply`,
  `NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow` — the auxiliary lemmas of the Sylow
  reduction.
-/

import Submission.NK.HassePrinciple.Defs
import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.HassePrinciple.Norm
import Submission.NK.HassePrinciple.loc_injective_of_le_stabSubgroup
import Submission.NK.HassePrinciple.Inert
import Submission.NK.HassePrinciple.LevelHasse
import Submission.NK.HassePrinciple.levelInclHom_injective
import Submission.NK.HassePrinciple.levelInclHom_mem_levelObstruction
import Submission.NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow
import Submission.NK.HassePrinciple.obstruction_trivial_of_pgroup
import Submission.NK.HassePrinciple.obstruction_trivial_of_pgroup_rel
import Submission.NK.HassePrinciple.levelForm_of_pgroupLevel
import Submission.NK.HassePrinciple.Inputs
import Submission.NK.HassePrinciple.Main
import Submission.NK.HassePrinciple.exists_add_local
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.HassePrinciple.levelLocVanishing_mono
import Submission.NK.HassePrinciple.exists_finset_levelObstruction
import Submission.NK.HassePrinciple.subsingleton_tateCohomology_one_of_cyclic
import Submission.NK.HassePrinciple.Mu
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.HassePrinciple.ArithmeticForm
import Submission.NK.HassePrinciple.levelH2MulEquiv
import Submission.NK.HassePrinciple.natCard_levelGroup
import Submission.NK.HassePrinciple.localInclHom_eq_restriction
import Submission.NK.HassePrinciple.kummerMap_injective_of_pdivisible
import Submission.NK.HassePrinciple.kummerMap_range_eq_pTorsion
import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.unitsIncl_smul
import Submission.NK.HassePrinciple.exists_unitsLevelMapCoeff
import Submission.NK.HassePrinciple.unitsLevelMap_refl
import Submission.NK.HassePrinciple.unitsLevelMap_comp
import Submission.NK.HassePrinciple.UnitsColimit
import Submission.NK.HassePrinciple.MuLevel
import Submission.NK.HassePrinciple.MuLevelEquivariance
import Submission.NK.HassePrinciple.exists_muLevelMapCoeff
import Submission.NK.HassePrinciple.MuLevelMap
import Submission.NK.HassePrinciple.muLevelMap_refl
import Submission.NK.HassePrinciple.muLevelMap_comp
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.kummerLevel_naturality
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.exists_addCommGroup_H2Units
import Submission.NK.HassePrinciple.exists_addCommGroup_MuColim
import Submission.NK.HassePrinciple.hilbert90_levelGroup
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NK.HassePrinciple.exists_normal_subgroup_index_eq_prime
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField
import Submission.NK.HassePrinciple.ideleClassGroupH1Pgroup
import Submission.NK.HassePrinciple.IdelesLevel
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_ideleRep
import Submission.NK.HassePrinciple.injective_h2_units_of_subsingleton_h1_classGroupRep
import Submission.NK.HassePrinciple.CyclicBase
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
import Submission.NK.HassePrinciple.locUnits_compatible
import Submission.NK.HassePrinciple.hbnIdele
import Submission.NK.HassePrinciple.HBNUnits_from_cyclic
import Submission.NK.HassePrinciple.CoeffTransfer
import Submission.NK.HassePrinciple.Spec
import Submission.NK.HassePrinciple.RankInput
import Submission.NK.HassePrinciple.IndexInput
import Submission.NK.HassePrinciple.iInf_sup_fixingSubgroup_eq_stabSubgroup
import Submission.NK.HassePrinciple.LevelCoincidence
import Submission.NK.HassePrinciple.le_stabSubgroup_iff_localInclHom_surjective
import Submission.NK.HassePrinciple.rankInput_of_inert_of_card
import Submission.NK.HassePrinciple.locAt_bijective_of_le_stabSubgroup
import Submission.NK.HassePrinciple.IdelesColimit
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.HassePrinciple.idelePush
import Submission.NK.HassePrinciple.HBNIdeleProof
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.IdeleCocycleLocal
import Submission.NK.HassePrinciple.IdeleLevel
import Submission.NK.HassePrinciple.IdeleLevelGlue
import Submission.NK.HassePrinciple.IdeleOrbit
import Submission.NK.HassePrinciple.IdeleOrbitCoind
import Submission.NK.HassePrinciple.LocalUnitsSub
import Submission.NK.HassePrinciple.MuColimAdd
import Submission.NK.HassePrinciple.OrbitCoindSection
import Submission.NK.HassePrinciple.RepOfMonoidHom
import Submission.NK.HassePrinciple.exists_fixed_uniformizer_localAutHom
import Submission.NK.HassePrinciple.exists_idele_coboundary_of_isMulCocycle
import Submission.NK.HassePrinciple.exists_level_of_h2
import Submission.NK.HassePrinciple.exists_mem_localUnits_div_of_forall_eq_div
import Submission.NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
import Submission.NK.HassePrinciple.localUnits_h2_injective
import Submission.NK.HassePrinciple.LocalCharacterisation
import Submission.NK.HassePrinciple.LocalGroupInputDefs
import Submission.NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective
import Submission.NK.HassePrinciple.LocalGroupInput
import Submission.NK.HassePrinciple.NSWSConsumer
import Submission.NK.HassePrinciple.Deliverable
import Submission.NK.HassePrinciple.sha2Vanishing_congr_labelling
import Submission.NK.HassePrinciple.nswsInput_of_le_stabSubgroup
import Submission.NK.HassePrinciple.ArchimedeanDefect
import Submission.NK.HassePrinciple.muColimNeg_add_cancel
import Submission.NK.HassePrinciple.muJoinAdd_assoc
import Submission.NK.HassePrinciple.muJoinAdd_comm
import Submission.NK.HassePrinciple.muJoinAdd_zero_left
import Submission.NK.HassePrinciple.muJoinAdd_zero_right
import Submission.NK.HassePrinciple.orbitCoindMapA_split
import Submission.NK.HassePrinciple.orbitCoindMapU_split
import Submission.NK.HassePrinciple.outsideUnitsLift_split
import Submission.NK.HassePrinciple.supportedLift_split
import Submission.NK.HassePrinciple.OfLevelZero
import Submission.NK.HassePrinciple.Placement
import Submission.NK.HassePrinciple.map_levelRestrict_stabSubgroup
