/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The level-wise Hasse principle in the arithmetic form

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 3).

`NK.HassePrinciple.Sha2Input.pgroup_level` (the labelled, strong, `p`-primary level-wise Hasse
principle) is a statement about the profinite cohomology `NK.BrauerHasse.LevelH2 p V L` of the
level group `NK.BrauerHasse.LevelGroup V L = V ⧸ (V ⊓ Gal(K'/L))` and the level-wise
localisations `NK.BrauerHasse.locLevel`.  Thanks to
`Submission/Work/HassePrinciple/LevelDictionary.lean` (item 3 of README §8.4) the same statement can
be written in the arithmetic vocabulary:

* the level group is the image `V.map (levelRestrict L) ≤ Gal(L/K)` of `V` under the restriction
  `Gal(K'/K) →* Gal(L/K)`, i.e. the Galois group of the finite extension `L/(L ⊓ K'^V)` of number
  fields (`levelGroupMulEquivLevelGalois`);
* the local level group is the image `(V ⊓ D_A).map (levelRestrict L)` of the intersection with
  the decomposition subgroup `D_A` of the place `A`;
* under these identifications the level-wise localisation `locLevel` is *literally* the restriction
  `H²(Γ, Z/p) → H²(Γ_A, Z/p)` along the inclusion `Γ_A ≤ Γ` (`localInclHom_comm`).

This module performs the translation and states the *arithmetic form* of the input
(`NK.HassePrinciple.ArithmeticLevelHasse`), together with the (proved) reduction

`NK.HassePrinciple.obstruction_trivial_of_arithmeticLevelHasse :

  ArithmeticLevelHasse p K K' κ κ' → (the p-primary level-wise Hasse principle of `Sha2Input`)`,

so that the open number-theoretic content of the chapter is visible as a statement about finite
Galois groups of number fields and their decomposition subgroups.

## Main definitions and results

* `NK.HassePrinciple.levelGroupEquivRange` — the level group as the range of the restriction map,
  `LevelGroup V L ≃* ↥(V.map (levelRestrict L))`;
* `NK.HassePrinciple.localLevelGroupEquivRange` — the same for the local level group;
* `NK.HassePrinciple.localInclHom_comm` — the localisation is the restriction along
  `Γ_A ≤ Γ`;
* `NK.HassePrinciple.isPGroup_levelGroup_iff` — the `p`-primary hypothesis in arithmetic form;
* `NK.HassePrinciple.ArithmeticLevelHasse` — the arithmetic form of the labelled, strong,
  `p`-primary level-wise Hasse principle;
* `NK.HassePrinciple.obstruction_trivial_of_arithmeticLevelHasse` — the reduction.
-/

import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.HassePrinciple.Obstruction

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The computation rule for Noether's first isomorphism theorem -/

/-- The canonical isomorphism `G ⧸ ker φ ≃* φ.range` of Noether's first isomorphism theorem sends
the class of `x` to `φ x`. -/
lemma quotientKerEquivRange_mk_val {G H : Type*} [Group G] [Group H] (φ : G →* H) (x : G) :
    ((QuotientGroup.quotientKerEquivRange φ) (QuotientGroup.mk x) : H) = φ x := by
  simp only [QuotientGroup.quotientKerEquivRange, MulEquiv.ofBijective_apply,
    QuotientGroup.rangeKerLift, MonoidHom.rangeRestrict]
  rfl

/-! ## The level group as the range of the restriction map -/

/-- **The level group in the arithmetic picture**: the level group `V ⧸ (V ⊓ Gal(K'/L))` is the
range of the restriction map `V →* Gal(L/K)`, i.e. the subgroup `V.map (levelRestrict L)` of the
finite Galois group `Gal(L/K)`. -/
noncomputable def levelGroupEquivRange (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    LevelGroup V L ≃* ↥(V.map (levelRestrict L)) :=
  (QuotientGroup.quotientMulEquivOfEq (levelRestrictHom_ker V L).symm).trans
    ((QuotientGroup.quotientKerEquivRange (levelRestrictHom V L)).trans
      (MulEquiv.subgroupCongr (levelRestrictHom_range V L)))

/-- Computation rule for `levelGroupEquivRange`. -/
theorem levelGroupEquivRange_mk (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (x : ↥V) :
    (levelGroupEquivRange V L (QuotientGroup.mk x) : Gal(↥L/K)) =
      levelRestrict L (x : Gal(K'/K)) := by
  rw [levelGroupEquivRange]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivRange, MulEquiv.ofBijective_apply, QuotientGroup.rangeKerLift,
    MonoidHom.rangeRestrict, levelRestrictHom, levelRestrict]
  rfl

/-! ## The local level group -/

/-- The restriction map on `V ⊓ D_A` (the part of `V` cut out by the decomposition subgroup of a
place), whose range is the local level group in the arithmetic picture. -/
noncomputable abbrev localLevelRestrictFun (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') : ↥(V ⊓ stabSubgroup A) →* Gal(↥L/K) :=
  (levelRestrict L).comp (V ⊓ stabSubgroup A).subtype

/-- The kernel of the local restriction map. -/
theorem localLevelRestrictFun_ker (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    (localLevelRestrictFun V A L).ker = L.fixingSubgroup.subgroupOf (V ⊓ stabSubgroup A) := by
  ext x
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  change (x : Gal(K'/K)).restrictNormal (L : IntermediateField K K') = 1 ↔ _
  rw [AlgEquiv.restrictNormal_eq_one_iff]

/-- The range of the local restriction map. -/
theorem localLevelRestrictFun_range (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    (localLevelRestrictFun V A L).range = (V ⊓ stabSubgroup A).map (levelRestrict L) := by
  rw [localLevelRestrictFun, MonoidHom.range_comp, Subgroup.range_subtype]

/-- **The local level group in the arithmetic picture**: the image of `V ⊓ D_A` in `Gal(L/K)`. -/
noncomputable def localLevelGroupEquivRange (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    LocalLevelGroup V A L ≃* ↥((V ⊓ stabSubgroup A).map (levelRestrict L)) :=
  (QuotientGroup.quotientMulEquivOfEq (localLevelRestrictFun_ker V A L).symm).trans
    ((QuotientGroup.quotientKerEquivRange (localLevelRestrictFun V A L)).trans
      (MulEquiv.subgroupCongr (localLevelRestrictFun_range V A L)))

/-- Computation rule for `localLevelGroupEquivRange`. -/
theorem localLevelGroupEquivRange_mk (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') (x : ↥(V ⊓ stabSubgroup A)) :
    (localLevelGroupEquivRange V A L (QuotientGroup.mk x) : Gal(↥L/K)) =
      levelRestrict L (x : Gal(K'/K)) := by
  rw [localLevelGroupEquivRange]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivRange, MulEquiv.ofBijective_apply, QuotientGroup.rangeKerLift,
    MonoidHom.rangeRestrict, localLevelRestrictFun, levelRestrict]
  rfl

/-! ## The localisation is the restriction -/

/-- **The level-wise localisation is the restriction to the decomposition subgroup.**  Under the
arithmetic identifications of the level group (`levelGroupEquivRange`) and of the local level group
(`localLevelGroupEquivRange`), the map `localInclHom` — whose induced map on `H²` is the level-wise
localisation `locLevel` — is the inclusion of the subgroup `(V ⊓ D_A).map (levelRestrict L)` into
`V.map (levelRestrict L)`. -/
theorem localInclHom_comm (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') (x : LocalLevelGroup V A L) :
    levelGroupEquivRange V L (localInclHom V A L x) =
      Subgroup.inclusion (Subgroup.map_mono (f := levelRestrict L)
        (inf_le_left : V ⊓ stabSubgroup A ≤ V)) (localLevelGroupEquivRange V A L x) := by
  induction x using QuotientGroup.induction_on with
  | H y =>
      apply Subtype.ext
      rw [localInclHom, QuotientGroup.map_mk, levelGroupEquivRange_mk]
      simp only [Subgroup.coe_inclusion]
      rw [localLevelGroupEquivRange_mk]

/-- The same statement as an identity of monoid homomorphisms (the form in which it is used to
transport cohomology classes). -/
theorem localInclHom_eq_inclusion_comp (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    Subgroup.inclusion (Subgroup.map_mono (f := levelRestrict L)
        (inf_le_left : V ⊓ stabSubgroup A ≤ V)) =
      (levelGroupEquivRange V L).toMonoidHom.comp
        ((localInclHom V A L).comp (localLevelGroupEquivRange V A L).symm.toMonoidHom) := by
  refine MonoidHom.ext fun y => ?_
  apply Subtype.ext
  simp only [Subgroup.coe_inclusion, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [localInclHom_comm, MulEquiv.apply_symm_apply]
  exact (Subgroup.coe_inclusion _ y).symm

/-! ## The `p`-primary hypothesis in arithmetic form -/

/-- The `p`-primary hypothesis of the level-wise Hasse principle is a statement about the finite
Galois group of the level extension: the image of `V` in `Gal(L/K)` is a `p`-group. -/
theorem isPGroup_levelGroup_iff (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    IsPGroup p (LevelGroup V L) ↔ IsPGroup p ↥(V.map (levelRestrict L)) := by
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h ((levelGroupEquivRange V L).symm g)
    refine ⟨k, ?_⟩
    have h1 := congrArg (levelGroupEquivRange V L) hk
    rw [map_pow, map_one, MulEquiv.apply_symm_apply] at h1
    exact h1
  · intro h g
    obtain ⟨k, hk⟩ := h ((levelGroupEquivRange V L) g)
    refine ⟨k, ?_⟩
    have h1 := congrArg (levelGroupEquivRange V L).symm hk
    rw [map_pow, map_one, MulEquiv.symm_apply_apply] at h1
    exact h1

/-! ## The arithmetic form of the input, and the reduction -/

/-- **The level-wise Hasse principle at the `p`-primary levels, in arithmetic form.**  For every
closed `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, every `V ≤ U` and every finite Galois
intermediate field `L` of `K'/K` such that the image `Γ = V.map (levelRestrict L) ≤ Gal(L/K)` is a
`p`-group, a class of `H²(Γ, Z/p)` whose restriction to the subgroup
`Γ_A = (V ⊓ D_A).map (levelRestrict L)` vanishes for *every* place `A` of `K'` over a finite prime
of `K` is zero.

This is the same statement as `Sha2Input.pgroup_level`
(`obstruction_trivial_of_arithmeticLevelHasse`), written entirely in terms of the finite Galois
groups `Gal(L/K)` of the number-field extensions arising as levels: `Γ` is a finite group of the
arithmetic shape `V.map (levelRestrict L)`, the coefficients are the trivial `Z/p`, and the local
conditions are restrictions to the subgroups `Γ_A`. -/
def ArithmeticLevelHasse (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Nonempty (U ≃* Gal(κ'/κ)) →
    ∀ (V : Subgroup Gal(K'/K)), V ≤ U → ∀ (L : FiniteGaloisIntermediateField K K'),
      IsPGroup p ↥(V.map (levelRestrict L)) →
        ∀ a : H2 p ↥(V.map (levelRestrict L)),
          (∀ A : OverFinitePrime K K',
            H2.map (Subgroup.inclusion (Subgroup.map_mono (f := levelRestrict L)
              (inf_le_left : V ⊓ stabSubgroup A.1 ≤ V))) a = 0) →
          a = 0

section Reduction

variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
variable [NumberField K]

/-- Composition of the two inverse `H2`-maps of a group isomorphism is the identity. -/
lemma H2_map_symm_comp_self (p : ℕ) {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    H2.map (p := p) e.symm.toMonoidHom ≫ H2.map (p := p) e.toMonoidHom = 𝟙 (H2 p G) := by
  rw [← H2.map_comp]
  rw [H2.map_congr (show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from
    MonoidHom.ext fun x => e.symm_apply_apply x), H2.map_id]

/-- **The reduction**: the arithmetic form of the level-wise Hasse principle implies the
`p`-primary level-wise Hasse principle of `Sha2Input` (at all levels, for all labelled subgroups). -/
theorem obstruction_trivial_of_arithmeticLevelHasse (p : ℕ)
    (h : ArithmeticLevelHasse (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ (V : Subgroup Gal(K'/K)), V ≤ U →
        ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p V L),
          IsPGroup p (LevelGroup V L) → a ∈ levelObstruction p V L → a = 0 := by
  intro U hU hκ V _hVU L a hpg ha
  have hpg' : IsPGroup p ↥(V.map (levelRestrict L)) := (isPGroup_levelGroup_iff p V L).mp hpg
  have hloc : ∀ A : OverFinitePrime K K',
      (H2.map (p := p) (Subgroup.inclusion (Subgroup.map_mono (f := levelRestrict L)
        (inf_le_left : V ⊓ stabSubgroup A.1 ≤ V)))).hom
        ((H2.map (p := p) (levelGroupEquivRange V L).symm.toMonoidHom).hom a) = 0 := by
    intro A
    have hA : (H2.map (p := p) (localInclHom V A.1 L)).hom a = 0 := by
      have h := (mem_levelObstruction_iff p V L a).mp ha A
      simpa [locLevel] using h
    have key : H2.map (p := p) (Subgroup.inclusion (Subgroup.map_mono (f := levelRestrict L)
          (inf_le_left : V ⊓ stabSubgroup A.1 ≤ V))) =
        H2.map (p := p) (levelGroupEquivRange V L).toMonoidHom ≫
          (H2.map (p := p) (localInclHom V A.1 L) ≫
            H2.map (p := p) (localLevelGroupEquivRange V A.1 L).symm.toMonoidHom) := by
      rw [localInclHom_eq_inclusion_comp V A.1 L, H2.map_comp, H2.map_comp]
    have h1 : (H2.map (p := p) (levelGroupEquivRange V L).toMonoidHom).hom
        ((H2.map (p := p) (levelGroupEquivRange V L).symm.toMonoidHom).hom a) = a := by
      have h := congrArg (fun (φ : H2 p (LevelGroup V L) ⟶ H2 p (LevelGroup V L)) => φ.hom a)
        (H2_map_symm_comp_self (p := p) (levelGroupEquivRange V L))
      simpa using h
    rw [key]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [h1, hA, map_zero]
  have h0 := h U hU hκ V _hVU L hpg'
    (H2.map (p := p) (levelGroupEquivRange V L).symm.toMonoidHom a) hloc
  have h1 : (H2.map (p := p) (levelGroupEquivRange V L).toMonoidHom).hom
      ((H2.map (p := p) (levelGroupEquivRange V L).symm.toMonoidHom).hom a) = a := by
    have hh := congrArg (fun (φ : H2 p (LevelGroup V L) ⟶ H2 p (LevelGroup V L)) => φ.hom a)
      (H2_map_symm_comp_self (p := p) (levelGroupEquivRange V L))
    simpa using hh
  have h2 := congrArg (fun x => (H2.map (p := p) (levelGroupEquivRange V L).toMonoidHom).hom x) h0
  rw [map_zero, h1] at h2
  exact h2

end Reduction

end NK.HassePrinciple
