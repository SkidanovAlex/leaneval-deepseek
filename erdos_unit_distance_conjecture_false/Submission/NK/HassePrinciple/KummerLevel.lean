/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer morphism between the level systems

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

The inclusion `μ_p(L) ↪ Lˣ` as a morphism of level representations (both over the level group
`LevelGroup V L` of this chapter's vocabulary, built in `MuLevel.lean` and `UnitsLevel.lean`), and
the induced map on level cohomology

`kummerLevel p V L : MuLevelH2 p V L ⟶ UnitsLevelH2 V L`.

This is the level-wise piece of the Kummer morphism `kummer : H2Twist V → H2Units V` between the
colimits of the `μ_p` and units level systems; its naturality with respect to the transition
morphisms (which makes it well defined on the colimits) is the remaining step, see README §10.4.
-/

import Submission.NK.HassePrinciple.MuLevel

open CategoryTheory Representation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The coefficient inclusion `μ_p(L) ↪ Lˣ` as a `CoeffInt`-linear map. -/
noncomputable def muToUnitsLinearMap (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    Additive ↥(rootsOfUnity p ↥L) →ₗ[CoeffInt] Additive (↥L)ˣ where
  toFun x := Additive.ofMul ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ)
  map_add' x y := by
    change Additive.ofMul (((Additive.toMul x * Additive.toMul y : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ)) =
      Additive.ofMul ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ) +
        Additive.ofMul ((Additive.toMul y : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ)
    rw [Submonoid.coe_mul]
    rfl
  map_smul' n x := by
    obtain ⟨z⟩ := n
    show Additive.ofMul ((((Additive.toMul x) ^ z : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ)) =
      Additive.ofMul (((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ) ^ z)
    congr 1

/-- The computation rule for `muToUnitsLinearMap`. -/
theorem muToUnitsLinearMap_apply (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (x : Additive ↥(rootsOfUnity p ↥L)) :
    muToUnitsLinearMap p L x =
      Additive.ofMul ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ) := rfl

/-- **The Kummer inclusion** `μ_p(L) ↪ Lˣ` as a morphism of level representations: the transport of
`NK.HassePrinciple.kummerIncl` along the representation pullback `Rep.res`. -/
noncomputable def muToUnits (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : muLevelRep p V L ⟶ unitsLevelRep V L :=
  Rep.resMap (levelGroupRestrictHom V L) (kummerIncl p K ↥L)

/-- The computation rule for the Kummer inclusion. -/
theorem muToUnits_apply (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (x : (muLevelRep p V L).V) :
    (muToUnits p V L).hom.toLinearMap x = muToUnitsLinearMap p L x := by
  simp only [muToUnits, Rep.resMap_hom_toLinearMap, muToUnitsLinearMap, kummerIncl]
  rfl

/-- **The Kummer morphism at a level**: `H²(LevelGroup V L, μ_p(L)) ⟶ H²(LevelGroup V L, Lˣ)`. -/
noncomputable def kummerLevel (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : MuLevelH2 p V L ⟶ UnitsLevelH2 V L :=
  groupCohomology.map (MonoidHom.id (LevelGroup V L)) (muToUnits p V L) 2

/-- The computation rule for `kummerLevel`. -/
theorem kummerLevel_apply (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (x : MuLevelH2 p V L) :
    (kummerLevel p V L).hom x =
      (groupCohomology.map (MonoidHom.id (LevelGroup V L)) (muToUnits p V L) 2).hom x := rfl

/-! ## What remains in this file

The **naturality** of `kummerLevel` with respect to the two transition systems,

`kummerLevel p V L ≫ unitsLevelMap V h = muLevelMap p V h ≫ kummerLevel p V L'`   (`h : L ≤ L'`),

is the statement that makes the Kummer morphism descend to the colimits `MuColimit V → H2Units V`
(README §10.4).  It is provable from `kummerLevel_apply`, `unitsLevelMap_apply`,
`muLevelMap_apply` and the coherence of the two coefficient inclusions (`muToUnits_apply` together
with `Rep.hom_ext` at the level of the underlying linear maps).
-/

end NK.HassePrinciple
