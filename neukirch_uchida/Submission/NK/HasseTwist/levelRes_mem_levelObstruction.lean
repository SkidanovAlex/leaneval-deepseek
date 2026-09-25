/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Restriction of the level obstruction to a subgroup (twisted coefficients)

For `V ≤ U` two closed subgroups of `Gal(K'/K)` and a finite Galois level `L`, the *restriction*
`NK.HasseTwist.levelRes p h L : H²(U/(U ∩ Gal(K'/L)), μ_p(L)) ⟶ H²(V/(V ∩ Gal(K'/L)), μ_p(L))`
is the map induced by the inclusion of the level groups together with the *identity* coefficient
morphism (the level module `μ_p(L)` is the same for `U` and `V`).

The purpose of this file is the naturality of the level-wise localisation `NK.BrauerTwist.locLevel`
with respect to this restriction: for every place `A` of `K'`,

```
levelRes p h L ≫ locLevel p V A L = locLevel p U A L ≫ (restriction of local level groups),
```

i.e. restricting a global level class to the smaller subgroup and then localising at `A` agrees with
localising the larger subgroup first and then restricting the *local* level groups
`(V ⊓ D_A)/((V ⊓ D_A) ∩ Gal(K'/L)) →* (U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))`.

The consequence, `NK.HasseTwist.levelRes_mem_levelObstruction`, is the twisted analogue of
`NK.HassePrinciple.levelInclHom_mem_levelObstruction`: the restriction of a locally trivial level
class is locally trivial. -/

import Mathlib
import Submission.NK.HasseTwist.Restrict
import Submission.NK.HassePrinciple.levelInclHom_mem_levelObstruction

open CategoryTheory Representation
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The action of the local level group on `μ_p(L)` -/

/-- The action of a class `QuotientGroup.mk w` of the local level group `(W ⊓ D_A)/(…)` on `μ_p(L)`
is the action of the underlying element `w.1 ∈ Gal(K'/K)`. -/
private lemma localLevelRep_ρ_mk (p : ℕ) (W : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') (w : ↥(W ⊓ stabSubgroup A))
    (x : Additive ↥(muLevel p L)) :
    (localLevelRep p W A L).ρ (QuotientGroup.mk w) x = (w.1 : Gal(K'/K)) • x := rfl

/-! ## Naturality of the coefficient morphisms -/

/-- The coefficient identity `μ_p(L) → μ_p(L)` intertwines the local action of `V ⊓ D_A` with the
local action of `U ⊓ D_A` along the inclusion `V ≤ U`; this is the fact that makes the coefficient
morphism of the restriction of the localisation square well defined. -/
private lemma muIncl_localLevel_ρ {U V : Subgroup Gal(K'/K)} (h : V ≤ U) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') (p : ℕ)
    (v : ↥(V ⊓ stabSubgroup A)) (x : Additive ↥(muLevel p L)) :
    (muInclLinearMap (le_refl L))
        ((localLevelRep p U A L).ρ (NK.HassePrinciple.localLevelInclHom h A L (QuotientGroup.mk v)) x)
      = (localLevelRep p V A L).ρ (QuotientGroup.mk v) (muInclLinearMap (le_refl L) x) := by
  rw [show NK.HassePrinciple.localLevelInclHom h A L (QuotientGroup.mk v) =
      QuotientGroup.mk ⟨(v.1 : Gal(K'/K)),
        (inf_le_inf_right (stabSubgroup A) h) v.2⟩ from rfl]
  rw [localLevelRep_ρ_mk p U A L ⟨(v.1 : Gal(K'/K)), (inf_le_inf_right (stabSubgroup A) h) v.2⟩ x]
  rw [localLevelRep_ρ_mk p V A L v (muInclLinearMap (le_refl L) x)]
  exact muIncl_smul (le_refl L) (v.1 : Gal(K'/K)) x

/-- **The coefficient morphism of the restriction of the level-wise localisation**: the identity of
`μ_p(L)` viewed as a morphism from the local level representation of `V` (pulled back along the
inclusion of the local level groups) to the local level representation of `U`. -/
private noncomputable def localLevelInclCoeff (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    Rep.res (NK.HassePrinciple.localLevelInclHom h A L) (localLevelRep p U A L) ⟶
      localLevelRep p V A L :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.HassePrinciple.localLevelInclHom h A L) (localLevelRep p U A L)).ρ)
    (σ := (localLevelRep p V A L).ρ) (f := muInclLinearMap (le_refl L))
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H v =>
        rw [Rep.coe_res_obj_ρ']
        exact muIncl_localLevel_ρ.{u, u, u, u, u} h A L p v x))

/-! ## The square of restriction and localisation -/

/-- **Naturality of the level-wise localisation in the subgroup.**  For `V ≤ U` the restriction
`levelRes p h L` of the level cohomology followed by the level-wise localisation at `A` equals the
level-wise localisation of the larger subgroup followed by the restriction of the *local* level
groups. -/
private theorem levelRes_locLevel (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    levelRes p h L ≫ locLevel p V A L =
      locLevel p U A L ≫
        groupCohomology.map (NK.HassePrinciple.localLevelInclHom h A L)
          (localLevelInclCoeff p h A L) 2 := by
  rw [levelRes, locLevel, locLevel, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  exact groupCohomology.map_congr (NK.HassePrinciple.levelInclHom_comp_localInclHom h A L) rfl 2

/-- Elementwise form of `levelRes_locLevel`. -/
private theorem levelRes_locLevel_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) :
    (locLevel p V A L) ((levelRes p h L) a) =
      (groupCohomology.map (NK.HassePrinciple.localLevelInclHom h A L)
        (localLevelInclCoeff p h A L) 2) ((locLevel p U A L) a) := by
  have h1 := congrArg (fun (k : LevelH2 p U L ⟶ LocalLevelH2 p V A L) => k.hom a)
    (levelRes_locLevel p h A L)
  simpa using h1

/-! ## The restriction of the level obstruction -/

/-- **The level obstruction is a subsystem with respect to restriction.**  Restricting a locally
trivial class of the level `L` from `U` to a subgroup `V ≤ U` yields a locally trivial class: the
level-wise localisation of `V` at a place `A` is the localisation of `U` followed by the restriction
of the local level groups (`levelRes_locLevel`), and the latter is linear, so it kills `0`. -/
theorem levelRes_mem_levelObstruction (p : ℕ) {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L : FiniteGaloisIntermediateField K K'} {a : NK.BrauerTwist.LevelH2 p U L}
    (ha : a ∈ NK.HasseTwist.levelObstruction p U L) :
    (NK.HasseTwist.levelRes p h L) a ∈ NK.HasseTwist.levelObstruction p V L := by
  rw [mem_levelObstruction_iff] at ha ⊢
  intro A
  rw [levelRes_locLevel_apply p h A.1 L a, ha A, map_zero]

end NK.HasseTwist
