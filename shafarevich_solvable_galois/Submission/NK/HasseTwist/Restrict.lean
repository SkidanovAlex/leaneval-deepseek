/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Restriction of twisted level cohomology to a subgroup

For an inclusion `V ≤ U` of subgroups of `Gal(K'/K)` the level groups are connected by the quotient
map `NK.BrauerHasse.levelInclHom h L : V/(V ⊓ Gal(K'/L)) →* U/(U ⊓ Gal(K'/L))`, and — because the
level module `μ_p(L)` is the *same* module for both — it induces a map on the level cohomology

`NK.HasseTwist.levelRes p h L : H²(U, μ_p(L)) ⟶ H²(V, μ_p(L))`

(the *restriction* to the subgroup).  This module constructs it, proves its compatibility with the
inflation maps `levelMap` (so that it descends to the twisted profinite cohomology
`NK.HasseTwist.H2Twist.res`), and records the API that the Sylow reduction and the rank count of
Neukirch's "indecomposed prime" argument consume.  This is the twisted counterpart of
`Submission/Work/HassePrinciple/levelInclHom_injective.lean` and
`.../levelMap_levelInclHom.lean`.

## Main definitions and results

* `NK.HasseTwist.levelRes p h L` — the restriction on the level cohomology;
* `NK.HasseTwist.levelRes_levelMap` — its compatibility with inflation;
* `NK.HasseTwist.H2Twist.res p h` — the restriction on the twisted profinite cohomology
  `H²(U, μ_p) → H²(V, μ_p)`, with the computation rule `H2Twist.res_ofLevel`;
* `NK.HasseTwist.le_of_mem_localGroupSubgroupsOver`, `H2Twist.resTo` — the restriction to the
  local groups realised over a prime (used by the rank count).
-/

import Submission.NK.HasseTwist.Obstruction
import Submission.NK.HasseTwist.Inputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The group-theoretic squares -/

/-- The quotient maps `levelGroupHom` are compatible with the inclusions of the level groups: for
`V ≤ U` the map `V/(V ⊓ Gal(K'/L)) →* Gal(K'/K)/Gal(K'/L)` is the composite of
`levelInclHom h L` with the map for `U`. -/
lemma levelGroupHom_comp_levelInclHom {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    (levelGroupHom U L).comp (NK.BrauerHasse.levelInclHom h L) = levelGroupHom V L := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H v => rfl

/-- **The square of quotient maps**: the inclusion of the level groups commutes with inflation,
`(V/(V ⊓ Gal(K'/L')) →* V/(V ⊓ Gal(K'/L)))` after inclusion in `U` equals inclusion after
inflation. -/
lemma levelQuotHom_levelInclHom_comp {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    (NK.BrauerHasse.levelInclHom hV L).comp (NK.BrauerHasse.levelQuotHom (U := V) h) =
      (NK.BrauerHasse.levelQuotHom (U := U) h).comp (NK.BrauerHasse.levelInclHom hV M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

/-! ## The restriction on the level cohomology -/

/-- **The coefficient morphism of the restriction**: the identity of the level module `μ_p(L)`,
viewed as a morphism from the restriction of the level-`U` representation to the level-`V` one.
Since the two representations have the same underlying module and the same action, this is the
identity linear map. -/
noncomputable def levelResCoeff (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    Rep.res (NK.BrauerHasse.levelInclHom h L) (levelRep p U L) ⟶ levelRep p V L :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.BrauerHasse.levelInclHom h L) (levelRep p U L)).ρ)
    (σ := (levelRep p V L).ρ) (f := muInclLinearMap (le_refl L))
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H v =>
        simp only [NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk, MonoidHom.id_apply,
          Rep.coe_res_obj_ρ', levelRep_ρ_apply, muInclLinearMap_apply]
        rfl))

/-- The coefficient morphism of the restriction acts by the identity on `μ_p(L)`. -/
lemma levelResCoeff_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (x : (Rep.res (NK.BrauerHasse.levelInclHom h L) (levelRep p U L)).V) :
    (levelResCoeff p h L).hom.toLinearMap x = muInclLinearMap (le_refl L) x := rfl

/-- **The restriction map on the level cohomology**: the map induced by the inclusion of the level
groups `V/(V ⊓ Gal(K'/L)) →* U/(U ⊓ Gal(K'/L))` with the identity coefficient morphism. -/
noncomputable def levelRes (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') : LevelH2 p U L ⟶ LevelH2 p V L :=
  groupCohomology.map (NK.BrauerHasse.levelInclHom h L) (levelResCoeff p h L) 2

/-- The computation rule for the restriction map. -/
lemma levelRes_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (x : LevelH2 p U L) :
    (levelRes p h L).hom x =
      (groupCohomology.map (NK.BrauerHasse.levelInclHom h L) (levelResCoeff p h L) 2).hom x :=
  rfl

/-- **The restriction commutes with inflation.**  For `V ≤ U` and levels `L ≤ M` the two ways of
going from the level-`L` cohomology of `U` to the level-`M` cohomology of `V` agree. -/
theorem levelRes_levelMap (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) :
    levelRes p h L ≫ levelMap p V hLM = levelMap p U hLM ≫ levelRes p h M := by
  have hcomp : (NK.BrauerHasse.levelInclHom h L).comp
        (NK.BrauerHasse.levelQuotHom (U := V) hLM) =
      (NK.BrauerHasse.levelQuotHom (U := U) hLM).comp
        (NK.BrauerHasse.levelInclHom h M) :=
    levelQuotHom_levelInclHom_comp h hLM
  have hcoe : ((Rep.resMap (NK.BrauerHasse.levelQuotHom (U := V) hLM)
        (levelResCoeff p h L)) ≫ levelMapCoeff p V hLM).hom.toLinearMap =
      ((Rep.resMap (NK.BrauerHasse.levelInclHom h M)
        (levelMapCoeff p U hLM)) ≫ levelResCoeff p h M).hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  rw [levelRes, levelMap, levelRes, levelMap, ← groupCohomology.map_comp,
    ← groupCohomology.map_comp]
  exact groupCohomology.map_congr hcomp hcoe 2

/-- **The restriction commutes with inflation** (elementwise form). -/
theorem levelRes_levelMap_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) (a : LevelH2 p U L) :
    (levelRes p h M) ((levelMap p U hLM) a) = (levelMap p V hLM) ((levelRes p h L) a) := by
  have h1 := congrArg (fun (k : LevelH2 p U L ⟶ LevelH2 p V M) => k.hom a)
    (levelRes_levelMap p h hLM)
  simpa using h1.symm


/-! ## The restriction on the twisted profinite cohomology -/

section Colim

variable (p : ℕ) {U V : Subgroup Gal(K'/K)}

/-- **The restriction map on the twisted profinite cohomology**: for `V ≤ U` a map
`H²(U, μ_p) → H²(V, μ_p)`, constructed on the filtered colimit by the level-wise restriction maps
`levelRes`, which are compatible with inflation by `levelRes_levelMap`. -/
noncomputable def H2Twist.res (h : V ≤ U) : H2Twist p U → H2Twist p V :=
  H2Twist.lift p U (fun L a => H2Twist.ofLevel p V L (levelRes p h L a))
    (by
      intro L M hLM a
      rw [levelRes_levelMap_apply p h hLM, H2Twist.ofLevel_levelMap])

/-- The computation rule for the restriction on the twisted profinite cohomology. -/
@[simp]
lemma H2Twist.res_ofLevel (h : V ≤ U) (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) :
    H2Twist.res p h (H2Twist.ofLevel p U L a) =
      H2Twist.ofLevel p V L (levelRes p h L a) := rfl

/-- The restriction takes the zero class to the zero class. -/
lemma H2Twist.res_zero (h : V ≤ U) :
    H2Twist.res p h (0 : H2Twist p U) = 0 := by
  show H2Twist.res p h (H2Twist.ofLevel p U ⊥ (0 : LevelH2 p U ⊥)) = 0
  rw [H2Twist.res_ofLevel, map_zero]
  exact H2Twist.ofLevel_zero (p := p) (U := V) ⊥

end Colim

end NK.HasseTwist
