import Mathlib
import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.unitsIncl_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

set_option linter.unusedSimpArgs false

namespace NK.HassePrinciple

/-- **The coefficient morphism of the units level transition map**: the inclusion `Lˣ ↪ L'ˣ` of
units, as a morphism of representations from the restriction of the level-`L` units representation
along `levelQuotHom h` to the level-`L'` units representation.

This is the units analogue of `NK.BrauerTwist.levelMapCoeff`; the equivariance input is
`NK.HassePrinciple.unitsIncl_smul`. -/
noncomputable def unitsLevelMapCoeff {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (unitsLevelRep V L) ⟶
      unitsLevelRep V L' :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (unitsLevelRep V L)).ρ)
    (σ := (unitsLevelRep V L').ρ) (f := unitsInclLinearMap L L' h)
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H u =>
        simp only [NK.BrauerHasse.levelQuotHom, QuotientGroup.map_mk, MonoidHom.id_apply,
          Rep.coe_res_obj_ρ', levelGroupRestrictHom_mk, unitsInclLinearMap_apply]
        exact unitsIncl_smul.{u, u, u} L L' h (u : Gal(K'/K)) x))

/-- The morphism `unitsLevelMapCoeff` acts by the coefficient inclusion. -/
theorem unitsLevelMapCoeff_apply {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K'))
    (x : (Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (unitsLevelRep V L)).V) :
    (unitsLevelMapCoeff V h).hom.toLinearMap x = unitsInclLinearMap L L' h x := rfl

/-- **The transition map of the units level system**: inflation along the quotient
`levelQuotHom h` together with the coefficient inclusion `Lˣ ↪ L'ˣ`. -/
noncomputable def unitsLevelMap {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    UnitsLevelH2 V L ⟶ UnitsLevelH2 V L' :=
  groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h) (unitsLevelMapCoeff V h) 2

/-- The computation rule for the units transition map. -/
theorem unitsLevelMap_apply {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) (x : UnitsLevelH2 V L) :
    (unitsLevelMap V h).hom x =
      (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h)
        (unitsLevelMapCoeff V h) 2).hom x := rfl

theorem exists_unitsLevelMapCoeff {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'} (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    ∃ (φ : Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (NK.HassePrinciple.unitsLevelRep V L) ⟶
        NK.HassePrinciple.unitsLevelRep V L'),
      ∀ x, φ.hom.toLinearMap x = NK.HassePrinciple.unitsInclLinearMap L L' h x :=
  ⟨unitsLevelMapCoeff V h, fun _ => rfl⟩

end NK.HassePrinciple
