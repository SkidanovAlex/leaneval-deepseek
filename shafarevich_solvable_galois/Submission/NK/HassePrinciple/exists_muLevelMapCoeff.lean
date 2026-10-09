import Mathlib
import Submission.NK.HassePrinciple.MuLevel
import Submission.NK.HassePrinciple.MuLevelEquivariance
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSimpArgs false

namespace NK.HassePrinciple

universe u

open CategoryTheory

/-- **The coefficient morphism of the `μ_p` level transition map**: the inclusion `μ_p(L) ↪ μ_p(L')`
of roots of unity, as a morphism of representations from the restriction of the level-`L` `μ_p`
representation along `levelQuotHom h` to the level-`L'` `μ_p` representation.

The `μ_p`-analogue of `NK.HassePrinciple.unitsLevelMapCoeff`; the equivariance input is
`NK.HassePrinciple.muLevelIncl_smul`. -/
noncomputable def muLevelMapCoeff {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (muLevelRep p V L) ⟶
      muLevelRep p V L' :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (muLevelRep p V L)).ρ)
    (σ := (muLevelRep p V L').ρ) (f := muLevelInclLinearMap p L L' h)
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H u =>
        simp only [NK.BrauerHasse.levelQuotHom, QuotientGroup.map_mk, MonoidHom.id_apply,
          Rep.coe_res_obj_ρ', levelGroupRestrictHom_mk, muLevelInclLinearMap_apply]
        exact muLevelIncl_smul.{u, u, u} p L L' h (u : Gal(K'/K)) x))

/-- The morphism `muLevelMapCoeff` acts by the coefficient inclusion. -/
theorem muLevelMapCoeff_apply {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K'))
    (x : (Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (muLevelRep p V L)).V) :
    (muLevelMapCoeff p V h).hom.toLinearMap x = muLevelInclLinearMap p L L' h x := rfl

theorem exists_muLevelMapCoeff {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K'))
    {L L' : FiniteGaloisIntermediateField K K'} (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    ∃ (φ : Rep.res (NK.BrauerHasse.levelQuotHom (U := V) h) (NK.HassePrinciple.muLevelRep p V L) ⟶
        NK.HassePrinciple.muLevelRep p V L'),
      ∀ x, φ.hom.toLinearMap x = NK.HassePrinciple.muLevelInclLinearMap p L L' h x :=
  ⟨muLevelMapCoeff p V h, fun _ => rfl⟩

end NK.HassePrinciple
