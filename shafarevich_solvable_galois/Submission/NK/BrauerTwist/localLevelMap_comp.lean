import Mathlib
import Submission.NK.BrauerTwist.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NK.BrauerTwist

universe u

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The quotient maps defining the *local* levels are compatible with composition, i.e. the maps
`(U ∩ D_A)/((U ∩ D_A) ∩ Gal(K'/L')) →* (U ∩ D_A)/((U ∩ D_A) ∩ Gal(K'/L))` form a functor on the
lattice of finite Galois intermediate fields.  (Local version of
`NK.BrauerHasse.levelQuotHom_comp`.) -/
private lemma localLevelQuotHom_comp (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) :
    (NK.BrauerHasse.localLevelQuotHom U A h₁).comp
        (NK.BrauerHasse.localLevelQuotHom U A h₂) =
      NK.BrauerHasse.localLevelQuotHom U A (h₁.trans h₂) := by
  simp only [NK.BrauerHasse.localLevelQuotHom]
  rw [QuotientGroup.map_comp_map
      (N := L₃.fixingSubgroup.subgroupOf (U ⊓ NK.BrauerHasse.stabSubgroup A))
      (M := L₂.fixingSubgroup.subgroupOf (U ⊓ NK.BrauerHasse.stabSubgroup A))
      (O := L₁.fixingSubgroup.subgroupOf (U ⊓ NK.BrauerHasse.stabSubgroup A))
      (f := MonoidHom.id ↥(U ⊓ NK.BrauerHasse.stabSubgroup A))
      (g := MonoidHom.id ↥(U ⊓ NK.BrauerHasse.stabSubgroup A))]
  simp

/-- The *coefficient* transitions of the local system compose: the transition
`μ_p(L₁) ↪ μ_p(L₂) ↪ μ_p(L₃)` of the cyclotomic twist is the transition `μ_p(L₁) ↪ μ_p(L₃)`.

This is the non-trivial half of the functoriality of the local level system: the two sides are the
composites of the coefficient inclusions, and they agree on elements by construction. -/
private lemma localLevelMapCoeff_comp_apply (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃)
    (x : (Rep.res (NK.BrauerHasse.localLevelQuotHom U A h₁) (localLevelRep p U A L₁)).V) :
    (localLevelMapCoeff p U A h₂).hom.toLinearMap
        ((localLevelMapCoeff p U A h₁).hom.toLinearMap x) =
      (localLevelMapCoeff p U A (h₁.trans h₂)).hom.toLinearMap x := rfl

/-- The coefficient morphisms of the local level system compose. -/
private lemma localLevelMapCoeff_comp (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) :
    (CategoryTheory.CategoryStruct.comp
        ((Rep.resFunctor (NK.BrauerHasse.localLevelQuotHom U A h₂)).map
          (localLevelMapCoeff p U A h₁))
        (localLevelMapCoeff p U A h₂)).hom.toLinearMap =
      (localLevelMapCoeff p U A (h₁.trans h₂)).hom.toLinearMap := by
  rw [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap]
  ext x
  simp only [LinearMap.comp_apply]
  exact localLevelMapCoeff_comp_apply.{u, u} p U A h₁ h₂ x

/-- **Functoriality of the local level system of the cyclotomic twist.**  The level-wise local
inflation maps of `H²((U ⊓ D_A), μ_p(L))` are compatible with composition, so that the local
cohomology of the twist is the filtered colimit of the local level cohomologies.

This is the `μ_p`-coefficient counterpart of `NK.BrauerHasse.localLevelMap_comp`. -/
theorem localLevelMap_comp {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) :
    CategoryTheory.CategoryStruct.comp (NK.BrauerTwist.localLevelMap p U A h₁)
        (NK.BrauerTwist.localLevelMap p U A h₂) =
      NK.BrauerTwist.localLevelMap p U A (h₁.trans h₂) := by
  have hf : (NK.BrauerHasse.localLevelQuotHom U A h₁).comp
        (NK.BrauerHasse.localLevelQuotHom U A h₂) =
      NK.BrauerHasse.localLevelQuotHom U A (h₁.trans h₂) :=
    localLevelQuotHom_comp U A h₁ h₂
  have hφ := localLevelMapCoeff_comp p U A h₁ h₂
  simp only [localLevelMap]
  rw [← groupCohomology.map_comp (NK.BrauerHasse.localLevelQuotHom U A h₁)
        (NK.BrauerHasse.localLevelQuotHom U A h₂) (localLevelMapCoeff p U A h₁)
        (localLevelMapCoeff p U A h₂) 2]
  exact groupCohomology.map_congr hf hφ 2

end NK.BrauerTwist
