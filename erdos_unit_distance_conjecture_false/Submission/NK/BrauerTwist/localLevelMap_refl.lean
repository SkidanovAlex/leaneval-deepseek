import Mathlib
import Submission.NK.BrauerTwist.Basic

namespace NK.BrauerTwist

universe u

/-- The local level-quotient map at a level is the identity: `localLevelQuotHom U A (le_refl L)` is
`QuotientGroup.map N N (MonoidHom.id _) = MonoidHom.id _`. -/
private lemma localLevelQuotHom_refl {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.localLevelQuotHom U A (le_refl L) =
      MonoidHom.id (NK.BrauerHasse.LocalLevelGroup U A L) := by
  unfold NK.BrauerHasse.localLevelQuotHom
  exact QuotientGroup.map_id (L.fixingSubgroup.subgroupOf (U ⊓ NK.BrauerHasse.stabSubgroup A))

/-- The coefficient morphism of the local transition map at a level is the identity (its underlying
linear map is `muInclLinearMap (le_refl L) = LinearMap.id`). -/
private lemma localLevelMapCoeff_refl_toLinearMap {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    (Rep.Hom.hom (NK.BrauerTwist.localLevelMapCoeff p U A (le_refl L))).toLinearMap
      = (Rep.Hom.hom
          (CategoryTheory.CategoryStruct.id (NK.BrauerTwist.localLevelRep p U A L))).toLinearMap := by
  have h1 : (Rep.Hom.hom (NK.BrauerTwist.localLevelMapCoeff p U A (le_refl L))).toLinearMap
      = NK.BrauerTwist.muInclLinearMap (p := p) (le_refl L) := rfl
  have h2 : (Rep.Hom.hom
        (CategoryTheory.CategoryStruct.id (NK.BrauerTwist.localLevelRep p U A L))).toLinearMap
      = (LinearMap.id : Additive ↥(NK.BrauerTwist.muLevel p L) →ₗ[NK.BrauerTwist.CoeffInt]
          Additive ↥(NK.BrauerTwist.muLevel p L)) := rfl
  have h3 : NK.BrauerTwist.muInclLinearMap (p := p) (le_refl L)
      = (LinearMap.id : Additive ↥(NK.BrauerTwist.muLevel p L) →ₗ[NK.BrauerTwist.CoeffInt]
          Additive ↥(NK.BrauerTwist.muLevel p L)) := by
    ext x
    rfl
  rw [h1, h2, h3]

/-- The local transition maps are compatible: at a level, the map `localLevelMap` is the identity. -/
theorem localLevelMap_refl {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerTwist.localLevelMap p U A (le_refl L) =
      CategoryTheory.CategoryStruct.id (NK.BrauerTwist.LocalLevelH2 p U A L) := by
  simp only [NK.BrauerTwist.localLevelMap]
  rw [groupCohomology.map_congr (localLevelQuotHom_refl U A L)
    (localLevelMapCoeff_refl_toLinearMap p U A L) 2]
  exact groupCohomology.map_id 2

end NK.BrauerTwist
