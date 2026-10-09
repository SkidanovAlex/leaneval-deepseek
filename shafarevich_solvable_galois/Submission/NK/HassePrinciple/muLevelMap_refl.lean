import Mathlib
import Submission.NK.HassePrinciple.MuLevelMap
import Submission.NK.HassePrinciple.unitsLevelMap_refl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.HassePrinciple

theorem muLevelMap_refl {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.muLevelMap p V (le_refl (L : IntermediateField K K')) =
      CategoryTheory.CategoryStruct.id (NK.HassePrinciple.MuLevelH2 p V L) := by
  -- The transition map at the reflexive level inclusion is `groupCohomology.map` of the
  -- reflexive quotient hom `levelQuotHom (le_refl L)` and of the coefficient morphism
  -- `muLevelMapCoeff p V (le_refl L)`, whose underlying linear map is the inclusion
  -- `μ_p(L) ↪ μ_p(L)`, i.e. the identity.
  have hfg : NK.BrauerHasse.levelQuotHom (U := V) (le_refl (L : IntermediateField K K')) =
      MonoidHom.id (NK.BrauerHasse.LevelGroup V L) := by
    simp [NK.BrauerHasse.levelQuotHom]
  -- Unfold the transition map; `muLevelMap` is by definition `groupCohomology.map _ _ 2`.
  change groupCohomology.map
      (NK.BrauerHasse.levelQuotHom (U := V) (le_refl (L : IntermediateField K K')))
      (NK.HassePrinciple.muLevelMapCoeff p V (le_refl (L : IntermediateField K K'))) 2 =
    CategoryTheory.CategoryStruct.id (NK.HassePrinciple.MuLevelH2 p V L)
  -- Compare with `map (MonoidHom.id _) (𝟙 _) 2 = 𝟙 _` (Mathlib's `groupCohomology.map_id`):
  -- the group hom is the identity by `hfg`, and the coefficient morphism has the same underlying
  -- linear map as the identity by `muLevelMapCoeff_apply`.
  refine (groupCohomology.map_congr
    (f := NK.BrauerHasse.levelQuotHom (U := V) (le_refl (L : IntermediateField K K')))
    (g := MonoidHom.id _)
    (ψ := CategoryTheory.CategoryStruct.id (NK.HassePrinciple.muLevelRep p V L))
    hfg ?_ 2).trans ?_
  · ext x
    rw [NK.HassePrinciple.muLevelMapCoeff_apply.{u, u, u}]
    rfl
  · exact groupCohomology.map_id 2

end NK.HassePrinciple
