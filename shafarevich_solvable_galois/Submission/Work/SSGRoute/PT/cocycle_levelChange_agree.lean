import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute.PT

/-- **The two cocycles agree.**  For `K ≤ L ≤ L'` with places of `L`, `L'` under the same finite
place `A` of `Ω`, the level-`L'` function `b₀'` equals the level-`L` function `b₀` composed with the
restriction of decomposition groups `ρ : D_{w'} →* D_w`.

Both `b₀` and `b₀'` factor the *same* cocycle `b` on `decomp k A` (`hb₀`, `hb₀'`); surjectivity of
`restrictNormalHom L'` on `decomp k A` (which is `finQW_glue L' A hA` followed by
`Subgroup.mem_map`) supplies a lift, and
`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply` identifies the two restrictions. -/
theorem cocycle_levelChange_agree {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
    {X : Type} [AddCommGroup X] [DistribMulAction (↥K ≃ₐ[k] ↥K) X]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → X)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → X) (b₀' : (↥L' ≃ₐ[k] ↥L') → X)
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀' (AlgEquiv.restrictNormalHom L' σ))
    (hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))
    (τ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))) :
    b₀' (τ : ↥L' ≃ₐ[k] ↥L')
      = b₀ (((decompKRestrict k (↥L) (↥L')
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') τ :
            ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))) :
        ↥L ≃ₐ[k] ↥L) := by
  have hmem : (τ : ↥L' ≃ₐ[k] ↥L') ∈ (SSGRoute.decomp k A).map (SSGRoute.res k L') := by
    rw [finQW_glue L' A hA]
    exact τ.2
  obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp hmem
  have hσ' : AlgEquiv.restrictNormalHom ↥L' σ = (τ : ↥L' ≃ₐ[k] ↥L') := hστ
  have h1 : ((decompKRestrict k (↥L) (↥L')
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw') τ :
        ↥L ≃ₐ[k] ↥L) = AlgEquiv.restrictNormalHom ↥L σ := by
    rw [decompKRestrict_coe]
    show SSGRoute.PTExt.galRes k (↥L) (↥L') (τ : ↥L' ≃ₐ[k] ↥L')
      = AlgEquiv.restrictNormalHom ↥L σ
    rw [← hσ']
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (K₁ := ↥L) (K₂ := ↥L') σ).symm
  rw [h1, ← hσ']
  exact (hb₀' σ hσ).symm.trans (hb₀ σ hσ)

end Work.SSGRoute.PT
