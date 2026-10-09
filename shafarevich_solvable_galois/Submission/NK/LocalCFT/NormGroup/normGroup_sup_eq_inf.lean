import Mathlib
import Submission.NK.LocalCFT.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace NK.LocalCFT.NormGroup

/-- **The second axiom of a class formation** for the canonical local Artin reciprocity datum:
`N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F}L₁ˣ ∩ N_{L₂/F}L₂ˣ`.

Both directions are proved through the reciprocity isomorphism:

* by `D.isLevelIso`, at each finite abelian level `L` the norm group `normGroup F ↥L` is the kernel
  of `Fˣ →* Gal(L/F)`, i.e. the preimage under `D.artin` of the fixing subgroup of `L`
  (`AlgEquiv.restrictNormalHom_ker` + `MonoidHom.comap_ker`);
* the claim then reduces to `IntermediateField.fixingSubgroup_sup` together with the fact that
  `Subgroup.comap` preserves infima. -/
theorem normGroup_sup_eq_inf {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F')
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
    [FiniteDimensional F ↥(L₁ ⊔ L₂)] [Normal F ↥(L₁ ⊔ L₂)]
    (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
    (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ)
    (hsup : ∀ σ τ : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂), σ * τ = τ * σ) :
    NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂) =
      NK.LocalReciprocity.normGroup F ↥L₁ ⊓ NK.LocalReciprocity.normGroup F ↥L₂ := by
  -- At a finite abelian level the norm group is the preimage under the Artin map of the fixing
  -- subgroup of that level.
  have hker : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L]
      (hc : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      NK.LocalReciprocity.normGroup F ↥L = L.fixingSubgroup.comap D.artin := by
    intro L _ _ hc
    rw [← (D.isLevelIso L hc).2, ← L.restrictNormalHom_ker, MonoidHom.comap_ker]
    congr 1
  rw [hker (L₁ ⊔ L₂) hsup, hker L₁ h₁, hker L₂ h₂,
    IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf]

end NK.LocalCFT.NormGroup
