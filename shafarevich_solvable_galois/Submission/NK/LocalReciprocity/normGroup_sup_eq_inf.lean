import Mathlib
import Submission.NK.LocalReciprocity.Reciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocity

universe u v

/-- **The second axiom of a class formation**, deduced from the reciprocity datum:
`N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F}L₁ˣ ∩ N_{L₂/F}L₂ˣ`.

Route (both directions):
* `⊆`: `NK.LocalReciprocity.normGroup_le_of_tower` applied to `L₁ ≤ L₁ ⊔ L₂` and `L₂ ≤ L₁ ⊔ L₂`.
* `⊇`: by the datum, `normGroup F L = ((AlgEquiv.restrictNormalHom L).comp D.artin).ker` for each
  of the three levels; rewriting this as `(L.fixingSubgroup).comap D.artin`
  (`IntermediateField.restrictNormalHom_ker`, `MonoidHom.comap_ker`), the claim follows from
  `IntermediateField.fixingSubgroup_sup` together with the fact that `comap` preserves `⊓`.

(Note that no linear-disjointness hypothesis is needed: it is the *existence of the canonical
reciprocity isomorphism* that makes the intersection axiom true in general; conversely the axiom
fails for the weak existential Artin maps of the commons.) -/
theorem normGroup_sup_eq_inf {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    (D : NK.LocalReciprocity.LocalReciprocityDatum F F')
    (L₁ L₂ : IntermediateField F F') [FiniteDimensional F ↥L₁] [Normal F ↥L₁]
    [FiniteDimensional F ↥L₂] [Normal F ↥L₂]
    [FiniteDimensional F ↥(L₁ ⊔ L₂)] [Normal F ↥(L₁ ⊔ L₂)]
    (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
    (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ)
    (hsup : ∀ σ τ : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂), σ * τ = τ * σ) :
    NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂) =
      NK.LocalReciprocity.normGroup F ↥L₁ ⊓ NK.LocalReciprocity.normGroup F ↥L₂ := by
  -- At any finite abelian level, the norm group is the preimage under the Artin map of the
  -- fixing subgroup of that level.
  have hker : ∀ (L : IntermediateField F F') [FiniteDimensional F L] [Normal F L]
      (hc : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ),
      normGroup F ↥L = L.fixingSubgroup.comap D.artin := by
    intro L _ _ hc
    rw [← (D.isLevelIso L hc).2, ← L.restrictNormalHom_ker, MonoidHom.comap_ker]
  rw [hker (L₁ ⊔ L₂) hsup, hker L₁ h₁, hker L₂ h₂,
    IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf]

end NK.LocalReciprocity
