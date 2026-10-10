import Mathlib.FieldTheory.Galois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Given a normal extension `L/U`, an intermediate field `M` normal over `U`, and a character
`ω : Gal(L/U) →* μ` whose kernel contains the subgroup fixing `M`, the character descends to a
character `φ : Gal(M/U) →* μ` with `φ ∘ restrictNormalHom = ω`.

Indeed the restriction map `restrictNormalHom ↥M : Gal(L/U) →* Gal(M/U)` is surjective (because
`L/U` is normal) with kernel `M.fixingSubgroup`, so `MonoidHom.liftOfSurjective` applies. -/
theorem exists_character_lift_of_fixingSubgroup_le_ker
    {U L : Type*} [Field U] [Field L] [Algebra U L] [Normal U L]
    {μ : Type*} [Group μ]
    (M : IntermediateField U L) [Normal U ↥M]
    (ω : (L ≃ₐ[U] L) →* μ) (h : M.fixingSubgroup ≤ ω.ker) :
    ∃ φ : (↥M ≃ₐ[U] ↥M) →* μ,
      ∀ σ : L ≃ₐ[U] L, φ (AlgEquiv.restrictNormalHom (F := U) (K₁ := L) ↥M σ) = ω σ := by
  let f : (L ≃ₐ[U] L) →* (↥M ≃ₐ[U] ↥M) := AlgEquiv.restrictNormalHom (F := U) (K₁ := L) ↥M
  have hf : Function.Surjective f :=
    AlgEquiv.restrictNormalHom_surjective (F := U) (K₁ := ↥M) L
  have hker : f.ker ≤ ω.ker := by
    rw [show f.ker = M.fixingSubgroup from IntermediateField.restrictNormalHom_ker M]
    exact h
  refine ⟨(f.liftOfSurjective hf) ⟨ω, hker⟩, fun σ => ?_⟩
  exact MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨ω, hker⟩ σ

end Work.SSGRoute
