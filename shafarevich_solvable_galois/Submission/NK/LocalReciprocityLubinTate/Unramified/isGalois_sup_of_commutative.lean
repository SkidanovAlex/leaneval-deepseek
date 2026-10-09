import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Unramified

set_option linter.style.haveILetI false

/-- The compositum of two finite Galois extensions with commutative Galois groups is again
finite-dimensional and Galois over the base, and its Galois group is commutative.

This is the standard fact that `Gal(E₁ ⊔ E₂ / F)` embeds into the product
`Gal(E₁/F) × Gal(E₂/F)` via restriction, which is abelian whenever both factors are. -/
theorem isGalois_sup_of_commutative {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (E₁ E₂ : IntermediateField F Ω) [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    [IsGalois F E₁] [IsGalois F E₂]
    (h₁ : ∀ σ τ : ↥E₁ ≃ₐ[F] ↥E₁, σ * τ = τ * σ)
    (h₂ : ∀ σ τ : ↥E₂ ≃ₐ[F] ↥E₂, σ * τ = τ * σ) :
    FiniteDimensional F ↥(E₁ ⊔ E₂) ∧ IsGalois F ↥(E₁ ⊔ E₂) ∧
      (∀ σ τ : ↥(E₁ ⊔ E₂) ≃ₐ[F] ↥(E₁ ⊔ E₂), σ * τ = τ * σ) := by
  -- The two pieces `E₁`, `E₂` viewed inside the compositum `E₁ ⊔ E₂`.
  have hsup : E₁.comap (E₁ ⊔ E₂).val ⊔ E₂.comap (E₁ ⊔ E₂).val = ⊤ := by
    let v := (E₁ ⊔ E₂).val
    have h1 : (E₁.comap v).map v = E₁ := by
      apply le_antisymm
      · rw [IntermediateField.map_le_iff_le_comap]
      · intro x hx
        refine ⟨⟨x, (SetLike.le_def.mp le_sup_left) hx⟩, ?_, rfl⟩
        exact hx
    have h2 : (E₂.comap v).map v = E₂ := by
      apply le_antisymm
      · rw [IntermediateField.map_le_iff_le_comap]
      · intro x hx
        refine ⟨⟨x, (SetLike.le_def.mp le_sup_right) hx⟩, ?_, rfl⟩
        exact hx
    refine top_unique ?_
    intro x _
    rw [← IntermediateField.map_mem_map (E₁.comap v ⊔ E₂.comap v) v]
    rw [IntermediateField.map_sup, h1, h2]
    exact x.2
  -- `E₁` (resp. `E₂`) is isomorphic to its copy inside the compositum.
  have e₁ : ↥(E₁.comap (E₁ ⊔ E₂).val) ≃ₐ[F] ↥E₁ :=
    { toFun := fun x => ⟨(x.1 : Ω), x.2⟩
      invFun := fun y => ⟨⟨(y : Ω), (SetLike.le_def.mp le_sup_left) y.2⟩, y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl
      commutes' := fun c => by ext; rfl }
  have e₂ : ↥(E₂.comap (E₁ ⊔ E₂).val) ≃ₐ[F] ↥E₂ :=
    { toFun := fun x => ⟨(x.1 : Ω), x.2⟩
      invFun := fun y => ⟨⟨(y : Ω), (SetLike.le_def.mp le_sup_right) y.2⟩, y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl
      commutes' := fun c => by ext; rfl }
  -- Hence the corresponding Galois groups are commutative.
  have hab₁ : ∀ σ τ : ↥(E₁.comap (E₁ ⊔ E₂).val) ≃ₐ[F] ↥(E₁.comap (E₁ ⊔ E₂).val),
      σ * τ = τ * σ := by
    intro σ τ
    apply (AlgEquiv.autCongr e₁).injective
    rw [map_mul, map_mul]
    exact h₁ _ _
  have hab₂ : ∀ σ τ : ↥(E₂.comap (E₁ ⊔ E₂).val) ≃ₐ[F] ↥(E₂.comap (E₁ ⊔ E₂).val),
      σ * τ = τ * σ := by
    intro σ τ
    apply (AlgEquiv.autCongr e₂).injective
    rw [map_mul, map_mul]
    exact h₂ _ _
  haveI : IsGalois F ↥(E₁.comap (E₁ ⊔ E₂).val) := (AlgEquiv.transfer_galois e₁).mpr inferInstance
  haveI : IsGalois F ↥(E₂.comap (E₁ ⊔ E₂).val) := (AlgEquiv.transfer_galois e₂).mpr inferInstance
  -- Restriction to the two factors, as a homomorphism into a product.
  let Φ : (↥(E₁ ⊔ E₂) ≃ₐ[F] ↥(E₁ ⊔ E₂)) →*
      ((↥(E₁.comap (E₁ ⊔ E₂).val) ≃ₐ[F] ↥(E₁.comap (E₁ ⊔ E₂).val)) ×
       (↥(E₂.comap (E₁ ⊔ E₂).val) ≃ₐ[F] ↥(E₂.comap (E₁ ⊔ E₂).val))) :=
    (AlgEquiv.restrictNormalHom (E := ↥(E₁.comap (E₁ ⊔ E₂).val)) (K₁ := ↥(E₁ ⊔ E₂))).prod
      (AlgEquiv.restrictNormalHom (E := ↥(E₂.comap (E₁ ⊔ E₂).val)) (K₁ := ↥(E₁ ⊔ E₂)))
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hker₁ : (AlgEquiv.restrictNormalHom (E := ↥(E₁.comap (E₁ ⊔ E₂).val))
        (K₁ := ↥(E₁ ⊔ E₂))) σ = 1 := by
      have := congrArg Prod.fst hσ
      simpa [Φ] using this
    have hker₂ : (AlgEquiv.restrictNormalHom (E := ↥(E₂.comap (E₁ ⊔ E₂).val))
        (K₁ := ↥(E₁ ⊔ E₂))) σ = 1 := by
      have := congrArg Prod.snd hσ
      simpa [Φ] using this
    have hmem₁ : σ ∈ (E₁.comap (E₁ ⊔ E₂).val).fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hker₁
    have hmem₂ : σ ∈ (E₂.comap (E₁ ⊔ E₂).val).fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hker₂
    have hmem : σ ∈ (⊤ : IntermediateField F ↥(E₁ ⊔ E₂)).fixingSubgroup := by
      rw [← hsup, IntermediateField.fixingSubgroup_sup]
      exact ⟨hmem₁, hmem₂⟩
    rw [IntermediateField.fixingSubgroup_top] at hmem
    exact Subgroup.mem_bot.mp hmem
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [isGalois_iff]
    exact ⟨inferInstance, inferInstance⟩
  · intro σ τ
    apply hΦinj
    rw [map_mul, map_mul]
    exact Prod.ext (hab₁ _ _) (hab₂ _ _)

end NK.LocalReciprocityLubinTate.Unramified
