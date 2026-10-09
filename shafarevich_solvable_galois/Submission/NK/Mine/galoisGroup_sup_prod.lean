import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IntermediateField

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

/-- The fixing subgroup of a binary supremum is the intersection of the fixing subgroups. -/
lemma fixingSubgroup_sup {F M : Type*} [Field F] [Field M] [Algebra F M]
    (L₁ L₂ : IntermediateField F M) :
    (L₁ ⊔ L₂).fixingSubgroup = L₁.fixingSubgroup ⊓ L₂.fixingSubgroup := by
  apply le_antisymm
  · exact le_inf (IntermediateField.fixingSubgroup_antitone le_sup_left)
      (IntermediateField.fixingSubgroup_antitone le_sup_right)
  · rw [← IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup)
      (K := L₁ ⊔ L₂)]
    refine sup_le ?_ ?_
    · rw [IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) (K := L₁)]
      exact inf_le_left
    · rw [IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) (K := L₂)]
      exact inf_le_right

/-- **The Galois group of a compositum of two independent Galois extensions.**

Let `M/F` be a finite Galois extension of fields and let `L₁ L₂ : IntermediateField F M` be
finite Galois subextensions with `L₁ ⊔ L₂ = ⊤` and `L₁ ⊓ L₂ = ⊥`.  Then the restriction maps
`Gal(M/F) → Gal(Lᵢ/F)` combine into an isomorphism
`Gal(M/F) ≃* Gal(L₁/F) × Gal(L₂/F)`.

This is the standard "compositum of linearly disjoint Galois extensions" statement: the map is
injective because an automorphism fixing `L₁` and `L₂` pointwise fixes their compositum `⊤`, and
it is surjective by counting, since `[L₁ ⊔ L₂ : F] = [L₁ : F] · [L₂ : F]` when `L₁ ⊓ L₂ = ⊥`. -/
theorem galoisGroup_sup_mulEquiv_prod {F M : Type*} [Field F] [Field M] [Algebra F M]
    [FiniteDimensional F M] [IsGalois F M]
    (L₁ L₂ : IntermediateField F M) [FiniteDimensional F ↥L₁] [FiniteDimensional F ↥L₂]
    [IsGalois F ↥L₁] [IsGalois F ↥L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) (hinf : L₁ ⊓ L₂ = ⊥) :
    Nonempty ((M ≃ₐ[F] M) ≃* ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂))) := by
  haveI hN₁ : Normal F ↥L₁ := inferInstance
  haveI hN₂ : Normal F ↥L₂ := inferInstance
  let φ : (M ≃ₐ[F] M) →* ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) :=
    MonoidHom.prod (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₁)
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₂)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    have h1 : (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₁) σ = 1 := by
      have h := congrArg Prod.fst hσ
      simpa [φ] using h
    have h2 : (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₂) σ = 1 := by
      have h := congrArg Prod.snd hσ
      simpa [φ] using h
    have hmem1 : σ ∈ L₁.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have key := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := M) L₁ σ ⟨x, hx⟩
      rw [h1] at key
      simpa using key.symm
    have hmem2 : σ ∈ L₂.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have key := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := M) L₂ σ ⟨x, hx⟩
      rw [h2] at key
      simpa using key.symm
    have hbot : L₁.fixingSubgroup ⊓ L₂.fixingSubgroup = ⊥ := by
      rw [← fixingSubgroup_sup L₁ L₂, hsup]
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      ext x
      exact hτ x trivial
    have hmem : σ ∈ L₁.fixingSubgroup ⊓ L₂.fixingSubgroup := ⟨hmem1, hmem2⟩
    rw [hbot] at hmem
    simpa using hmem
  refine ⟨MulEquiv.ofBijective φ ⟨hinj, ?_⟩⟩
  have hcard : Nat.card (M ≃ₐ[F] M) =
      Nat.card ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank F M, IsGalois.card_aut_eq_finrank F ↥L₁,
      IsGalois.card_aut_eq_finrank F ↥L₂]
    have hd := LinearDisjoint.finrank_sup (LinearDisjoint.of_inf_eq_bot (F := F) hinf)
    rw [hsup] at hd
    rw [show Module.finrank F ↥(⊤ : IntermediateField F M) = Module.finrank F M from
      finrank_top F M] at hd
    exact hd
  haveI : Fintype ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) := Fintype.ofFinite _
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]; exact hcard⟩
  exact hbij.2

end Commons.FieldTheory.Galois
