import Mathlib

/-!
# Discriminant of a compositum with coprime discriminants

If `K₁/ℚ` is Galois and `discr K₁`, `discr K₂` are coprime, then the two number fields are
linearly disjoint, their compositum `K₁ ⊔ K₂` has degree `[K₁:ℚ] * [K₂:ℚ]` over `ℚ`, and the
absolute discriminant of the compositum is `|discr K₁| ^ [K₂:ℚ] * |discr K₂| ^ [K₁:ℚ]`.

This is proved by applying Mathlib's
`NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow` inside the ambient number
field `↥(K₁ ⊔ K₂)`, with the two `ℚ`-intermediate fields (number-isomorphic to `K₁` and `K₂`)
given by the ranges of the inclusions `K₁ ↪ K₁ ⊔ K₂` and `K₂ ↪ K₁ ⊔ K₂`.
-/

set_option linter.style.haveILetI false

open NumberField

namespace Work.Tower.CyclotomicBase

theorem discr_compositum (L : Type*) [Field L] [NumberField L] (K₁ K₂ : IntermediateField ℚ L) [IsGalois ℚ ↥K₁] (hcop : IsCoprime (NumberField.discr ↥K₁) (NumberField.discr ↥K₂)) : (NumberField.discr ↥(K₁ ⊔ K₂)).natAbs = (NumberField.discr ↥K₁).natAbs ^ Module.finrank ℚ ↥K₂ * (NumberField.discr ↥K₂).natAbs ^ Module.finrank ℚ ↥K₁ := by
  -- Work inside the compositum `E = ↥(K₁ ⊔ K₂)`.
  let v : ↥(K₁ ⊔ K₂) →ₐ[ℚ] L := IntermediateField.val (K₁ ⊔ K₂)
  let i₁ : ↥K₁ →ₐ[ℚ] ↥(K₁ ⊔ K₂) := IntermediateField.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂)
  let i₂ : ↥K₂ →ₐ[ℚ] ↥(K₁ ⊔ K₂) := IntermediateField.inclusion (le_sup_right : K₂ ≤ K₁ ⊔ K₂)
  -- The two intermediate fields of `E` corresponding to `K₁` and `K₂`.
  let K₁' : IntermediateField ℚ ↥(K₁ ⊔ K₂) := i₁.fieldRange
  let K₂' : IntermediateField ℚ ↥(K₁ ⊔ K₂) := i₂.fieldRange
  have e₁ : ↥K₁ ≃ₐ[ℚ] ↥K₁' := i₁.equivFieldRange
  have e₂ : ↥K₂ ≃ₐ[ℚ] ↥K₂' := i₂.equivFieldRange
  -- Invariance of the discriminant and the degree under these isomorphisms.
  have hdisc₁ : NumberField.discr ↥K₁' = NumberField.discr ↥K₁ :=
    (NumberField.discr_eq_discr_of_algEquiv ↥K₁ e₁).symm
  have hdisc₂ : NumberField.discr ↥K₂' = NumberField.discr ↥K₂ :=
    (NumberField.discr_eq_discr_of_algEquiv ↥K₂ e₂).symm
  have hf₁ : Module.finrank ℚ ↥K₁' = Module.finrank ℚ ↥K₁ := e₁.toLinearEquiv.finrank_eq.symm
  have hf₂ : Module.finrank ℚ ↥K₂' = Module.finrank ℚ ↥K₂ := e₂.toLinearEquiv.finrank_eq.symm
  have hcop' : IsCoprime (NumberField.discr ↥K₁') (NumberField.discr ↥K₂') := by
    rw [hdisc₁, hdisc₂]; exact hcop
  haveI : IsGalois ℚ ↥K₁' := IsGalois.of_algEquiv e₁
  have hdisj : K₁'.LinearDisjoint K₂' :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr ↥(K₁ ⊔ K₂) K₁' K₂' hcop'
  -- `K₁'` and `K₂'` together generate all of `E`.
  have hcomp₁ : v.comp i₁ = IntermediateField.val K₁ := by ext x; rfl
  have hcomp₂ : v.comp i₂ = IntermediateField.val K₂ := by ext x; rfl
  have hmap₁ : IntermediateField.map v K₁' = K₁ := by
    change IntermediateField.map v (i₁.fieldRange) = K₁
    rw [AlgHom.fieldRange_eq_map, IntermediateField.map_map, hcomp₁,
      ← AlgHom.fieldRange_eq_map (IntermediateField.val K₁), IntermediateField.fieldRange_val]
  have hmap₂ : IntermediateField.map v K₂' = K₂ := by
    change IntermediateField.map v (i₂.fieldRange) = K₂
    rw [AlgHom.fieldRange_eq_map, IntermediateField.map_map, hcomp₂,
      ← AlgHom.fieldRange_eq_map (IntermediateField.val K₂), IntermediateField.fieldRange_val]
  have hsup : K₁' ⊔ K₂' = ⊤ := by
    apply IntermediateField.map_injective v
    rw [IntermediateField.map_sup, hmap₁, hmap₂, ← AlgHom.fieldRange_eq_map v]
    exact (IntermediateField.fieldRange_val (K₁ ⊔ K₂)).symm
  -- Coprimality of the different ideals, from coprimality of the discriminants.
  have hdifcop : IsCoprime
      (Ideal.map (algebraMap (𝓞 ↥K₁') (𝓞 ↥(K₁ ⊔ K₂))) (differentIdeal ℤ (𝓞 ↥K₁')))
      (Ideal.map (algebraMap (𝓞 ↥K₂') (𝓞 ↥(K₁ ⊔ K₂))) (differentIdeal ℤ (𝓞 ↥K₂'))) :=
    NumberField.isCoprime_differentIdeal_of_isCoprime_discr ↥(K₁ ⊔ K₂) hcop'
  have h := NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
    ↥(K₁ ⊔ K₂) K₁' K₂' hdisj hsup hdifcop
  rw [hdisc₁, hdisc₂, hf₁, hf₂] at h
  exact h

end Work.Tower.CyclotomicBase
