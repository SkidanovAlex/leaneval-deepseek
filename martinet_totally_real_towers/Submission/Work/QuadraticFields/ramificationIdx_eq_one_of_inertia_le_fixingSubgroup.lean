import Mathlib
import Submission.Work.QuadraticFields.Ramification

namespace Work.QuadraticFields

set_option linter.style.haveILetI false

open NumberField

/-- If `M/ℚ` is Galois and `F, K` are intermediate fields with `F ⊔ K = ⊤`, then an inertia
group of `𝔓` in `Gal(M/ℚ)` contained in the fixing subgroup of `K` forces `𝔓` to be unramified
over `F`: the inertia subgroup of `𝔓` over `F` is `I(𝔓) ∩ Gal(M/F)`, and
`Gal(M/F) ∩ Gal(M/K) = Gal(M/FK) = 1`. -/
theorem ramificationIdx_eq_one_of_inertia_le_fixingSubgroup {M : Type*} [Field M] [NumberField M]
    [IsGalois ℚ M] (F K : IntermediateField ℚ M) (hsup : F ⊔ K = ⊤)
    (𝔭 : Ideal (NumberField.RingOfIntegers ↥F)) (𝔓 : Ideal (NumberField.RingOfIntegers M))
    [𝔓.IsPrime] [𝔓.LiesOver 𝔭]
    (h : Ideal.inertia (M ≃ₐ[ℚ] M) 𝔓 ≤ K.fixingSubgroup) :
    𝔓.ramificationIdx (NumberField.RingOfIntegers ↥F) = 1 := by
  -- `𝔭`, being the contraction of the prime `𝔓`, is prime.
  haveI : 𝔭.IsPrime := by
    have h𝔭 : 𝔭 = 𝔓.under (𝓞 ↥F) := (Ideal.liesOver_iff 𝔓 𝔭).mp inferInstance
    rw [h𝔭]; infer_instance
  -- The action of `Gal(M/F)` on `𝓞 M` is the action of the corresponding element of
  -- `Gal(M/ℚ)`, since both are the restriction of the underlying field automorphism.
  have hsmul : ∀ (σ : F.fixingSubgroup) (x : 𝓞 M),
      (((IntermediateField.fixingSubgroupEquiv F) σ : M ≃ₐ[↥F] M) • x)
        = ((σ : M ≃ₐ[ℚ] M) • x) := by
    intro σ x
    apply RingOfIntegers.ext
    show algebraMap (𝓞 M) M (((IntermediateField.fixingSubgroupEquiv F) σ : M ≃ₐ[↥F] M) • x)
       = algebraMap (𝓞 M) M ((σ : M ≃ₐ[ℚ] M) • x)
    rw [Commons.NumberTheory.RamificationInertia.coe_smul_ringOfIntegers,
        Commons.NumberTheory.RamificationInertia.coe_smul_ringOfIntegers,
        AlgEquiv.smul_def, AlgEquiv.smul_def]
    rfl
  -- The inertia group over `ℚ` meets `Gal(M/F)` trivially, because `F ⊔ K = ⊤`.
  have hbot : Ideal.inertia (M ≃ₐ[ℚ] M) 𝔓 ⊓ F.fixingSubgroup = ⊥ := by
    apply le_bot_iff.mp
    calc Ideal.inertia (M ≃ₐ[ℚ] M) 𝔓 ⊓ F.fixingSubgroup
        ≤ K.fixingSubgroup ⊓ F.fixingSubgroup := inf_le_inf_right _ h
      _ = (F ⊔ K).fixingSubgroup := by rw [IntermediateField.fixingSubgroup_sup, inf_comm]
      _ = ⊥ := by rw [hsup, IntermediateField.fixingSubgroup_top]
  -- Hence the inertia group of `M/F` at `𝔓` is trivial.
  have hbot' : Ideal.inertia (M ≃ₐ[↥F] M) 𝔓 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    set σ : F.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv F).symm τ with hσdef
    have hστ : (IntermediateField.fixingSubgroupEquiv F) σ = τ := by
      rw [hσdef]; exact MulEquiv.apply_symm_apply _ _
    have hσ : (σ : M ≃ₐ[ℚ] M) ∈ Ideal.inertia (M ≃ₐ[ℚ] M) 𝔓 := by
      rw [Ideal.mem_inertia] at hτ ⊢
      intro x
      rw [← hsmul σ x, hστ]
      exact hτ x
    have hmem : (σ : M ≃ₐ[ℚ] M) ∈ (⊥ : Subgroup (M ≃ₐ[ℚ] M)) := by
      rw [← hbot]
      exact ⟨hσ, σ.2⟩
    have h1 : (σ : M ≃ₐ[ℚ] M) = 1 := Subgroup.mem_bot.mp hmem
    have h2 : σ = 1 := Subtype.ext h1
    show τ = 1
    rw [← hστ, h2, map_one]
  -- A trivial inertia group means ramification index one.
  exact (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
    𝔭 𝔓).mp hbot'

end Work.QuadraticFields
