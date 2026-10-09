import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Conjugation equivariance of the Kummer cochain

For `b ∈ Kˣ` and `σ ∈ Gal(Ω/k)` the Kummer cochain of the conjugate class `σ • b` is the conjugate
cochain of `b`:

  `z_{σ • b}(τ) = z_b(σ⁻¹ τ σ)`   for every `τ ∈ Gal(Ω/k)`,

where `σ • b` is the action of `σ` on `(↥K)ˣ` through `AlgEquiv.restrictNormalHom K σ` and the
conjugate cochain is the usual action on functions.

This is the naturality statement that lets Schmidt–Wingberg's §4 conditions `(3)`, `(4)` (and the
Claim `(z_i)^σ_{P_i} = 0` for involutions `σ`) be transferred between a class and its conjugates.

The proof reduces both sides to "the automorphism fixes a square root of the class": for
`τ ∈ K.fixingSubgroup`, `σ(√b)` is a square root of the class of `σ • b`, whence

  `z_{σ•b}(τ) = 0  ↔  τ (σ √b) = σ √b  ↔  (σ⁻¹ τ σ) √b = √b  ↔  z_b(σ⁻¹ τ σ) = 0`,

and two elements of `ZMod 2` with the same vanishing set are equal.  Off the fixing subgroup both
sides vanish, by normality of `K.fixingSubgroup` in `Gal(Ω/k)` (`IsGalois k K`).

## Main results

* `Work.SSGRoute.kummerIdx_eq_zero_iff_apply_eq` — the Kummer index at a `p`-th root vanishes
  exactly when the automorphism fixes the root (the converse of
  `Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq`);
* `Work.SSGRoute.kummerChar_eq_zero_iff_fixes` — the same criterion for the Kummer character at an
  arbitrary square root of the class;
* `Work.SSGRoute.kummerCochar_conjElem` — the equivariance of the Kummer cochain.
-/

open scoped Classical

namespace Work.SSGRoute

section IdxFixes

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **The Kummer index of an automorphism at a `p`-th root vanishes exactly when the automorphism
fixes the root.**  This is the converse of `Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq`. -/
lemma kummerIdx_eq_zero_iff_apply_eq (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (c : Fˣ) (γ : Eˣ) (h : γ ^ p = Units.map (algebraMap F E) c) (σ : E ≃ₐ[F] E) :
    kummerIdx p hζ c γ h σ = 0 ↔ (σ : E → E) (γ : E) = (γ : E) := by
  constructor
  · intro h0
    have hspec := kummerIdx_spec p hζ c γ h σ
    have hratio : Work.Kummer.kummerRatio σ γ = 1 := by simpa [h0] using hspec
    have hcoe : (σ : E → E) (γ : E) / (γ : E) = 1 := by
      have h2 := congrArg (fun u : Eˣ => (u : E)) hratio
      simpa [Work.Kummer.kummerRatio_coe] using h2
    exact (div_eq_one_iff_eq (Units.ne_zero γ)).mp hcoe
  · intro hfix
    exact kummerIdx_eq_zero_of_apply_eq p hζ c γ h σ hfix

end IdxFixes

section Conj

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- The `algebraMap` of a normal intermediate field commutes with the restriction of a
`k`-automorphism of `Ω` to it. -/
lemma algebraMap_restrictNormalHom (K : IntermediateField k Ω) [Normal k K] (σ : Ω ≃ₐ[k] Ω)
    (x : ↥K) :
    algebraMap ↥K Ω ((AlgEquiv.restrictNormalHom K σ) x) = σ (algebraMap ↥K Ω x) :=
  AlgEquiv.restrictNormal_commutes σ K x

/-- The Kummer character depends only on the underlying function of the automorphism. -/
lemma kummerChar_congr_fun (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (a : (↥K)ˣ) {σ τ : Ω ≃ₐ[↥K] Ω} (h : ∀ x : Ω, σ x = τ x) :
    kummerChar (Ω := Ω) ζ hζ a σ = kummerChar (Ω := Ω) ζ hζ a τ := by
  have hστ : σ = τ := AlgEquiv.ext h
  rw [hστ]

/-- The Kummer character is the Kummer index at an arbitrary square root of the class. -/
lemma kummerChar_eq_kummerIdx (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (a : (↥K)ˣ) (σ : Ω ≃ₐ[↥K] Ω) (γ : Ωˣ)
    (hγ : γ ^ 2 = Units.map (algebraMap ↥K Ω) a) :
    kummerChar (Ω := Ω) ζ hζ a σ = kummerIdx 2 hζ a γ hγ σ :=
  kummerIdx_congr 2 hζ a (kummerSqrt_pow (Ω := Ω) a) hγ σ

/-- **Vanishing criterion for the Kummer character at an arbitrary square root.**  The Kummer
character of `a` vanishes at `σ` exactly when `σ` fixes the square root `γ` of `a`. -/
lemma kummerChar_eq_zero_iff_fixes (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (a : (↥K)ˣ) (σ : Ω ≃ₐ[↥K] Ω) (γ : Ωˣ)
    (hγ : γ ^ 2 = Units.map (algebraMap ↥K Ω) a) :
    kummerChar (Ω := Ω) ζ hζ a σ = 0 ↔ (σ : Ω → Ω) (γ : Ω) = (γ : Ω) := by
  rw [kummerChar_eq_kummerIdx (K := K) ζ hζ a σ γ hγ]
  exact kummerIdx_eq_zero_iff_apply_eq 2 hζ a γ hγ σ

/-- The `σ`-image of a square root of `b` is a square root of the conjugate class `σ • b`. -/
lemma smul_sqrtVal_sq (K : IntermediateField k Ω) [Normal k K] (σ : Ω ≃ₐ[k] Ω) (b : (↥K)ˣ) :
    (σ (kummerSqrtVal (Ω := Ω) b)) ^ 2 = algebraMap ↥K Ω
      ((Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b : (↥K)ˣ) : ↥K) := by
  rw [← map_pow, kummerSqrtVal_pow]
  show σ (algebraMap ↥K Ω (b : ↥K)) =
    algebraMap ↥K Ω ((AlgEquiv.restrictNormalHom K σ) (b : ↥K))
  exact (algebraMap_restrictNormalHom (K := K) σ (b : ↥K)).symm

/-- **Conjugation equivariance of the Kummer cochain.**  The Kummer cochain of the conjugate class
`σ • b` is the conjugate of the Kummer cochain of `b`: `z_{σ • b}(τ) = z_b(σ⁻¹ τ σ)`. -/
theorem kummerCochar_conjElem (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ) (σ : Ω ≃ₐ[k] Ω) :
    kummerCochar K ζ hζ (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b) =
      fun τ : Ω ≃ₐ[k] Ω => kummerCochar K ζ hζ b (σ⁻¹ * τ * σ) := by
  classical
  -- the fixing subgroup is normal: conjugation by any `ρ` preserves `K.fixingSubgroup`
  have hmem_conj : ∀ (u ρ : Ω ≃ₐ[k] Ω), u ∈ K.fixingSubgroup → ρ⁻¹ * u * ρ ∈ K.fixingSubgroup := by
    intro u ρ hu
    rw [IntermediateField.mem_fixingSubgroup_iff] at hu ⊢
    intro x hx
    have hρx : ρ x = algebraMap ↥K Ω ((AlgEquiv.restrictNormalHom K ρ) ⟨x, hx⟩) :=
      (algebraMap_restrictNormalHom (K := K) ρ ⟨x, hx⟩).symm
    have hmem : ρ x ∈ K := by
      rw [hρx]
      exact ((AlgEquiv.restrictNormalHom K ρ) ⟨x, hx⟩).2
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu (ρ x) hmem]
    exact AlgEquiv.symm_apply_apply ρ x
  funext τ
  by_cases hτ : τ ∈ K.fixingSubgroup
  · -- the conjugate element and the conjugate square root
    have hconj : σ⁻¹ * τ * σ ∈ K.fixingSubgroup := hmem_conj τ σ hτ
    have hγne : σ (kummerSqrtVal (Ω := Ω) b) ≠ 0 := by
      rw [show (0 : Ω) = σ 0 from (map_zero σ).symm]
      exact σ.injective.ne (kummerSqrtVal_ne_zero (Ω := Ω) b)
    have hγ2 : (Units.mk0 (σ (kummerSqrtVal (Ω := Ω) b)) hγne) ^ 2 =
        Units.map (algebraMap ↥K Ω)
          (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b) := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, Units.coe_map]
      exact smul_sqrtVal_sq K σ b
    have hfunτ : ∀ x : Ω,
        ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩ : Ω ≃ₐ[↥K] Ω) x = τ x :=
      fun x => rfl
    have hfunΨ : ∀ x : Ω,
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ⁻¹ * τ * σ, hconj⟩ : Ω ≃ₐ[↥K] Ω) x =
          (σ⁻¹ * τ * σ) x := fun x => rfl
    have hA : kummerCochar K ζ hζ
          (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b) τ = 0 ↔
        τ (σ (kummerSqrtVal (Ω := Ω) b)) = σ (kummerSqrtVal (Ω := Ω) b) := by
      rw [kummerCochar_apply K ζ hζ
            (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b) hτ,
        kummerChar_eq_zero_iff_fixes K ζ hζ
          (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b)
          ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩)
          (Units.mk0 (σ (kummerSqrtVal (Ω := Ω) b)) hγne) hγ2]
      simp only [hfunτ, Units.val_mk0]
    have hB : kummerCochar K ζ hζ b (σ⁻¹ * τ * σ) = 0 ↔
        τ (σ (kummerSqrtVal (Ω := Ω) b)) = σ (kummerSqrtVal (Ω := Ω) b) := by
      rw [kummerCochar_apply K ζ hζ b hconj,
        kummerChar_eq_zero_iff_fixes K ζ hζ b
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ⁻¹ * τ * σ, hconj⟩)
          (kummerSqrt (Ω := Ω) b) (kummerSqrt_pow (Ω := Ω) b)]
      simp only [kummerSqrt, Units.val_mk0, hfunΨ]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      constructor
      · intro h
        have h2 := congrArg (fun y : Ω => σ y) h
        simpa [AlgEquiv.apply_symm_apply] using h2
      · intro h
        rw [h]
        simpa using AlgEquiv.symm_apply_apply σ (kummerSqrtVal (Ω := Ω) b)
    have hiff : (kummerCochar K ζ hζ
          (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b) τ = 0) ↔
        (kummerCochar K ζ hζ b (σ⁻¹ * τ * σ) = 0) := hA.trans hB.symm
    have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    by_cases h0 : kummerCochar K ζ hζ
        (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b) τ = 0
    · have h1 : kummerCochar K ζ hζ b (σ⁻¹ * τ * σ) = 0 := hiff.mp h0
      rw [h0, h1]
    · have h1 : kummerCochar K ζ hζ b (σ⁻¹ * τ * σ) ≠ 0 := fun h => h0 (hiff.mpr h)
      rw [hz _ h0, hz _ h1]
  · have hconj : σ⁻¹ * τ * σ ∉ K.fixingSubgroup := by
      intro hmem
      apply hτ
      have heq : τ = σ * (σ⁻¹ * τ * σ) * σ⁻¹ := by group
      rw [heq]
      exact hmem_conj (σ⁻¹ * τ * σ) σ⁻¹ hmem
    rw [kummerCochar_of_not_mem K ζ hζ
        (Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom b) hτ,
      kummerCochar_of_not_mem K ζ hζ b hconj]

end Conj

end Work.SSGRoute
