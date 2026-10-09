import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute

theorem exists_cyclotomicDual (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (ZMod p) T)
      (_ : DistribMulAction (K ≃ₐ[ℚ] K) T) (_ : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T),
      @SSGRoute.IsCyclotomicDual p SSGRoute.GalQ (K ≃ₐ[ℚ] K) T SSGRoute.QBar _ _ _ _ _ _ _
        (AlgEquiv.restrictNormalHom K) ζ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set ζK : K := ⟨ζ, hζK⟩ with hζKdef
  have hζKprim : IsPrimitiveRoot ζK p :=
    IsPrimitiveRoot.of_map_of_injective (f := (algebraMap K SSGRoute.QBar : K →+* SSGRoute.QBar))
      (ζ := ζK) (by simpa [hζKdef] using hζ) (algebraMap K SSGRoute.QBar).injective
  let χ : (K ≃ₐ[ℚ] K) →* (ZMod p)ˣ := IsPrimitiveRoot.autToPow ℚ hζKprim
  let act : (K ≃ₐ[ℚ] K) → ZMod p → ZMod p := fun g t => ((χ g)⁻¹ : ZMod p) * t
  have hact_one : ∀ t, act 1 t = t := by
    intro t
    change ((χ 1)⁻¹ : ZMod p) * t = t
    rw [map_one]
    simp
  have hact_mul : ∀ g h t, act (g * h) t = act g (act h t) := by
    intro g h t
    change ((χ (g * h))⁻¹ : ZMod p) * t =
      ((χ g)⁻¹ : ZMod p) * (((χ h)⁻¹ : ZMod p) * t)
    rw [map_mul, Units.val_mul, mul_inv_rev]
    ring
  have hact_zero : ∀ g, act g 0 = 0 := by
    intro g; change ((χ g)⁻¹ : ZMod p) * 0 = 0; rw [mul_zero]
  have hact_add : ∀ g x y, act g (x + y) = act g x + act g y := by
    intro g x y
    change ((χ g)⁻¹ : ZMod p) * (x + y) = ((χ g)⁻¹ : ZMod p) * x + ((χ g)⁻¹ : ZMod p) * y
    rw [mul_add]
  letI : DistribMulAction (K ≃ₐ[ℚ] K) (ZMod p) :=
    { smul := act
      one_smul := hact_one
      mul_smul := hact_mul
      smul_zero := hact_zero
      smul_add := hact_add }
  letI : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) (ZMod p) :=
    ⟨fun g c t => by
      change act g (c * t) = c * act g t
      change ((χ g)⁻¹ : ZMod p) * (c * t) = c * (((χ g)⁻¹ : ZMod p) * t)
      ring⟩
  refine ⟨ZMod p, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact Module.finrank_self (ZMod p)
  · intro σ c hc t
    have hχ : ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)) = (c : ZMod p) := by
      have hcomm : (algebraMap K SSGRoute.QBar) ((AlgEquiv.restrictNormalHom K σ) ζK)
          = σ ((algebraMap K SSGRoute.QBar) ζK) :=
        AlgEquiv.restrictNormal_commutes σ K ζK
      have hspec := IsPrimitiveRoot.autToPow_spec ℚ hζKprim (AlgEquiv.restrictNormalHom K σ)
      have h1 : ζ ^ ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val = ζ ^ c := by
        have h2 := congrArg (algebraMap K SSGRoute.QBar) hspec
        rw [hcomm] at h2
        simp only [map_pow] at h2
        simp only [IntermediateField.algebraMap_apply] at h2
        exact h2.trans hc
      have h3 : ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val ≡ c [MOD p] := by
        have h4 := ((hζ.isOfFinOrder (NeZero.ne p)).pow_eq_pow_iff_modEq
          (n := ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val) (m := c)).mp h1
        rwa [← hζ.eq_orderOf] at h4
      calc (χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)
          = (((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val : ZMod p) :=
            (ZMod.natCast_zmod_val _).symm
        _ = (c : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h3
    have hkey : (c : ZMod p) * (((χ (AlgEquiv.restrictNormalHom K σ))⁻¹ : ZMod p)) = 1 := by
      have hcu : (c : ZMod p) = (χ (AlgEquiv.restrictNormalHom K σ) : ZMod p) := hχ.symm
      rw [hcu]
      exact mul_inv_cancel₀ (Units.ne_zero _)
    rw [nsmul_eq_mul]
    show (c : ZMod p) * (((χ (AlgEquiv.restrictNormalHom K σ))⁻¹ : ZMod p) * t) = t
    rw [← mul_assoc, hkey, one_mul]

end Work.SSGRoute
