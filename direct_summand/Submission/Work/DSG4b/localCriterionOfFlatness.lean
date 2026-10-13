import Mathlib
import Submission.Work.DSG4b.LCF.General

namespace Work.DSG4b

/-- **Local criterion of flatness (Stacks 00MK).**  Let `R → S` be a local homomorphism of
Noetherian local rings and let `M` be a finite `S`-module.  If `Tor₁^R(R/𝔪, M) = 0` — here
spelled out as the injectivity of the map `M ⊗[R] 𝔪 → M`, `m ⊗ x ↦ x • m` — then `M` is flat
over `R`. -/
theorem localCriterionOfFlatness {R S M : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (h : Function.Injective ((TensorProduct.rid R M).toLinearMap ∘ₗ
      LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype)) :
    Module.Flat R M := by
  -- `TensorProduct.rid` is an isomorphism, so it does not affect injectivity
  have h𝔪 : Function.Injective (LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype) :=
    (LCF.injective_lTensor_of_comp_rid (M := M)
      (f := (IsLocalRing.maximalIdeal R).subtype)).mp h
  rw [Module.Flat.iff_lTensor_injective]
  intro I hI
  exact LCF.injective_lTensor_subtype_of_fg (R := R) (S := S) (M := M) h𝔪 I hI

end Work.DSG4b
