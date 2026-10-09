import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.NormPow
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local factor of the abelian Artin map: multiplicativity, killing norms, and the level
character

This file collects the `LTRecFamHonest` versions of the local-factor lemmas of
`ZConstruction/localPairingValue.lean` (whose module is unbuildable because it imports the broken
`ZConstruction/exists_abelianArtin_localFactors`; here they are stated for `hLocalFactor`, which is
defined in `LTRecFamHonest/HonestPairing.lean` against the *clean* crux copy
`LTRecFamCrux.exists_abelianArtin_localFactors`).
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open _root_.SSGRoute
open Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

/-- **Multiplicativity of the local factor in the global element.** -/
theorem hLocalFactor_mul (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField ↥K Ω) (Φ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (y y' : (↥K)ˣ) :
    hLocalFactor (K := K) A hA L Φ (y * y') =
      hLocalFactor (K := K) A hA L Φ y * hLocalFactor (K := K) A hA L Φ y' := by
  have hpi : ∀ x : (↥K)ˣ,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA)) x =
        (NK.GlobalCFT.Idele.principalIdele ↥K x)
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA)) :=
    fun x => (Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt x
      (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA))).symm
  unfold hLocalFactor
  rw [hpi (y * y'), hpi y, hpi y', map_mul, NK.GlobalCFT.Idele.mul_apply,
    NK.CFTLib.IdeleHasse.onePlace_mul, map_mul]

/-- **The local factor kills the local norm subgroup.** -/
theorem hLocalFactor_eq_one_of_mem_localNormSubgroup (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (hΦ : ∀ x ∈ NK.GlobalCFT.Idele.normImage ↥K ↥L, Φ x = 1) (γ : (↥K)ˣ)
    (hγ : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA)) γ ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA))) :
    hLocalFactor (K := K) A hA L Φ γ = 1 := by
  rw [hLocalFactor]
  exact hΦ _
    ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥L) _ _).mpr hγ)

/-- **The component bookkeeping**: trivial local `p`-th power class means the component is a
`p`-th power. -/
theorem hLocalImageAt_mem_powRange_of_localPowClass_eq_one (hA : SSGRoute.IsFinPlace k A)
    (γ : (↥K)ˣ)
    (hγ : NK.UchidaKummer.localPowClass ↥K p (hPrimeBelow (K := K) (A := A) hA) γ = 1) :
    NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA)) γ ∈
      (powMonoidHom p :
        ((hPrimeBelow (K := K) (A := A) hA).adicCompletion ↥K)ˣ →*
        ((hPrimeBelow (K := K) (A := A) hA).adicCompletion ↥K)ˣ).range := by
  rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hγ
  exact (QuotientGroup.eq_one_iff _).mp hγ

/-- **The local factor kills an element whose local Kummer class is trivial** (a local `p`-th
power), for a level of order `p` over `↥K`. -/
theorem hLocalFactor_eq_one_of_localPowClass_eq_one (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (hcard : Nat.card (↥L ≃ₐ[↥K] ↥L) = p)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (hΦ : ∀ x ∈ NK.GlobalCFT.Idele.normImage ↥K ↥L, Φ x = 1) (γ : (↥K)ˣ)
    (hγ : NK.UchidaKummer.localPowClass ↥K p (hPrimeBelow (K := K) (A := A) hA) γ = 1) :
    hLocalFactor (K := K) A hA L Φ γ = 1 :=
  hLocalFactor_eq_one_of_mem_localNormSubgroup (K := K) hA L Φ hΦ γ
    (mem_localNormSubgroup_of_mem_powRange (K := ↥K) (L := ↥L) hcard
      (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) (A := A) hA)) _
      (hLocalImageAt_mem_powRange_of_localPowClass_eq_one (K := K) (p := p) (A := A) hA γ hγ))

/-- **The Kummer character of `b` vanishes on the fixing subgroup of any level containing its
Kummer field.** -/
theorem kummerCharZMod_eq_zero_of_mem_fixingSubgroup (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (b : (↥K)ˣ) {L : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (hKL : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) b ≤ L)
    {σ : Ω ≃ₐ[↥K] Ω} (hσ : σ ∈ L.fixingSubgroup) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ = 0 := by
  have hroot : kummerSqrtZMod (Ω := Ω) p b ∈ L :=
    hKL (NK.LocalAnabelian.mem_kummerField_of_pow_eq (K' := Ω)
      (kummerSqrtZMod_pow (Ω := Ω) p b))
  have hfix : (σ : Ω → Ω) (kummerSqrtZMod (Ω := Ω) p b) = kummerSqrtZMod (Ω := Ω) p b :=
    (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ _ hroot
  rw [kummerCharZMod_apply]
  refine kummerIdx_eq_zero_of_apply_eq p hζ b (kummerSqrtUnitZMod (Ω := Ω) p b)
    (kummerSqrtUnitZMod_pow (Ω := Ω) p b) σ ?_
  rw [kummerSqrtUnitZMod_coe]
  exact hfix

/-- **The Kummer character of `b` depends only on the restriction to a level containing the Kummer
field of `b`.** -/
theorem kummerCharZMod_eq_of_restrictNormalHom_eq (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (b : (↥K)ˣ) {L : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (hKL : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) b ≤ L)
    {σ σ' : Ω ≃ₐ[↥K] Ω}
    (h : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L σ =
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L σ') :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ =
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ' := by
  have hτ : (σ⁻¹ * σ' : Ω ≃ₐ[↥K] Ω) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hρ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L (σ⁻¹ * σ') = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : (↑(((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L) (σ⁻¹ * σ'))
        ⟨x, hx⟩) : Ω) = x := by
      have h3 : ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L) (σ⁻¹ * σ')) ⟨x, hx⟩
          = ⟨x, hx⟩ := by
        rw [hρ]; rfl
      simpa using congrArg (fun z : ↥L => (z : Ω)) h3
    rw [AlgEquiv.restrictNormalHom_apply L (σ⁻¹ * σ') ⟨x, hx⟩] at h2
    simpa using h2
  have hzero : kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b (σ⁻¹ * σ') = 0 :=
    kummerCharZMod_eq_zero_of_mem_fixingSubgroup ζ hζ b hKL hτ
  have hadd : kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b (σ * (σ⁻¹ * σ')) =
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ +
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b (σ⁻¹ * σ') := by
    rw [kummerCharZMod_apply, kummerCharZMod_apply, kummerCharZMod_apply,
      kummerIdx_mul_apply p hζ b (kummerSqrtUnitZMod (Ω := Ω) p b)
        (kummerSqrtUnitZMod_pow (Ω := Ω) p b) σ (σ⁻¹ * σ')]
  have hσ' : σ * (σ⁻¹ * σ') = σ' := by group
  rw [← hσ', hadd, hzero, add_zero]

/-- **The descended level character**: the Kummer character of `b` factors through `Gal(L/↥K)` for
every level `L` containing the Kummer field of `b`. -/
theorem exists_levelCharacter (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (b : (↥K)ˣ)
    {L : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (hKL : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) b ≤ L) :
    ∃ χ : (↥L ≃ₐ[↥K] ↥L) →* Multiplicative (ZMod p),
      ∀ σ : Ω ≃ₐ[↥K] Ω,
        χ ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L) σ) =
          Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ) := by
  classical
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω) (K₁ := ↥L)
  have hadd : ∀ σ τ : Ω ≃ₐ[↥K] Ω,
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b (σ * τ) =
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ +
          kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b τ := by
    intro σ τ
    rw [kummerCharZMod_apply, kummerCharZMod_apply, kummerCharZMod_apply,
      kummerIdx_mul_apply p hζ b (kummerSqrtUnitZMod (Ω := Ω) p b)
        (kummerSqrtUnitZMod_pow (Ω := Ω) p b) σ τ]
  have hcongr : ∀ {σ σ' : Ω ≃ₐ[↥K] Ω},
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L σ =
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L σ' →
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ =
          kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ' :=
    fun h => kummerCharZMod_eq_of_restrictNormalHom_eq ζ hζ b hKL h
  refine ⟨MonoidHom.mk' (fun g => Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b
    (Classical.choose (hsurj g)))) ?_, fun σ => ?_⟩
  · intro g g'
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd ?_
    rw [← hadd]
    exact hcongr (by
      rw [map_mul, Classical.choose_spec (hsurj g), Classical.choose_spec (hsurj g'),
        Classical.choose_spec (hsurj (g * g'))])
  · refine congrArg Multiplicative.ofAdd ?_
    exact hcongr (Classical.choose_spec (hsurj
      ((AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) L) σ)))

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest
