import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.mupOddForm
import Submission.Work.SSGRoute.ZDataMup.mupOddTower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bilinearity of the odd-`p` pairing

* `hChar_mul`: the descended Kummer character is multiplicative at a common level;
* `oFactorGlob α γ`: the local factor at the Kummer level of `α`, applied to `γ`, packaged with the
  instances of that level so that it can be used in statements without instance gymnastics;
* `oFactorGlob_localClass`: this factor only depends on the local `p`-th power class of `γ`;
* `oPairGlob α β`: the pairing computed with *global* representatives `α, β ∈ Kˣ` (the level being
  the Kummer level of the first representative);
* `oPair_congr`: the pairing only depends on the *local classes* of the representatives;
* `oPair_add_left`: additivity of the pairing in the first variable.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

variable (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (hA : SSGRoute.IsFinPlace k A)

/-- **The descended Kummer character is multiplicative at a common level.** -/
theorem hChar_mul (α α' : (↥K)ˣ) {M : IntermediateField ↥K Ω}
    [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (hM : NK.LocalAnabelian.kummerField (K' := Ω) p (α * α') ≤ M)
    (hMα : NK.LocalAnabelian.kummerField (K' := Ω) p α ≤ M)
    (hMα' : NK.LocalAnabelian.kummerField (K' := Ω) p α' ≤ M)
    (g : ↥M ≃ₐ[↥K] ↥M) :
    hChar (K := K) (p := p) ζ hζ (α * α') hM g =
      hChar (K := K) (p := p) ζ hζ α hMα g * hChar (K := K) (p := p) ζ hζ α' hMα' g := by
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω) (K₁ := ↥M) g
  rw [← hσ, hChar_apply, hChar_apply, hChar_apply, ← ofAdd_add,
    ZConstruction.kummerCharZMod_add]

/-- **The local factor at the Kummer level of `α`**, applied to `γ`. -/
noncomputable def oFactorGlob (α γ : (↥K)ˣ) : ↥(hLevel (Ω := Ω) (K := K) (p := p) α) ≃ₐ[↥K]
    ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
  letI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI hnf : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ α
  hLocalFactor (K := K) A hA (hLevel (Ω := Ω) (K := K) (p := p) α)
    (oddArtin (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α)) γ

/-- The local factor is multiplicative in its argument. -/
theorem oFactorGlob_mul (α γ γ' : (↥K)ˣ) :
    oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α (γ * γ') =
      oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ *
        oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ' := by
  unfold oFactorGlob
  exact hLocalFactor_mul (K := K) hA _ _ γ γ'

/-- **The local factor at a Kummer level only depends on the local `p`-th power class of its
argument.** -/
theorem oFactorGlob_localClass (α γ γ' : (↥K)ˣ)
    (h : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) γ =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) γ') :
    oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ =
      oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ' := by
  classical
  have hδ : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) (γ * γ'⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  by_cases hα : α ∈ NK.LocalAnabelian.powSubgroup p ↥K
  · -- the level is trivial
    have hbot : hLevel (Ω := Ω) (K := K) (p := p) α = ⊥ :=
      NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) p
        Fact.out hζ hα
    haveI : Subsingleton (↥(hLevel (Ω := Ω) (K := K) (p := p) α) ≃ₐ[↥K]
        ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) := by
      rw [hbot]
      exact ⟨fun x y => AlgEquiv.ext fun z => by
        obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp z.2
        have hz : z = algebraMap ↥K ↥(⊥ : IntermediateField ↥K Ω) c := (Subtype.ext hc).symm
        rw [hz, AlgEquiv.commutes, AlgEquiv.commutes]⟩
    exact Subsingleton.elim _ _
  · have hgal' := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) (k := ↥K)
      p Fact.out hζ α hα
    haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
    haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) := hgal'.1
    haveI hnf : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
      hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ α
    have hcard : Nat.card (↥(hLevel (Ω := Ω) (K := K) (p := p) α) ≃ₐ[↥K]
        ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) = p := by
      rw [IsGalois.card_aut_eq_finrank, hgal'.2]
    have hfacδ : oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α (γ * γ'⁻¹) = 1 := by
      unfold oFactorGlob
      rw [hLocalFactor]
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp
        (hLocalImageAt_mem_powRange_of_localPowClass_eq_one (K := K) (p := p) (A := A) hA
          (γ * γ'⁻¹) hδ)
      simp only [powMonoidHom_apply] at hz
      rw [← hz]
      have h1 : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA))
          (z ^ p) = (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite
            (oddPrime (K := K) A hA)) z) ^ p := by
        rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply, map_pow,
          NK.CFTLib.IdeleHasse.onePlaceHom_apply]
      rw [h1, map_pow]
      exact hLevel_aut_pow_eq_one (Ω := Ω) (K := K) ζ hζ α _
    have hsplit : γ = (γ * γ'⁻¹) * γ' := by group
    rw [hsplit, oFactorGlob_mul, hfacδ, one_mul]

/-- **The pairing computed with global representatives**: the Kummer character of `α`, descended to
its Kummer level, evaluated at the local factor of that level applied to `β`. -/
noncomputable def oPairGlob (α β : (↥K)ˣ) : ZMod p :=
  letI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
  letI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
  (hChar (K := K) (p := p) ζ hζ α (le_refl _)
    (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α β)).toAdd

/-- The defining equation of `oPairGlob`. -/
theorem oPairGlob_def (α β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α)] :
    oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α β =
      (hChar (K := K) (p := p) ζ hζ α (le_refl _)
        (oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α β)).toAdd :=
  rfl

end

end Work.SSGRoute.ZDataMup.OddForm
