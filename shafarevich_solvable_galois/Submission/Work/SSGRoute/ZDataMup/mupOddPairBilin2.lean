import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.mupOddPairBilin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Additivity and well-definedness of the odd-`p` pairing

* `oFactorGlob_eq_one_of_localPowClass_eq_one`: a locally trivial first argument makes the factor
  trivial at *any* level;
* `oPair_congr`: the pairing depends on the representatives only through their local classes;
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

/-- The Kummer level is invariant under inversion of the class. -/
theorem hLevel_inv (β : (↥K)ˣ) :
    hLevel (Ω := Ω) (K := K) (p := p) β⁻¹ = hLevel (Ω := Ω) (K := K) (p := p) β := by
  refine le_antisymm ?_ ?_
  · rw [NK.LocalAnabelian.kummerField_le_iff]
    intro x hx
    have hx' : x⁻¹ ^ p = algebraMap ↥K Ω (β : ↥K) := by
      have h2 : x⁻¹ ^ p = (algebraMap ↥K Ω ((β⁻¹ : (↥K)ˣ) : ↥K))⁻¹ := by
        rw [inv_pow, hx]
      rw [h2]
      norm_num [Units.val_inv_eq_inv_val]
    simpa using inv_mem (NK.LocalAnabelian.mem_kummerField_of_pow_eq hx')
  · rw [NK.LocalAnabelian.kummerField_le_iff]
    intro x hx
    have hx' : x⁻¹ ^ p = algebraMap ↥K Ω ((β⁻¹ : (↥K)ˣ) : ↥K) := by
      have h2 : x⁻¹ ^ p = (algebraMap ↥K Ω (β : ↥K))⁻¹ := by
        rw [inv_pow, hx]
      rw [h2]
      norm_num [Units.val_inv_eq_inv_val]
    simpa using inv_mem (NK.LocalAnabelian.mem_kummerField_of_pow_eq hx')

/-- **The local factor of the pairing** at the level of `α`, applied to `γ`. -/
theorem oPairGlob_localClass (α γ γ' : (↥K)ˣ)
    (h : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) γ =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) γ') :
    oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ =
      oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ' := by
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
  rw [oPairGlob_def, oPairGlob_def,
    oFactorGlob_localClass (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ γ' h]

/-- **A locally trivial element has trivial local factor at every level.** -/
theorem oFactorGlob_eq_one_of_localPowClass_eq_one (α γ : (↥K)ˣ)
    (hα : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) α = 1) :
    oFactorGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α γ = 1 := by
  classical
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ α
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ α
  haveI hnf : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ α
  have hsplit : SSGRoute.IsSplitIn ↥K (hLevel (Ω := Ω) (K := K) (p := p) α) A :=
    (odd_localPowClass_eq_one_iff_isSplitIn (K := K) (p := p) ζ hζ A hA α).mp hα
  have hnorm : NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α))
      (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) = ⊤ :=
    localNormSubgroup_eq_top_of_isSplitIn (k := k) (Ω := Ω) K
      (hLevel (Ω := Ω) (K := K) (p := p) α) A (oddFinPlace (K := K) (A := A) hA)
      (oddPrime (K := K) A hA) (oddPrime_spec (K := K) (A := A) hA) hsplit
  unfold oFactorGlob
  exact hLocalFactor_eq_one_of_mem_localNormSubgroup (K := K) hA _
    (oddArtin (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α))
    (fun x hx => by
      rw [NK.GlobalCFT.Idele.normImage_eq_map] at hx
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
      exact oddArtin_norm (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α)
        (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α) y)
    γ (by rw [hnorm]; exact Subgroup.mem_top _)

end

end Work.SSGRoute.ZDataMup.OddForm
