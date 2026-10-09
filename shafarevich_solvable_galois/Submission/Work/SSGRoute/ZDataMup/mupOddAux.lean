import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupOddChar
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_mul_le
import Submission.Work.SSGRoute.ZDataMup.ramificationIdx_eq_one_of_localNormSubgroup_eq_top
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_split
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary arithmetic for the odd-`p` local Tate system

* the local Kummer dictionary in "splitting" form (`odd_localPowClass_eq_one_iff_isSplitIn`):
  a global unit is a local `p`-th power at a finite place `A` exactly when `A` splits completely in
  its Kummer extension `↥K(β^{1/p})`;
* the Kummer character is faithful on its level
  (`odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup`), hence the descended character is injective
  when `β` is not a global `p`-th power (`odd_hChar_injective`);
* the passage from a trivial local norm group to complete splitting
  (`oddSplitIn_of_localNormSubgroup_eq_top`).
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

/-- The prime of `↥K` below a finite place of `Ω`. -/
abbrev oddPrime (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
  hPrimeBelow (K := K) A hA

/-- The prime below `A` is the place of `↥K` determined by `A`. -/
theorem oddPrime_spec (hA : SSGRoute.IsFinPlace k A) :
    A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
        (oddPrime (K := K) A hA) :=
  Submission.NeukirchUchida.primeOf_spec A
    (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA)

theorem oddFinPlace (hA : SSGRoute.IsFinPlace k A) : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
  Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA

/-- **The Kummer level is the adjoin of the chosen `p`-th root** (when `ζ_p ∈ ↥K`). -/
theorem odd_level_eq_adjoin (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    hLevel (Ω := Ω) (K := K) (p := p) β =
      IntermediateField.adjoin ↥K {kummerSqrtZMod (Ω := Ω) (K := ↥K) p β} :=
  NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ β
    (kummerSqrtZMod_pow (Ω := Ω) (K := ↥K) p β)

/-- The chosen `p`-th root lies in the Kummer level. -/
theorem odd_kummerSqrt_mem_level (β : (↥K)ˣ) :
    kummerSqrtZMod (Ω := Ω) (K := ↥K) p β ∈ hLevel (Ω := Ω) (K := K) (p := p) β :=
  NK.LocalAnabelian.mem_kummerField_of_pow_eq (kummerSqrtZMod_pow (Ω := Ω) (K := ↥K) p β)

/-- **The fixing subgroups of two equal intermediate fields agree.** -/
theorem odd_fixingSubgroup_congr {L M : IntermediateField ↥K Ω} (h : L = M) :
    L.fixingSubgroup = M.fixingSubgroup :=
  congrArg IntermediateField.fixingSubgroup h

/-- **Faithfulness of the Kummer character on its level**: the character of `β` vanishes at `σ`
exactly when `σ` fixes the Kummer level of `β` (with `ζ_p ∈ ↥K`). -/
theorem odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup (ζ : ↥K)
    (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) (σ : Ω ≃ₐ[↥K] Ω) :
    kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β σ = 0 ↔
      σ ∈ (hLevel (Ω := Ω) (K := K) (p := p) β).fixingSubgroup := by
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ β
  constructor
  · intro h
    have hfix := (LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt (K := ↥K) (Ω := Ω)
      p hζ β σ).mp h
    have hmem := Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
      (K := ↥K) (Ω := Ω) (kummerSqrtZMod (Ω := Ω) (K := ↥K) p β) σ hfix
    rw [odd_fixingSubgroup_congr (K := K) (odd_level_eq_adjoin (K := K) ζ hζ β)]
    exact hmem
  · intro hσ
    exact LTRecFamHonest.kummerCharZMod_eq_zero_of_mem_fixingSubgroup (K := K) ζ hζ β
      (le_rfl) hσ


/-- **The descended Kummer character is injective** when `β` is not a global `p`-th power. -/
theorem odd_hChar_injective (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β)]
    (hβ : β ∉ NK.LocalAnabelian.powSubgroup p ↥K) :
    Function.Injective (hChar (K := K) (p := p) ζ hζ β
      (le_refl (hLevel (Ω := Ω) (K := K) (p := p) β))) := by
  have hkey : ∀ g : ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]


      ↥(hLevel (Ω := Ω) (K := K) (p := p) β),
      hChar (K := K) (p := p) ζ hζ β
        (le_refl (hLevel (Ω := Ω) (K := K) (p := p) β)) g = 1 → g = 1 := by
    intro g hg
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω)
      (K₁ := ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) g
    have h1 : Multiplicative.ofAdd
        (kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β σ) = 1 := by
      rw [← hChar_apply (K := K) (p := p) ζ hζ β
        (le_refl (hLevel (Ω := Ω) (K := K) (p := p) β)) σ, hσ]
      exact hg
    have h2 : kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β σ = 0 :=
      (ofAdd_eq_one).mp h1
    have h3 : σ ∈ (hLevel (Ω := Ω) (K := K) (p := p) β).fixingSubgroup :=
      (odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup (K := K) ζ hζ β σ).mp h2
    have h4 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        ↥(hLevel (Ω := Ω) (K := K) (p := p) β) σ = 1 := by
      rw [show AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
          ↥(hLevel (Ω := Ω) (K := K) (p := p) β) σ =
          σ.restrictNormal ↥(hLevel (Ω := Ω) (K := K) (p := p) β) from rfl,
        AlgEquiv.restrictNormal_eq_one_iff]
      exact fun y hy => (IntermediateField.mem_fixingSubgroup_iff _ σ).mp h3 y hy
    rw [← hσ, h4]
  intro g g' hgg
  have h2 : g * g'⁻¹ = 1 := hkey _ (by rw [map_mul, map_inv, hgg, mul_inv_cancel])
  calc g = g * g'⁻¹ * g' := by group
    _ = 1 * g' := by rw [h2]
    _ = g' := one_mul _


/-- **The local Kummer dictionary in splitting form**: `β ∈ ↥Kˣ` is a local `p`-th power at the
finite place `A` if and only if `A` splits completely in the Kummer extension `↥K(β^{1/p})`. -/
theorem odd_localPowClass_eq_one_iff_isSplitIn (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (β : (↥K)ˣ) :
    NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) β = 1 ↔
      SSGRoute.IsSplitIn ↥K (hLevel (Ω := Ω) (K := K) (p := p) β) A := by
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ β
  have hzero : ∀ (g : ↥(SSGRoute.decomp (k := ↥K) A)),
      ZConstruction.kummerCharHom p k Ω K ζ hζ A β g = 1 ↔
        kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β (g : Ω ≃ₐ[↥K] Ω) = 0 := by
    intro g
    rw [show ZConstruction.kummerCharHom p k Ω K ζ hζ A β g =
        Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
          (g : Ω ≃ₐ[↥K] Ω)) from rfl, ofAdd_eq_one]
  constructor
  · intro hβ
    have h1 : ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA β = 1 :=
      (ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA (oddPrime (K := K) A hA) (oddPrime_spec (K := K) (A := A) hA) β).mpr hβ
    have hpt : ∀ g : ↥(SSGRoute.decomp (k := ↥K) A),
        ZConstruction.kummerCharHom p k Ω K ζ hζ A β g = 1 := by
      intro g
      have h2 := congrArg (fun χ : ↥(lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) =>
        ((χ : ↥(SSGRoute.decomp (k := ↥K) A) →* Multiplicative (ZMod p)) g)) h1
      rwa [ZConstruction.kummerCharMonoidHom_apply] at h2
    rw [SSGRoute.IsSplitIn]
    intro σ hσ
    exact (odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup (K := K) ζ hζ β σ).mp
      ((hzero ⟨σ, hσ⟩).mp (hpt ⟨σ, hσ⟩))
  · intro hsplit
    refine (ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA (oddPrime (K := K) A hA) (oddPrime_spec (K := K) (A := A) hA) β).mp ?_
    refine Subtype.ext (MonoidHom.ext fun g => ?_)
    have hfix : (g : Ω ≃ₐ[↥K] Ω) ∈
        (hLevel (Ω := Ω) (K := K) (p := p) β).fixingSubgroup := hsplit g.2
    have hσ : (g : Ω ≃ₐ[↥K] Ω) (kummerSqrtZMod (Ω := Ω) (K := ↥K) p β) =
        kummerSqrtZMod (Ω := Ω) (K := ↥K) p β :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix _
        (odd_kummerSqrt_mem_level (K := K) (p := p) β)
    rw [show ((ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA β) :
        ↥(SSGRoute.decomp (k := ↥K) A) →* Multiplicative (ZMod p)) g =
        ZConstruction.kummerCharHom p k Ω K ζ hζ A β g from rfl]
    exact (hzero g).mpr
      ((LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt (K := ↥K) (Ω := Ω)
        p hζ β (g : Ω ≃ₐ[↥K] Ω)).mpr hσ)

/-- **Trivial local norm group implies complete splitting** (the converse of
`localNormSubgroup_eq_top_of_isSplitIn` in the prime-degree case). -/
theorem oddSplitIn_of_localNormSubgroup_eq_top (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E]
    [IsGalois ↥K E] [NumberField ↥E] (hcard : Nat.card (↥E ≃ₐ[↥K] ↥E) = p)
    (h : NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E)
      (NK.GlobalCFT.Place.ofFinite (oddPrime (K := K) A hA)) = ⊤) :
    SSGRoute.IsSplitIn ↥K E A := by
  classical
  obtain ⟨q, hq⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥K) (L := ↥E) (oddPrime (K := K) A hA)
  have hin := ramificationIdx_eq_one_of_localNormSubgroup_eq_top (K := ↥K) (L := ↥E) hcard
    (oddPrime (K := K) A hA) h q hq
  have hnc : ((oddPrime (K := K) A hA).asIdeal.primesOver
      (NumberField.RingOfIntegers ↥E)).ncard = Module.finrank ↥K ↥E :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := ↥K) (L := ↥E) (oddPrime (K := K) A hA)).mpr hin
  refine (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
    (K := ↥K) (K' := Ω) (N := E) (oddPrime (K := K) A hA) A
    (oddPrime_spec (K := K) (A := A) hA)).mpr hnc

end

end Work.SSGRoute.ZDataMup.OddForm
