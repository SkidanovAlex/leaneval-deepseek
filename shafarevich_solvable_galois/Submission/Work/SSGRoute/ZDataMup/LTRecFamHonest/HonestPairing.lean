import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.ZConstruction.localKummerLift
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
import Submission.Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
import Submission.Work.SSGRoute.ZDataMup.LTRecFamCrux.exists_abelianArtin_localFactors
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The honest level-`K` local pairing of `μ_p`, built from the *global* abelian Artin map

This is the `LTRecFamHonest` lane of `Work.SSGRoute.ZDataMup.localTate_reciprocityFamily`: the
construction of the family `F` of the target from the **global** abelian Artin map at a Kummer
level, instead of from the (opaque) local reciprocity datum of the completion
(`ZDataMup/LTRecFam.lean`, whose clause (1) is proved but whose clause (2) is not derivable —
see `NOTES_LTRecFam_session4.md` §1).

For a finite place `A` of `Ω` over `k`, a class `x ∈ V_A`, and a *lift* `x̃ ∈ Kˣ` of `x` (an
element whose local Kummer class at `A` is `x`), the level is

  `L(x̃) := ↥K(x̃^{1/p})  ⊆ Ω`  (the Kummer field of `x̃` over `↥K`, an abelian extension of degree
  dividing `p`),

and the pairing value is

  `⟨x, y⟩_A := χ_{x̃}(θ^{L(x̃)}_A(ỹ))`,

where

* `χ_{x̃}` is the Kummer character of `x̃` (a homomorphism `Gal(Ω/↥K) → ZMod p` vanishing on
  `Gal(Ω/L(x̃))`),
* `θ^{L}_A := Φ_L ∘ onePlace_𝔭 ∘ localImageAt_𝔭` is the local factor at `A` of the **global abelian
  idèlic Artin map** `Φ_L` of `L/↥K` (`ZConstruction.exists_abelianArtin_localFactors`), an element
  of `Gal(L/↥K)`,
* `θ^{L(x̃)}_A(ỹ) ∈ Gal(L(x̃)/↥K)` is computed with the *same* lift `ỹ` of `y`.

The advantage over the completion-based pairing is that the value is **determined**: `Φ_L` is
pinned by `ker Φ_L = N𝕀 ⊔ Kˣ` and the Frobenius normalisation (`ArtinUniqueness`), and the Kummer
character is a global object; the level `L(x̃)` and the lift `x̃` enter only through local classes at
`A`, which is exactly what Hilbert reciprocity needs.
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

/-! ## The level-`K` local group and local `H¹` -/

/-- The level-`K` local group at a finite place `A`. -/
abbrev hH (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓ K.fixingSubgroup

/-- The level-`K` local `H¹` at a finite place `A`. -/
abbrev hV (A : ValuationSubring Ω) : Type :=
  Work.SSGRoute.H1loc p k Ω K (ZMod p) (hH (K := K) A)

/-! ## The Kummer level of a global element -/

/-- **The Kummer level of `β ∈ Kˣ`**: the subfield `K(β^{1/p})` of `Ω`, an abelian extension of
`↥K` of degree dividing `p`. -/
abbrev hLevel (β : (↥K)ˣ) : IntermediateField ↥K Ω :=
  NK.LocalAnabelian.kummerField (K' := Ω) p β

theorem hLevel_finiteDimensional (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
  NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (K' := Ω) (k := ↥K)
    (p := p) Fact.out hζ β

theorem hLevel_isGalois (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
  NK.GlobalCFTdeep.SecondInequality.isGalois_kummerField (K' := Ω) (k := ↥K)
    (p := p) Fact.out hζ β

theorem hLevel_numberField (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β) := by
  haveI := hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β
  exact Commons.NumberTheory.NumberField.numberField_of_intermediateField
    (K := ↥K) (K' := Ω) (L := hLevel (Ω := Ω) (K := K) (p := p) β)

/-- In a group of prime order, `a * b = b * a`. -/
theorem h_mul_comm_of_card_prime {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (h : Nat.card G = p) (a b : G) : a * b = b * a := by
  haveI : IsCyclic G := isCyclic_of_prime_card h
  exact IsMulCommutative.is_comm.comm a b

/-- **The Galois group of a Kummer level is commutative** (it has order `1` or `p`). -/
theorem hLevel_isMulCommutative (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    ∀ a b : ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) β), a * b = b * a := by
  by_cases hβ : β ∈ NK.LocalAnabelian.powSubgroup p ↥K
  · have hbot : hLevel (Ω := Ω) (K := K) (p := p) β = ⊥ :=
      NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) p
        Fact.out hζ hβ
    rw [hbot]
    intro a b
    have hsub : Subsingleton (↥(⊥ : IntermediateField ↥K Ω) ≃ₐ[↥K]
        ↥(⊥ : IntermediateField ↥K Ω)) :=
      ⟨fun x y => AlgEquiv.ext fun z => by
        obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp z.2
        have hz : z = algebraMap ↥K ↥(⊥ : IntermediateField ↥K Ω) c := (Subtype.ext hc).symm
        rw [hz, AlgEquiv.commutes, AlgEquiv.commutes]⟩
    rw [Subsingleton.elim a b]
  · have hgal := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω)
      (k := ↥K) p Fact.out hζ β hβ
    haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β
    haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) := hgal.1
    have hcard : Nat.card (↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
        ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) = p := by
      rw [IsGalois.card_aut_eq_finrank, hgal.2]
    exact fun a b => h_mul_comm_of_card_prime p hcard a b

/-! ## The local factor at a finite place of an abelian Artin map -/

/-- **The prime of `↥K` below the finite place `A` of `Ω`** (the place `A` is finite over `k`, hence
over the finite extension `↥K`). -/
noncomputable abbrev hPrimeBelow (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
  Submission.NeukirchUchida.primeOf A
    (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA)

/-- **The local factor at `A` of the abelian idèlic Artin map `Φ` of a level `L/↥K`, applied to a
global element `y ∈ Kˣ`**: `θ_A(y) = Φ(onePlace_𝔭(localImageAt_𝔭 y)) ∈ Gal(L/↥K)`. -/
noncomputable def hLocalFactor (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField ↥K Ω) (Φ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (y : (↥K)ˣ) : ↥L ≃ₐ[↥K] ↥L :=
  Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA))
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) y))

/-- **The value of the honest local pairing at the level `L`**: the Kummer character of `β` (the
first variable) evaluated at any preimage in `Gal(Ω/↥K)` of the local factor of `Φ` at `A` applied
to `ν` (the second variable).  Well defined as soon as `L` contains the Kummer field of `β`. -/
noncomputable def hValueAt (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L]
    [IsGalois ↥K L] (Φ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (β ν : (↥K)ˣ) : ZMod p :=
  kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
    (Classical.choose (AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := Ω) (K₁ := ↥L)
      (hLocalFactor (K := K) A hA L Φ ν)))

/-! ## The coherent lift of the local Kummer classes -/

/-- **The coherent lift of the level-`K` local Kummer classes** at the finite place `A`
(`Work.SSGRoute.ZConstruction.exists_localKummerLift`): a choice `x ↦ x̃` of a global element of
`Kˣ` for every level-`K` local class `x`, realising `x` at `A` and coherent under addition. -/
theorem exists_hLift (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ∃ β : hV (K := K) (p := p) (k := k) (Ω := Ω) A → (↥K)ˣ,
      (∀ x, Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA (β x) =
        Work.SSGRoute.ZConstruction.localModelIso (p := p) (k := k) (Ω := Ω) (K := K)
          (A := A) hA x) ∧
      (∀ x x', Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA (β (x + x') * (β x * β x')⁻¹) = 1) :=
  Work.SSGRoute.ZConstruction.exists_localKummerLift (p := p) (k := k) (Ω := Ω) (K := K)
    ζ hζ A hA

/-- **The chosen coherent lift** at the finite place `A`. -/
noncomputable def hLift (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) : hV (K := K) (p := p) (k := k) (Ω := Ω) A → (↥K)ˣ :=
  Classical.choose (exists_hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA)

/-- The defining property of the chosen lift: it realises the level-`K` local class. -/
theorem hLift_realises (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA
        (hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x) =
      Work.SSGRoute.ZConstruction.localModelIso (p := p) (k := k) (Ω := Ω) (K := K)
        (A := A) hA x :=
  (Classical.choose_spec (exists_hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA)).1 x

/-- The coherence of the chosen lift. -/
theorem hLift_coherent (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (x x' : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA
        (hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA (x + x') *
          (hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x *
            hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x')⁻¹) = 1 :=
  (Classical.choose_spec (exists_hLift (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA)).2 x x'

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest
