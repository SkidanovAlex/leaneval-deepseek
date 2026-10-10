import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.H9.swDictionaryKills
import Submission.Work.ZDataTwo.localNormSubgroup_eq_normGroup_quadLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The transposed local dictionary at `p = 2`: the symmetry of the local Kummer pairing

The `p ≠ 2` transposed dictionary (`Work.SSGRoute.H9.swPairingValueFrob_of_kills_swap`) rests on the
*alternation* `⟨z, z⟩_A = 0` of the odd-`p` local pairing, which is false at `p = 2`.  What is true
at `p = 2` — and what replaces alternation — is the *symmetry* of the local Kummer pairing
(the symmetry of the Hilbert symbol):

    oPairGlob α β = oPairGlob β α        (α, β ∈ ↥Kˣ, `p = 2`, finite place A).

This module proves it, and deduces the transposed dictionary `oPairAt_swapTwo` from the
already-proved first-variable form (`Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count`, applied
with the two variables interchanged).

## Route

The symmetry of the pairing is proved through the *norm criterion*:

* `oFactorGlob α β = 1` iff the local component of `β` at the prime `𝔭 = hPrimeBelow A hA` is a local
  norm from the Kummer level `K(α^{1/2})` (this is `oddArtin_onePlace`, the one-place faithfulness of
  the level Artin map);
* `oPairGlob α β = 0` iff `oFactorGlob α β = 1`, the Kummer character of `α` being injective on its
  own Kummer level (`odd_hChar_injective`, the `p = 2` faithfulness);
* the local norm subgroup of a quadratic Kummer level is the norm group of the quadratic level
  `F(√ᾱ)` of the completion `F` (`Work.ZDataTwo.localNormSubgroup_eq_normGroup_quadLevel`), whose
  membership is *representability by the norm form* `X ^ 2 - ᾱ Y ^ 2`
  (`Work.HilbertSymbolGeneral.mem_normGroup_quadLevel_iff`);
* and the norm form is symmetric in its two coefficients
  (`Work.HilbertSymbolGeneral.exists_sq_sub_mul_sq_comm`).

-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup.OddForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ## Two elementary facts about `ZMod 2` -/

/-- In `ZMod 2`, a nonzero element is `1`. -/
private lemma zmodTwo_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

/-- In `ZMod 2`, an equality is determined by the vanishing of the two elements. -/
private lemma zmodTwo_eq_of_iff_eq_zero {x y : ZMod 2} (h : (x = 0) ↔ (y = 0)) : x = y := by
  by_cases hx : x = 0
  · rw [hx, h.mp hx]
  · exact (zmodTwo_eq_one_of_ne_zero x hx).trans
      (zmodTwo_eq_one_of_ne_zero y (fun hh => hx (h.mpr hh))).symm

/-! ## The Kummer level of a non-square is a quadratic extension -/

/-- **The quadratic structure of the Kummer level of a non-square.**  If `α ∈ ↥Kˣ` is not a square,
the Kummer level `↥K(α^{1/2})` is a quadratic Galois extension of `↥K` whose degree is witnessed by
a square root of `α` outside the base field. -/
lemma hLevel_quadratic_data {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (α : (↥K)ˣ)
    (hα : α ∉ NK.LocalAnabelian.powSubgroup 2 ↥K) :
    Nat.card (↥(hLevel (Ω := Ω) (K := K) (p := 2) α) ≃ₐ[↥K]
        ↥(hLevel (Ω := Ω) (K := K) (p := 2) α)) = 2 ∧
      ∃ y : ↥(hLevel (Ω := Ω) (K := K) (p := 2) α),
        y * y = algebraMap ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) α) (α : ↥K) ∧
        y ∉ Set.range (algebraMap ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) α)) := by
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) ζ hζ α
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) ζ hζ α
  obtain ⟨-, hfr⟩ := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
    (k := ↥K) (K' := Ω) 2 (by norm_num) hζ α hα
  refine ⟨?_, ?_⟩
  · rw [IsGalois.card_aut_eq_finrank]
    exact hfr
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Ω (α : ↥K))
      (by norm_num : 0 < 2)
    have hzmul : z * z = algebraMap ↥K Ω (α : ↥K) := by rw [← pow_two]; exact hz
    have hzmem : z ∈ hLevel (Ω := Ω) (K := K) (p := 2) α :=
      NK.LocalAnabelian.mem_kummerField_of_pow_eq (p := 2) hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_mul] at hzmul
      exact α.ne_zero ((algebraMap ↥K Ω).injective (hzmul.symm.trans (map_zero _).symm))
    refine ⟨⟨z, hzmem⟩, ?_, ?_⟩
    · refine Subtype.ext ?_
      rw [IntermediateField.coe_algebraMap_apply, Submonoid.coe_mul, Subtype.coe_mk]
      exact hzmul
    · rintro ⟨d, hd⟩
      have hdz : z = algebraMap ↥K Ω d := by
        have h := congrArg (fun t : ↥(hLevel (Ω := Ω) (K := K) (p := 2) α) => (t : Ω)) hd
        rw [IntermediateField.coe_algebraMap_apply] at h
        exact h.symm
      have hd0 : d ≠ 0 := by
        intro h0
        exact hz0 (by rw [hdz, h0, map_zero])
      have hdd : d * d = (α : ↥K) :=
        (algebraMap ↥K Ω).injective (by rw [map_mul, ← hdz, hzmul])
      refine hα ⟨Units.mk0 d hd0, ?_⟩
      rw [powMonoidHom_apply]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two]
      exact hdd

/-! ## The norm criterion for the local factor -/

/-- **The local factor is trivial exactly on the local norm subgroup.**  For the Kummer level
`L = ↥K(α^{1/2})` and the level Artin map of `L`, the local factor at the finite place `A` applied
to `β` is trivial if and only if the local component of `β` at the prime below `A` is a local norm
from `L`.  This is `oddArtin_onePlace`, read through the definition of `hLocalFactor`. -/
lemma oFactorGlob_eq_one_iff_mem_localNormSubgroup {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (α β : (↥K)ˣ) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A)
    [FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) α)] :
    oFactorGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α β = 1 ↔
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) β ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
          (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) α))
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) := by
  rw [show oFactorGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α β =
      Work.SSGRoute.ZDataMup.oddArtin (K := K) (hLevel (Ω := Ω) (K := K) (p := 2) α)
        (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := 2) ζ hζ α)
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA))
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) β)) from rfl]
  exact Work.SSGRoute.ZDataMup.oddArtin_onePlace (K := K) (hLevel (Ω := Ω) (K := K) (p := 2) α)
    (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := 2) ζ hζ α) _ _

/-! ## The norm form of the local norm subgroup -/

/-- **The local norm condition is representability by the norm form.**  If `α` is not a square, the
local component of `β` at the prime below `A` is a local norm from `↥K(α^{1/2})` exactly when it is
represented by `X ^ 2 - ᾱ Y ^ 2` over the completion `F = 𝔭.adicCompletion ↥K` of `↥K` at `𝔭`. -/
lemma mem_localNormSubgroup_iff_normForm {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (α β : (↥K)ˣ) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A)
    [FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) α)]
    (hα : α ∉ NK.LocalAnabelian.powSubgroup 2 ↥K) :
    (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) β ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) α))
        (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)))
      ↔ ∃ u v : (hPrimeBelow (K := K) A hA).adicCompletion ↥K,
          u ^ 2 - (algebraMap ↥K ((hPrimeBelow (K := K) A hA).adicCompletion ↥K) (α : ↥K)) * v ^ 2
            = (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) β :
                (hPrimeBelow (K := K) A hA).adicCompletion ↥K) := by
  obtain ⟨hc, hy⟩ := hLevel_quadratic_data (Ω := Ω) (K := K) ζ hζ α hα
  obtain ⟨y, hyy, hN⟩ := Work.ZDataTwo.localNormSubgroup_eq_normGroup_quadLevel (k := ↥K)
    (hPrimeBelow (K := K) A hA) α (↥(hLevel (Ω := Ω) (K := K) (p := 2) α)) hc hy
  rw [hN]
  exact Work.HilbertSymbolGeneral.mem_normGroup_quadLevel_iff y _
    (fun h => α.ne_zero ((algebraMap ↥K ((hPrimeBelow (K := K) A hA).adicCompletion ↥K)).injective
      (by rw [h, map_zero]))) hyy _

/-! ## The norm criterion for the pairing -/

/-- **The local pairing vanishes exactly on the local norm condition.**  For a non-square `α`, the
pairing of the Kummer classes of `α` and `β` at `A` vanishes if and only if the local component of
`β` at the prime below `A` is a local norm from the Kummer level of `α`. -/
lemma oPairGlob_eq_zero_iff_mem_localNormSubgroup {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (α β : (↥K)ˣ) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A)
    [FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) α)]
    (hα : α ∉ NK.LocalAnabelian.powSubgroup 2 ↥K) :
    oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α β = 0 ↔
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) β ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
          (L := ↥(hLevel (Ω := Ω) (K := K) (p := 2) α))
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) := by
  have hinj := odd_hChar_injective (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ α hα
  constructor
  · intro h
    rw [oPairGlob_def (K := K) (p := 2) (k := k) (Ω := Ω) (A := A) ζ hζ hA α β] at h
    have hx : hChar (K := K) (p := 2) ζ hζ α
        (le_refl (hLevel (Ω := Ω) (K := K) (p := 2) α)) (oFactorGlob (K := K) (p := 2)
          (k := k) (Ω := Ω) ζ hζ hA α β) =
        hChar (K := K) (p := 2) ζ hζ α
          (le_refl (hLevel (Ω := Ω) (K := K) (p := 2) α)) 1 := by
      rw [map_one]; exact h
    exact (oFactorGlob_eq_one_iff_mem_localNormSubgroup (K := K) (k := k) (Ω := Ω)
      ζ hζ α β A hA).mp (hinj hx)
  · intro h
    rw [oPairGlob_def (K := K) (p := 2) (k := k) (Ω := Ω) (A := A) ζ hζ hA α β,
      (oFactorGlob_eq_one_iff_mem_localNormSubgroup (K := K) (k := k) (Ω := Ω)
        ζ hζ α β A hA).mpr h, map_one]
    rfl

/-! ## The degenerate cases of the symmetry -/

/-- **The pairing vanishes when its second variable is a square** (the local factor is multiplicative
and `Multiplicative (ZMod 2)` has exponent `2`). -/
lemma oPairGlob_eq_zero_of_sq_right {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (α d : (↥K)ˣ) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A)
    [FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α)] :
    oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α (d * d) = 0 := by
  rw [oPairGlob_def (K := K) (p := 2) (k := k) (Ω := Ω) (A := A) ζ hζ hA α (d * d),
    oFactorGlob_mul (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α d d,
    map_mul, NK.NUV2.LC.mul_self_eq_one_zmod_two]
  rfl

/-- **The pairing vanishes when its first variable is a global square** (the Kummer level is then
trivial, so the local factor lies in the trivial Galois group). -/
lemma oPairGlob_eq_zero_of_mem_powSubgroup_fst {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (α β : (↥K)ˣ) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A)
    (hα : α ∈ NK.LocalAnabelian.powSubgroup 2 ↥K) :
    oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α β = 0 := by
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) ζ hζ α
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) ζ hζ α
  have hbot : hLevel (Ω := Ω) (K := K) (p := 2) α = ⊥ :=
    NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) 2
      (by norm_num) hζ hα
  haveI hsub : Subsingleton (↥(hLevel (Ω := Ω) (K := K) (p := 2) α) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := 2) α)) := by
    rw [hbot]
    exact ⟨fun x y => AlgEquiv.ext fun z => by
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp z.2
      have hz : z = algebraMap ↥K ↥(⊥ : IntermediateField ↥K Ω) c := (Subtype.ext hc).symm
      rw [hz, AlgEquiv.commutes, AlgEquiv.commutes]⟩
  rw [oPairGlob_def (K := K) (p := 2) (k := k) (Ω := Ω) (A := A) ζ hζ hA α β,
    Subsingleton.elim (oFactorGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α β) 1,
    map_one]
  rfl

/-! ## The symmetry of the local pairing at `p = 2` -/

/-- **Symmetry of the local Kummer pairing at `p = 2`** (the Hilbert-symbol symmetry): for two
global units `α`, `β` of `↥K` and a finite place `A`, the pairings computed with the levels of `α`
and of `β` agree.

This is the `p = 2` replacement for the alternation of the odd-`p` pairing: both sides vanish exactly
when the corresponding element is a local norm from the other's Kummer level, and that norm condition
is the symmetry of the norm form `X ^ 2 - d Y ^ 2`. -/
theorem oPairGlob_comm_two {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (α β : (↥K)ˣ) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A) :
    oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA α β =
      oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω) ζ hζ hA β α := by
  haveI hfdα : FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) ζ hζ α
  haveI hgalα : IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) ζ hζ α
  haveI hnfα : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) ζ hζ α
  haveI hfdβ : FiniteDimensional ↥K (hLevel (Ω := Ω) (K := K) (p := 2) β) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2) ζ hζ β
  haveI hgalβ : IsGalois ↥K (hLevel (Ω := Ω) (K := K) (p := 2) β) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := 2) ζ hζ β
  haveI hnfβ : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := 2) β) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := 2) ζ hζ β
  by_cases hα : α ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
  · obtain ⟨d, hd⟩ := hα
    have hdd : α = d * d := by rw [← hd, powMonoidHom_apply, pow_two]
    rw [oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω) ζ hζ α β A hA
        ⟨d, hd⟩,
      hdd, oPairGlob_eq_zero_of_sq_right (K := K) (k := k) (Ω := Ω) ζ hζ β d A hA]
  · by_cases hβ : β ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
    · obtain ⟨d, hd⟩ := hβ
      have hdd : β = d * d := by rw [← hd, powMonoidHom_apply, pow_two]
      rw [oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω) ζ hζ β α A hA
          ⟨d, hd⟩,
        hdd, oPairGlob_eq_zero_of_sq_right (K := K) (k := k) (Ω := Ω) ζ hζ α d A hA]
    · refine zmodTwo_eq_of_iff_eq_zero ?_
      rw [oPairGlob_eq_zero_iff_mem_localNormSubgroup (K := K) (k := k) (Ω := Ω)
          ζ hζ α β A hA hα,
        oPairGlob_eq_zero_iff_mem_localNormSubgroup (K := K) (k := k) (Ω := Ω)
          ζ hζ β α A hA hβ,
        mem_localNormSubgroup_iff_normForm (K := K) (k := k) (Ω := Ω) ζ hζ α β A hA hα,
        mem_localNormSubgroup_iff_normForm (K := K) (k := k) (Ω := Ω) ζ hζ β α A hA hβ]
      exact Work.HilbertSymbolGeneral.exists_sq_sub_mul_sq_comm
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) β)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (hPrimeBelow (K := K) A hA)) α)

/-- **The transposed local dictionary at `p = 2`** (the `p = 2` twin of `Work.SSGRoute.H9.swPairingValueFrob_of_kills_swap`, which carries `hp : p ≠ 2`).  If the Kummer level `K(β^{1/2})` is unramified at the finite place `A` (expressed as: the Kummer cochain of `β` kills the inertia of `A`) and the count of `α` at `A` is odd, then the local pairing of the two Kummer cochains at `A` is the value of `χ_β` at the canonical Frobenius `ψ` of `K(β^{1/2})` at `A` (no sign, since `−1 = 1` in `ZMod 2`).

The missing brick is the `p = 2` *symmetry* `oPairAt χ_α χ_β = oPairAt χ_β χ_α` (the p≠2 proof uses alternation, false at p=2; the symmetry is the Hilbert-symbol symmetry).  The first-variable form is already proved (`Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count`), so the statement follows from the symmetry plus that helper. -/
theorem oPairAt_swapTwo {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ K.fixingSubgroup)
    [FiniteDimensional ↥K (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) β)]
    [IsGalois ↥K (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) β)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) β)]
    (hkill : ∀ u ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β u = 0)
    (hpinning : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) β)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, hψ⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) β))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))
    (hcount : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (α : ↥K)))) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A hA (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β ψ := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the two readings of the pairing through global representatives
  have hcocycle : ∀ b : (↥K)ˣ,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := by
    intro b g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b g hg h hh]
    rfl
  have h1 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' hA α β :=
    oPair_toClass_eq_oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
      (ζ := (⟨ζ, hζK⟩ : ↥K)) hζ' (hA := hA) _ _ α β (hcocycle α)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ α) (hcocycle β)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β)
      (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ)
        (hζK := hζK) (hζ := hζ) (β := α) hσ)
      (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ)
        (hζK := hζK) (hζ := hζ) (β := β) hσ)
  have h2 : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
      = oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' hA β α :=
    oPair_toClass_eq_oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
      (ζ := (⟨ζ, hζK⟩ : ↥K)) hζ' (hA := hA) _ _ β α (hcocycle β)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β) (hcocycle α)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ α)
      (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ)
        (hζK := hζK) (hζ := hζ) (β := β) hσ)
      (fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ)
        (hζK := hζK) (hζ := hζ) (β := α) hσ)
  -- the symmetry of the pairing, and the dictionary read with the unramified variable second
  have hsym := oPairGlob_comm_two (K := K) (k := k) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' α β A hA
  have hunr := swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := 2) ζ hζ hζK β A hA hkill
  have hdict := Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count (K := K) ζ hζ hζK β α A hA
    ψ hψ hunr hpinning hcount
  rw [h1, hsym, ← h2]
  exact hdict

end Work.SSGRoute.H9
