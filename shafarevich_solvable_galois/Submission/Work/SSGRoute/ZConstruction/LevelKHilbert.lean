import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.ZDataTwo.Mu2Reciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Kummer pairing at the level `↥K` is the local Hilbert symbol

`Work.SSGRoute.ZDataMup.OddForm.oPairGlob ζ hζ hA α β` is the local Kummer pairing of the two
Kummer classes of `α, β ∈ (↥K)ˣ` at the finite place `A`, in the shape in which the workspace's
`§4` machinery (the product formula `oPairForm_sum_attach_eq_zero_of_outside`, the local
dictionary) computes with it.  This file identifies it with the **local Hilbert symbol** of the
completion of `↥K` at the prime `𝔮` below `A`:

  `oPairGlob … α β = finPair 𝔮 α β`,     `finPair 𝔮 α β = toAdd ⟪ᾱ, β̄⟫_𝔮`.

Consequences (used by the p. 16 computation of Schmidt–Wingberg's corrected proof): the norm
criterion `finPair_eq_zero_iff_isLocalNorm`, and hence the **transitivity (projector) formula**
`(x, a)_E = (N_{E/F} x, a)_F` (`ZConstruction.hilbertSymbol_transitivity`) become available for
`oPairGlob`, which is what makes the inert/split dichotomy of the `Σ`-terms in the paper's p. 16
computation formalisable.

## Proof

Both sides are `ZMod 2`-valued, so it suffices to show that they vanish simultaneously
(`zmodTwo_eq_of_iff_eq_zero`).  Both zero sets are the **local norm condition** for `β`:

* `oPairGlob_eq_zero_iff_mem_localNormSubgroup` (the workspace's norm criterion for the level-`K`
  pairing, expressed through the Kummer level `↥K(α^{1/2})`), and
* `finPair_eq_zero_iff_isLocalNorm` (the same criterion for the Hilbert symbol, expressed through
  the local norm subgroup of the same Kummer level — which is the norm group of the quadratic
  extension `↥K(α^{1/2})` by `Work.ZDataTwo.localNormSubgroup_eq_normGroup_quadLevel`).

`finPair_eq_zero_iff_isLocalNorm` needs a prime of `↥K` below `A` in the `primeBelow` presentation;
this is `Work.SSGRoute.ZDataTwo.primeBelow ↥K Ω A ·`, which agrees with the `hPrimeBelow`-prime of
the `§4` machinery (`NeukirchUchida.primeOf`) by injectivity of `valuationSubringAtPrime`.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- `ZMod 2`-valued functions whose zero sets coincide are equal. -/
private lemma zmodTwo_eq_of_iff_eq_zero {x y : ZMod 2} (h : (x = 0) ↔ (y = 0)) : x = y := by
  by_cases hx : x = 0
  · rw [hx, h.mp hx]
  · have hx1 : x = 1 := by
      revert hx; generalize x = x'; revert x'; decide
    have hy : y ≠ 0 := fun hy0 => hx (h.mpr hy0)
    have hy1 : y = 1 := by
      revert hy; generalize y = y'; revert y'; decide
    rw [hx1, hy1]

/-- The prime of `↥K` below `A` in the `hPrimeBelow` spelling (`NeukirchUchida.primeOf`) agrees with
the `primeBelow` spelling. -/
lemma hPrimeBelow_eq_primeBelow (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA
      = Work.SSGRoute.ZDataTwo.primeBelow ↥K Ω A
          (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA) := by
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K) ?_
  rw [← Submission.NeukirchUchida.primeOf_spec (K₁ := ↥K) (K₁' := Ω) A
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA),
      ← Work.SSGRoute.ZDataTwo.primeBelow_spec (k := ↥K) (Ω := Ω) A
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA)]

/-- **The local Kummer pairing of the `§4` machinery is the local Hilbert symbol** at the prime of
`↥K` below `A`.

The two sides are equal `ZMod 2`-valued functions; both vanish exactly on the local norm condition
for `β` with respect to the quadratic Kummer level `↥K(α^{1/2})`. -/
theorem oPairGlob_eq_finPair (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (α β : (↥K)ˣ) (hα : α ∉ NK.LocalAnabelian.powSubgroup 2 ↥K) :
    Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β
      = Work.SSGRoute.ZDataTwo.finPair (k := ↥K)
          (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA) α β := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  haveI hfd : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
    (⟨ζ, hζK⟩ : ↥K) hζ' α
  haveI hgal : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
    (⟨ζ, hζK⟩ : ↥K) hζ' α
  haveI hnf : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
    (⟨ζ, hζK⟩ : ↥K) hζ' α
  obtain ⟨hc, hy⟩ := Work.SSGRoute.H9.hLevel_quadratic_data (K := K) (Ω := Ω)
    (⟨ζ, hζK⟩ : ↥K) hζ' α hα
  have hAK : SSGRoute.IsFinPlace ↥K A :=
    Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA
  have hQ := hPrimeBelow_eq_primeBelow (K := K) (k := k) (Ω := Ω) (A := A) hA
  refine zmodTwo_eq_of_iff_eq_zero ?_
  rw [Work.SSGRoute.H9.oPairGlob_eq_zero_iff_mem_localNormSubgroup (K := K) (k := k) (Ω := Ω)
        (ζ := (⟨ζ, hζK⟩ : ↥K)) hζ' α β A hA hα,
      hQ,
      Work.SSGRoute.ZDataTwo.finPair_eq_zero_iff_isLocalNorm (k := ↥K) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) hζ' A hAK α β
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α) hc hy,
      Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup]

end Work.SSGRoute.ZConstruction
