import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.FiniteReciprocity
import Submission.Work.SSGRoute.ZDataTwo.Mu2FiniteForm
import Submission.Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
import Submission.Work.SSGRoute.ZDataTwo.finPairEqZeroOfKillsInertia
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.PlaceValBridge
import Submission.Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Hilbert symbol of `-1` and a global `𝔭`-unit at an odd place

For a number field `L`, a height-one prime `𝔭` of `𝓞 L` at which `2` is a unit, and a global unit
`a ∈ Lˣ` which is a `𝔭`-adic unit, the local Hilbert symbol of the images of `-1` and `a` in the
completion `L_𝔭` is trivial:

  `⟪-1, ā⟫_𝔭 = 1`.

Both `-1` and `a` are local units at `𝔭` and `L_𝔭(√ā)/L_𝔭` is unramified (`ᾱ` is a unit and `2` is
a unit), so `-1` — indeed *every* local unit — is a norm from `L_𝔭(√ā)`; equivalently the local
Kummer extension is unramified, and the Kummer character of a local unit kills the inertia.

The proof goes through the global finite pairing: choose a place `A` of `Ω = L̄` above `𝔭`
(`Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq`), and observe that the Kummer
characters of both `-1` and `a` kill the inertia of `A`
(`kummerChar_eq_zero_of_isInertia_of_unit_base`, the base-field form of
`Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit`).  Then
`finPairEqZeroOfKillsInertia` gives `finPair L 𝔭 (-1) a = 0`, which is exactly the statement that
the Hilbert symbol of the two local images is `1`.
-/

namespace Work.SSGRoute.ZConstruction

set_option linter.unusedVariables false

open scoped Classical

/-! ## The valuation bridges at the base field

`Work.SSGRoute.ZDataTwo.TwoRec.place_valuation_{le,lt}_one_iff` state the comparison between the
valuation of a place `A` of `Ω` and the `𝔭`-adic valuation for an *intermediate field*.  We need the
base-field form (no intermediate field), which is proved the same way. -/

theorem place_valuation_le_one_iff_base {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭) (x : K) :
    A.valuation (algebraMap K Ω x) ≤ 1 ↔ 𝔭.valuation K x ≤ 1 := by
  have hB : A.comap (algebraMap K Ω) = (𝔭.valuation K).valuationSubring := by
    rw [h𝔭, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact (Work.SSGRoute.ZDataTwo.TwoRec.comap_valuation_le_one (algebraMap K Ω) A x).symm.trans
    ((Work.SSGRoute.ZDataTwo.TwoRec.valuation_le_one_iff_of_eq hB x).trans
      (Work.SSGRoute.ZDataTwo.TwoRec.valuationSubring_valuation_le_one (𝔭.valuation K) x))

theorem place_valuation_lt_one_iff_base {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭) (x : K) :
    A.valuation (algebraMap K Ω x) < 1 ↔ 𝔭.valuation K x < 1 := by
  have hB : A.comap (algebraMap K Ω) = (𝔭.valuation K).valuationSubring := by
    rw [h𝔭, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact (Work.SSGRoute.ZDataTwo.TwoRec.comap_valuation_lt_one (algebraMap K Ω) A x).symm.trans
    ((Work.SSGRoute.ZDataTwo.TwoRec.valuation_lt_one_iff_of_eq hB x).trans
      (Work.SSGRoute.ZDataTwo.TwoRec.valuationSubring_valuation_lt_one (𝔭.valuation K) x))

/-- **The place-valuation bridge, unit form.** -/
theorem place_valuation_eq_one_iff_base {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭) (x : K) :
    A.valuation (algebraMap K Ω x) = 1 ↔ 𝔭.valuation K x = 1 := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, place_valuation_le_one_iff_base A 𝔭 h𝔭 x,
    place_valuation_lt_one_iff_base A 𝔭 h𝔭 x]

/-! ## `2` is not a local prime when it is a unit of the completion's integers -/

/-- **If `2` is a unit of the integers of the `𝔭`-adic completion, then `𝔭 ∤ 2`.** -/
theorem not_valuation_two_lt_one_of_isUnit {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers K)) :
    ¬ 𝔭.valuation K (2 : K) < 1 := by
  intro hlt
  have hnotmem : (2 : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal := by
    intro hmem
    have hmax : algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K)
        (2 : NumberField.RingOfIntegers K) ∈
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) :=
      (Work.SSGRoute.ZDataTwo.algebraMap_mem_maximalIdeal_iff K 𝔭
        (2 : NumberField.RingOfIntegers K)).mpr hmem
    have hmem2 : (2 : 𝔭.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
      rwa [← map_ofNat (algebraMap (NumberField.RingOfIntegers K)
        (𝔭.adicCompletionIntegers K)) 2]
    exact (IsLocalRing.notMem_maximalIdeal.mpr h2) hmem2
  have h1 : 𝔭.valuation K (2 : K) = 1 := by
    rw [← map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem 𝔭
      (r := (2 : NumberField.RingOfIntegers K))).mpr hnotmem
  rw [h1] at hlt
  exact lt_irrefl 1 hlt

/-! ## The Kummer character of a local unit kills the inertia, at the base field -/

/-- **The Kummer character of a `𝔭`-adic unit kills the inertia** (base-field form of
`Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit`): if `2` is a unit at the finite place `A`
and `a ∈ Lˣ` is a unit at `A`, then the Kummer character of `a` vanishes on the inertia group of
`A`, i.e. the Kummer extension `L(√a)/L` is unramified at `A`. -/
theorem kummerChar_eq_zero_of_isInertia_of_unit_base {L Ω : Type} [Field L] [NumberField L]
    [Field Ω] [Algebra L Ω] [IsAlgClosed Ω]
    (ζ : L) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace L A) (h2 : ¬ A.valuation (2 : Ω) < 1)
    (a : Lˣ) (ha : A.valuation (algebraMap L Ω (a : L)) = 1)
    (σ : Ω ≃ₐ[L] Ω) (hσ : SSGRoute.IsInertia L A σ) :
    Work.SSGRoute.kummerChar (K := L) (Ω := Ω) ζ hζ a σ = 0 := by
  -- A square root `γ` of the unit `a`; it is again a unit at `A`.
  set γ : Ω := Work.SSGRoute.kummerSqrtVal (Ω := Ω) a with hγdef
  have hγsq : γ ^ 2 = algebraMap L Ω (a : L) :=
    Work.SSGRoute.kummerSqrtVal_pow (Ω := Ω) a
  have hmem_a : algebraMap L Ω (a : L) ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff]; exact le_of_eq ha
  have hγA : γ ∈ A := by
    have hIC : IsIntegrallyClosedIn ↥A.toSubring Ω :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring hz
    have hint : IsIntegral ↥A.toSubring γ := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      rw [hγsq]
      exact isIntegral_algebraMap (x := (⟨algebraMap L Ω (a : L), hmem_a⟩ : ↥A.toSubring))
    exact (Subring.isIntegrallyClosedIn_iff.mp hIC) hint
  -- `2` is a unit at `A`, since `A ∤ 2`.
  have h2A : (2 : Ω) ∈ A := by
    have hh : (2 : Ω) = 1 + 1 := by norm_num
    rw [hh]; exact A.add_mem 1 1 A.one_mem A.one_mem
  have hval2_le : A.valuation (2 : Ω) ≤ 1 := (ValuationSubring.valuation_le_one_iff A _).mpr h2A
  have hval2 : A.valuation (2 : Ω) = 1 := le_antisymm hval2_le (not_lt.mp h2)
  -- `σ` fixes `a`, so `σ γ` is a square root of `a` as well.
  have hsq : (σ γ) ^ 2 = γ ^ 2 := by
    rw [← map_pow σ γ 2, hγsq]
    exact AlgEquiv.commutes σ (a : L)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · -- `σ γ = γ`: the Kummer character vanishes.
    refine Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq 2 hζ a
      (Work.SSGRoute.kummerSqrt (Ω := Ω) a) (Work.SSGRoute.kummerSqrt_pow (Ω := Ω) a) σ ?_
    simpa only [Work.SSGRoute.kummerSqrt, Units.val_mk0] using h
  · -- `σ γ = -γ`: the inertia condition would force `γ` to be non-integral, impossible.
    exfalso
    have hlt := hσ.2 γ hγA
    have hneg : σ γ - γ = -((2 : Ω) * γ) := by rw [h]; ring
    rw [hneg, Valuation.map_neg, Valuation.map_mul, hval2, one_mul] at hlt
    have heq : A.valuation γ * A.valuation γ = 1 := by
      rw [← Valuation.map_mul, ← pow_two, hγsq, ha]
    have hγpos : 0 < A.valuation γ := by
      rw [pos_iff_ne_zero]
      intro hz
      rw [hz] at heq
      simp only [zero_mul] at heq
      exact one_ne_zero heq.symm
    have hlt2 : A.valuation γ * A.valuation γ < 1 :=
      calc A.valuation γ * A.valuation γ < 1 * A.valuation γ :=
            mul_lt_mul_of_pos_right hlt hγpos
        _ = A.valuation γ := one_mul _
        _ < 1 := hlt
    rw [heq] at hlt2
    exact lt_irrefl 1 hlt2

/-! ## The main statement -/

theorem hilbertSymbolNegOneGlobal {L : Type} [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers L))
    (a : Lˣ) (ha : 𝔭.valuation L (a : L) = 1) :
    NK.NUV2.LC.hilbertSymbol (Work.SSGRoute.ZDataTwo.adicReciprocity L 𝔭)
        (Units.map (algebraMap L (𝔭.adicCompletion L)).toMonoidHom (-1 : Lˣ))
        (Units.map (algebraMap L (𝔭.adicCompletion L)).toMonoidHom a) = 1 := by
  -- A place `A` of the algebraic closure of `L` above `𝔭`.
  obtain ⟨A, hAcomap⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
    (K := L) (L := AlgebraicClosure L)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L 𝔭)
  have hA : SSGRoute.IsFinPlace L A := by
    show A.comap (algebraMap L (AlgebraicClosure L)) ≠ ⊤
    rw [hAcomap]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔭
  -- `2` is a unit at `A`
  have h2A : ¬ A.valuation (2 : AlgebraicClosure L) < 1 := by
    have h := place_valuation_lt_one_iff_base A 𝔭 hAcomap (2 : L)
    rw [map_ofNat (algebraMap L (AlgebraicClosure L)) 2] at h
    exact fun hlt => not_valuation_two_lt_one_of_isUnit 𝔭 h2 (h.mp hlt)
  -- `a` is a unit at `A`
  have haA : A.valuation (algebraMap L (AlgebraicClosure L) (a : L)) = 1 :=
    (place_valuation_eq_one_iff_base A 𝔭 hAcomap (a : L)).mpr ha
  -- `-1` is a unit at `A`
  have hnegA : A.valuation
      (algebraMap L (AlgebraicClosure L) ((-1 : Lˣ) : L)) = 1 := by
    refine (place_valuation_eq_one_iff_base A 𝔭 hAcomap ((-1 : Lˣ) : L)).mpr ?_
    have hcoe : ((-1 : Lˣ) : L) = (-1 : L) := by
      rw [show (-1 : Lˣ) = -(1 : Lˣ) from rfl, Units.val_neg, Units.val_one]
    rw [hcoe, Valuation.map_neg, Valuation.map_one]
  -- the two Kummer characters kill the inertia of `A`
  have hζ : IsPrimitiveRoot (-1 : L) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hkill_neg : ∀ σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L,
      SSGRoute.IsInertia L A σ →
        Work.SSGRoute.kummerChar (K := L) (Ω := AlgebraicClosure L) (-1 : L) hζ
          (-1 : Lˣ) σ = 0 :=
    fun σ hσ => kummerChar_eq_zero_of_isInertia_of_unit_base (-1 : L) hζ A hA h2A
      (-1 : Lˣ) hnegA σ hσ
  have hkill_a : ∀ σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L,
      SSGRoute.IsInertia L A σ →
        Work.SSGRoute.kummerChar (K := L) (Ω := AlgebraicClosure L) (-1 : L) hζ a σ = 0 :=
    fun σ hσ => kummerChar_eq_zero_of_isInertia_of_unit_base (-1 : L) hζ A hA h2A
      a haA σ hσ
  -- the finite pairing of `-1` and `a` at `𝔭` vanishes
  have hfp : Work.SSGRoute.ZDataTwo.finPair L 𝔭 (-1 : Lˣ) a = 0 :=
    Work.SSGRoute.ZDataTwo.finPairEqZeroOfKillsInertia L (AlgebraicClosure L) A hA h2A
      𝔭 hAcomap (-1 : L) hζ (-1 : Lˣ) a hkill_neg hkill_a
  rw [← Work.SSGRoute.ZDataTwo.toAdd_eq_zero_iff]
  exact hfp

end Work.SSGRoute.ZConstruction
