import Mathlib
import Submission.Work.SilvermanReduction.Basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SilvermanReduction

open WeierstrassCurve
open scoped WithZero

set_option linter.style.haveILetI false

/-- If a Weierstrass equation over `K = Frac R` is integral over the discrete valuation ring `R`
and has discriminant of valuation `1` — the top of the value group `{v // v ≤ 1}` — then it has
good reduction at `R`: the map `C ↦ valuation_Δ_aux R (C • W)` takes values in `{v // v ≤ 1}`, so
its value `1` at `1` is automatically maximal, and `goodReduction` is the hypothesis. -/
theorem hasGoodReduction_of_valuation_Δ_eq_one' {K : Type*} [Field K]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K} [hW : W.IsIntegral R]
    (h : (IsDedekindDomain.HeightOneSpectrum.valuation K
      (IsDiscreteValuationRing.maximalIdeal R)) W.Δ = 1) : W.HasGoodReduction R := by
  have htop : (valuation_Δ_aux R W : ℤᵐ⁰) = 1 := by
    rw [valuation_Δ_aux_eq_of_isIntegral R W, h]
  haveI hmin : W.IsMinimal R := by
    refine ⟨⟨?_, ?_⟩⟩
    · simpa only [one_smul] using hW
    · intro j _ _
      have h1 : valuation_Δ_aux R ((1 : VariableChange K) • W) = valuation_Δ_aux R W := by
        rw [one_smul]
      change (valuation_Δ_aux R (j • W) : ℤᵐ⁰) ≤
        (valuation_Δ_aux R ((1 : VariableChange K) • W) : ℤᵐ⁰)
      rw [h1, htop]
      exact (valuation_Δ_aux R (j • W)).2
  exact ⟨h⟩

/-- **Good reduction is stable under a base change of discrete valuation rings which is the local
model of a place.**  Let `K` be the fraction field of the discrete valuation ring `R`, `L` the
fraction field of the discrete valuation ring `S`, with compatible algebra structures (`R → S`,
`R → L`, `S → L`).  If a Weierstrass curve `W/K` has good reduction at `R`, then its base change
to `L` has good reduction at `S`.

The proof is the unit-discriminant argument: `Δ_W` is a unit of `R` (its valuation is `1`, the top
of the value group `{v // v ≤ 1}`), and any ring homomorphism sends units to units, so the image of
`Δ_W` in `S` is a unit; hence `W.baseChange L` is integral over `S` with unit discriminant, which
gives both `IsMinimal` (`WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral` and `MaximalFor` at the
top value) and `goodReduction`.  This is the step that lifts the good reduction of the Tate normal
form at `5` over `ℤ_(5)` to the place of the cyclotomic quintic field `L ⊂ ℚ(ζ₂₅)`
(`tateCurve_hasGoodReduction` supplies the input over `ℤ_(5)`). -/
theorem hasGoodReduction_baseChange {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K]
    (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [Algebra R S] [IsScalarTower R K L] [IsScalarTower R S L]
    {W : WeierstrassCurve.Affine K} (h : W.HasGoodReduction R) :
    (W.baseChange L).HasGoodReduction S := by
  haveI hMin : W.IsMinimal R := h.toIsMinimal
  -- the discriminant of `W` is the image of a unit of `R`
  obtain ⟨r, hr⟩ := WeierstrassCurve.Δ_integral_of_isIntegral R W
  have hvalR : (IsDedekindDomain.HeightOneSpectrum.valuation K
      (IsDiscreteValuationRing.maximalIdeal R)) W.Δ = 1 := h.goodReduction
  have hrunit : IsUnit r := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    refine (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (v := IsDiscreteValuationRing.maximalIdeal R) (K := K) (r := r)).mp ?_
    rw [hr]
    exact hvalR
  -- `W.baseChange L` is integral over `S`
  haveI hIntL : (W.baseChange L).IsIntegral S := by
    refine ⟨WeierstrassCurve.map (WeierstrassCurve.integralModel R W) (algebraMap R S), ?_⟩
    show WeierstrassCurve.map W (algebraMap K L)
      = WeierstrassCurve.map
          (WeierstrassCurve.map (WeierstrassCurve.integralModel R W) (algebraMap R S))
          (algebraMap S L)
    have hWmap : W
        = WeierstrassCurve.map (WeierstrassCurve.integralModel R W) (algebraMap R K) :=
      (WeierstrassCurve.baseChange_integralModel_eq R W).symm
    conv_lhs => rw [hWmap]
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
      ← IsScalarTower.algebraMap_eq R K L, ← IsScalarTower.algebraMap_eq R S L]
  -- and its discriminant has valuation `1` at `S`
  have hvalL : (IsDedekindDomain.HeightOneSpectrum.valuation L
      (IsDiscreteValuationRing.maximalIdeal S)) (W.baseChange L).Δ = 1 := by
    show (IsDedekindDomain.HeightOneSpectrum.valuation L
      (IsDiscreteValuationRing.maximalIdeal S))
        (WeierstrassCurve.map W (algebraMap K L)).Δ = 1
    rw [WeierstrassCurve.map_Δ, ← hr, ← IsScalarTower.algebraMap_apply R K L r,
      IsScalarTower.algebraMap_apply R S L r]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (v := IsDiscreteValuationRing.maximalIdeal S) (K := L)
      (r := algebraMap R S r)).mpr
        (IsLocalRing.notMem_maximalIdeal.mpr (hrunit.map (algebraMap R S)))
  exact hasGoodReduction_of_valuation_Δ_eq_one' (K := L) (R := S)
    (W := W.baseChange L) hvalL

end Work.SilvermanReduction
