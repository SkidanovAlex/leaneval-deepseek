import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.TorsorExistence.Tate.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped WithZero
open WeierstrassCurve

namespace Work.SilvermanReduction

/-! ## A general criterion: `val Δ = 1` forces minimality and good reduction -/

/-- If an integral Weierstrass equation over `K = Frac R` has discriminant of the *maximal*
possible valuation `1`, then it is minimal: the map
`C ↦ valuation_Δ_aux R (C • W)` takes values in `{v // v ≤ 1}`, so the value at `1` — which is
`1`, the top element — is automatically maximal. -/
theorem isMinimal_of_valuation_Δ_eq_one {K : Type} [Field K]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K} [hW : W.IsIntegral R]
    (h : (IsDedekindDomain.HeightOneSpectrum.valuation K
      (IsDiscreteValuationRing.maximalIdeal R)) W.Δ = 1) : W.IsMinimal R := by
  have htop : (valuation_Δ_aux R W : ℤᵐ⁰) = 1 := by
    rw [valuation_Δ_aux_eq_of_isIntegral, h]
  refine ⟨⟨?_, ?_⟩⟩
  · simpa only [one_smul] using hW
  · intro j _ _
    have h1 : valuation_Δ_aux R ((1 : VariableChange K) • W) = valuation_Δ_aux R W := by
      rw [one_smul]
    change (valuation_Δ_aux R (j • W) : ℤᵐ⁰) ≤
      (valuation_Δ_aux R ((1 : VariableChange K) • W) : ℤᵐ⁰)
    rw [h1, htop]
    exact (valuation_Δ_aux R (j • W)).2

/-- If an integral Weierstrass equation over `K = Frac R` has discriminant of valuation `1`, then
it has good reduction at the place. -/
theorem hasGoodReduction_of_valuation_Δ_eq_one {K : Type} [Field K]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K} [hW : W.IsIntegral R]
    (h : (IsDedekindDomain.HeightOneSpectrum.valuation K
      (IsDiscreteValuationRing.maximalIdeal R)) W.Δ = 1) : W.HasGoodReduction R := by
  haveI : W.IsMinimal R := isMinimal_of_valuation_Δ_eq_one R h
  exact ⟨h⟩

/-! ## The Tate normal form -/

/-- **The Tate normal form has good reduction when its discriminant is a unit.**
Let `R` be a discrete valuation ring with fraction field `K`, and let `c ∈ R` be such that both
`c` and `c² - 11c - 1` are units of `R`.  Then the Tate normal form
`y² + (1-c)xy - cy = x³ - cx²` over `K` has good reduction at the place, because its discriminant
`Δ = c⁵(c² - 11c - 1)` is a unit.

For `R = ℤ_(5)` (the valuation ring of the place `5` of `ℚ`) and `c ∈ ℤ` with `5 ∤ c` and
`5 ∤ c² - 11c - 1` — e.g. `c = 1`, where `c² - 11c - 1 = -11 ≡ 4 mod 5` — this is the concrete
input of the number-field class (a) of Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. 199 (1), 2024, Theorem 1.2: with these hypotheses the point `(0,0)` of order `5`
reduces to a nonsingular point of `Ẽ(𝔽₅)`, so the reduction of the marked point is non-zero.

Proof route: `Work.TorsorExistence.Tate.tateCurve_Δ` computes the discriminant, multiplicativity of
the valuation gives `val Δ = 1` (the maximal possible value: the codomain of
`WeierstrassCurve.valuation_Δ_aux` is the subtype `{v // v ≤ 1}`), which yields both
`IsMinimal` (`WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral` plus `MaximalFor` of the top
value) and `goodReduction`. -/
theorem tateCurve_hasGoodReduction {K : Type} [Field K]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] (c : R) (hc : IsUnit c)
    (hΔ : IsUnit (c ^ 2 - 11 * c - 1)) :
    WeierstrassCurve.HasGoodReduction R
      (Work.TorsorExistence.Tate.tateCurve (algebraMap R K c)) := by
  -- The Tate coefficients are the images of the coefficients `1 - c, -c, -c, 0, 0 ∈ R`.
  haveI hInt : WeierstrassCurve.IsIntegral R
      (Work.TorsorExistence.Tate.tateCurve (algebraMap R K c)) := by
    apply WeierstrassCurve.isIntegral_of_exists_lift R
    · exact ⟨1 - c, by simp [Work.TorsorExistence.Tate.tateCurve]⟩
    · exact ⟨-c, by simp [Work.TorsorExistence.Tate.tateCurve]⟩
    · exact ⟨-c, by simp [Work.TorsorExistence.Tate.tateCurve]⟩
    · exact ⟨0, by simp [Work.TorsorExistence.Tate.tateCurve]⟩
    · exact ⟨0, by simp [Work.TorsorExistence.Tate.tateCurve]⟩
  -- `Δ = (algebraMap c)^5 * ((algebraMap c)^2 - 11 * algebraMap c - 1)` is the image of the unit
  -- `c^5 * (c^2 - 11*c - 1)`, hence has valuation `1`.
  have hval : (IsDedekindDomain.HeightOneSpectrum.valuation K
      (IsDiscreteValuationRing.maximalIdeal R))
      (Work.TorsorExistence.Tate.tateCurve (algebraMap R K c)).Δ = 1 := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ]
    have hmap : (algebraMap R K c) ^ 5 * ((algebraMap R K c) ^ 2 - 11 * algebraMap R K c - 1)
        = algebraMap R K (c ^ 5 * (c ^ 2 - 11 * c - 1)) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
    rw [hmap, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.notMem_maximalIdeal]
    exact (hc.pow 5).mul hΔ
  exact hasGoodReduction_of_valuation_Δ_eq_one R hval

end Work.SilvermanReduction
