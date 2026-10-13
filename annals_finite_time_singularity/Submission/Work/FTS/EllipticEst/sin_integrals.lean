import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Elliptic.integral_sinCos2_mul_sin_two
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Work.FTS.EllipticEst

/-! ## The elementary angular integrals of the elliptic estimates

The four integrals of `Work.FTS.EllipticEst.sin_integrals` are reduced to the standard interval
integrals of Mathlib (`integral_sin_sq`, `integral_cos_sq`, `integral_cos_pow`) by

* the substitution `θ ↦ 2θ` (`intervalIntegral.integral_comp_mul_left`) and the double-angle
  identities `Real.sin_sq_eq_half_sub`, `Real.cos_sq` for the first two integrals;
* the identities `sin²θ cos⁴θ = cos⁴θ - cos⁶θ` (from `Real.sin_sq`) together with the reduction
  formulae for `∫ cos⁴`, `∫ cos⁶` for the third;
* the already delivered `Work.Elliptic.integral_sin_two_mul_sinCos2` for the fourth.
-/

/-- `∫_0^{π/2} cos⁴θ dθ = 3π/16`, by the reduction formula for `∫ cos^n`. -/
private lemma integral_cos_four : (∫ θ in (0:ℝ)..(π/2), Real.cos θ ^ 4) = 3 * π / 16 := by
  rw [integral_cos_pow (a := (0:ℝ)) (b := π/2) (n := 2), integral_cos_sq]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  ring

/-- `∫_0^{π/2} cos⁶θ dθ = 5π/32`, by the reduction formula for `∫ cos^n` and `integral_cos_four`. -/
private lemma integral_cos_six : (∫ θ in (0:ℝ)..(π/2), Real.cos θ ^ 6) = 5 * π / 32 := by
  rw [integral_cos_pow (a := (0:ℝ)) (b := π/2) (n := 4), integral_cos_four]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  ring

/-- `∫_0^{π/2} sin²(2θ) dθ = π/4`: substitute `u = 2θ` and use `integral_sin_sq`. -/
private lemma integral_sin_two_sq : (∫ θ in (0:ℝ)..(π/2), (Real.sin (2 * θ)) ^ 2) = π / 4 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2)
    (by norm_num : (2:ℝ) ≠ 0)]
  rw [show (2:ℝ) * 0 = 0 by ring, show (2:ℝ) * (π/2) = π by ring]
  simp only [smul_eq_mul]
  rw [integral_sin_sq, Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi]
  ring

/-- `∫_0^{π/2} (2cos(2θ))² dθ = π`: substitute `u = 2θ` and use `integral_cos_sq`. -/
private lemma integral_two_cos_two_sq :
    (∫ θ in (0:ℝ)..(π/2), (2 * Real.cos (2 * θ)) ^ 2) = π := by
  have hpt : ∀ θ : ℝ, (2 * Real.cos (2 * θ)) ^ 2 = 4 * Real.cos (2 * θ) ^ 2 := by
    intro θ; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x ^ 2)
    (by norm_num : (2:ℝ) ≠ 0)]
  rw [show (2:ℝ) * 0 = 0 by ring, show (2:ℝ) * (π/2) = π by ring]
  simp only [smul_eq_mul]
  rw [integral_cos_sq, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero]
  ring

/-- `∫_0^{π/2} (sinθcos²θ)² dθ = π/32`: since `sin²θ cos⁴θ = cos⁴θ - cos⁶θ`, this is
`3π/16 - 5π/32`. -/
private lemma integral_sinCos2_sq :
    (∫ θ in (0:ℝ)..(π/2), (Work.Elliptic.sinCos2 θ) ^ 2) = π / 32 := by
  have hpt : ∀ θ : ℝ, (Work.Elliptic.sinCos2 θ) ^ 2 = Real.cos θ ^ 4 - Real.cos θ ^ 6 := by
    intro θ
    simp only [Work.Elliptic.sinCos2]
    rw [show (Real.sin θ * Real.cos θ ^ 2) ^ 2 = Real.sin θ ^ 2 * (Real.cos θ ^ 2) ^ 2 by
      ring, Real.sin_sq]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  have hsub : (∫ x in (0:ℝ)..(π/2), Real.cos x ^ 4 - Real.cos x ^ 6)
      = (∫ x in (0:ℝ)..(π/2), Real.cos x ^ 4) - (∫ x in (0:ℝ)..(π/2), Real.cos x ^ 6) :=
    intervalIntegral.integral_sub ((Real.continuous_cos.pow 4).intervalIntegrable _ _)
      ((Real.continuous_cos.pow 6).intervalIntegrable _ _)
  rw [hsub, integral_cos_four, integral_cos_six]
  ring

/-- `∫_0^{π/2} sinθcos²θ · sin2θ dθ = 4/15`, transported from the delivered set-integral form
`Work.Elliptic.integral_sin_two_mul_sinCos2` over `Work.Spaces.Iθ`. -/
private lemma integral_sinCos2_mul_sin_two :
    (∫ θ in (0:ℝ)..(π/2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ)) = 4 / 15 := by
  have hIθ : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * θ))
      = ∫ θ in (0:ℝ)..(π/2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) := by
    change ∫ θ in Set.Icc 0 (π/2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) = _
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  have hcomm : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * θ))
      = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ :=
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [← hIθ, hcomm, Work.Elliptic.integral_sin_two_mul_sinCos2]

theorem sin_integrals :
    (∫ θ in (0:ℝ)..(π / 2), (Real.sin (2 * θ)) ^ 2 = π / 4) ∧
    (∫ θ in (0:ℝ)..(π / 2), (2 * Real.cos (2 * θ)) ^ 2 = π) ∧
    (∫ θ in (0:ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2 = π / 32) ∧
    (∫ θ in (0:ℝ)..(π / 2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) = 4 / 15) :=
  ⟨integral_sin_two_sq, integral_two_cos_two_sq, integral_sinCos2_sq,
    integral_sinCos2_mul_sin_two⟩

end Work.FTS.EllipticEst
