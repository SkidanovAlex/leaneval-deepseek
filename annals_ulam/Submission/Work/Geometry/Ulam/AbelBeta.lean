import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

noncomputable section

open scoped Interval
open MeasureTheory Set Filter

namespace Commons.Geometry.Ulam

/-- The elementary Abel kernel integral `∫_0^1 dτ / √(τ(1-τ)) = π`. -/
lemma integral_one_div_sqrt_tau_one_sub_tau_eq_pi :
    (∫ τ in (0 : ℝ)..(1 : ℝ), 1 / Real.sqrt (τ * ((1 : ℝ) - τ))) = Real.pi := by
  let f : ℝ → ℝ := fun u => 1 / Real.sqrt (1 - u ^ 2)
  have hcomp :
      (∫ τ in (0 : ℝ)..(1 : ℝ), f (2 * τ - 1)) =
        (1 / 2 : ℝ) * ∫ u in (-1 : ℝ)..(1 : ℝ), f u := by
    have h := intervalIntegral.integral_comp_mul_add (f := f) (a := (0:ℝ)) (b := (1:ℝ))
      (c := 2) (d := -1) (by norm_num : (2:ℝ) ≠ 0)
    change (∫ τ in (0 : ℝ)..(1 : ℝ), f (2 * τ + -1)) =
        (2 : ℝ)⁻¹ * ∫ u in (2 * 0 + -1)..(2 * 1 + -1), f u at h
    rw [show (2:ℝ)⁻¹ = 1 / 2 by norm_num,
        show 2 * (0:ℝ) + -1 = -1 by norm_num,
        show 2 * (1:ℝ) + -1 = 1 by norm_num] at h
    simpa [sub_eq_add_neg] using h
  have hpoint : ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
      1 / Real.sqrt (τ * ((1 : ℝ) - τ)) = 2 * f (2 * τ - 1) := by
    intro τ hτ
    have hτ0 : 0 < τ := hτ.1
    have hτ1 : τ < 1 := hτ.2
    have hA_pos : 0 < τ * ((1 : ℝ) - τ) := by positivity
    have hA_ne : τ * ((1 : ℝ) - τ) ≠ 0 := ne_of_gt hA_pos
    have hsqrt4 : Real.sqrt (4 * (τ * ((1 : ℝ) - τ))) =
        2 * Real.sqrt (τ * ((1 : ℝ) - τ)) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (τ * ((1 : ℝ) - τ))]
      have hsqrt4' : Real.sqrt (4:ℝ) = 2 := by norm_num [Real.sqrt]
      rw [hsqrt4']
    have harg : 1 - (2 * τ - 1) ^ 2 = 4 * (τ * ((1 : ℝ) - τ)) := by ring
    dsimp [f]
    rw [harg, hsqrt4]
    field_simp [hA_ne]
  have hcongr : (∫ τ in (0 : ℝ)..(1 : ℝ), 1 / Real.sqrt (τ * ((1 : ℝ) - τ))) =
      ∫ τ in (0 : ℝ)..(1 : ℝ), 2 * f (2 * τ - 1) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)
    intro τ hτ
    exact hpoint τ hτ
  have htwo_mul : (∫ τ in (0 : ℝ)..(1 : ℝ), 2 * f (2 * τ - 1)) =
      2 * (∫ τ in (0 : ℝ)..(1 : ℝ), f (2 * τ - 1)) := by
    rw [intervalIntegral.integral_const_mul]
  have hmain : (∫ u in (-1 : ℝ)..(1 : ℝ), f u) = Real.pi := by
    dsimp [f]
    have hcont_arcsin : ContinuousOn Real.arcsin (Set.uIcc (-1 : ℝ) 1) := by
      exact Real.continuous_arcsin.continuousOn
    have hderiv_interior : ∀ x ∈ Set.uIoo (-1 : ℝ) 1, DifferentiableAt ℝ Real.arcsin x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by
        simpa [Set.uIoo_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hx
      have hx1 : x ≠ -1 := by
        intro h; rw [h] at hx'; exact (lt_irrefl _) hx'.1
      have hx2 : x ≠ 1 := by
        intro h; rw [h] at hx'; exact (lt_irrefl _) hx'.2
      exact (Real.hasDerivAt_arcsin hx1 hx2).differentiableAt
    have hderiv_eq : deriv Real.arcsin = fun x => 1 / Real.sqrt (1 - x ^ 2) := by
      simpa using Real.deriv_arcsin
    have hint : IntervalIntegrable (deriv Real.arcsin) volume (-1 : ℝ) 1 := by
      rw [hderiv_eq]
      simpa using Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
    calc
      (∫ u in (-1 : ℝ)..(1 : ℝ), 1 / Real.sqrt (1 - u ^ 2))
          = ∫ u in (-1 : ℝ)..(1 : ℝ), deriv Real.arcsin u := by
              apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (-1:ℝ) ≤ 1)
              intro u hu
              rw [hderiv_eq]
      _ = Real.arcsin 1 - Real.arcsin (-1) := by
              rw [intervalIntegral.integral_deriv_eq_sub_uIoo hcont_arcsin hderiv_interior hint]
      _ = Real.pi := by
              rw [Real.arcsin_one, Real.arcsin_neg_one]
              ring
  rw [hcongr, htwo_mul, hcomp, hmain]
  ring

end Commons.Geometry.Ulam
