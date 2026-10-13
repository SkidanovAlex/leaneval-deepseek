import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

/-- The Gaussian integral on `ℝ³` with a positive quadratic coefficient:
`∫ z : ℝ³, exp (-(a‖z‖²)) = (π/a)^{3/2}` for `a > 0`.

The type `R3 = EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`, and `WithLp.toLp 2` is volume
preserving, so the integral factorises over the three coordinates; each one-dimensional factor is
the classical Gaussian integral `∫ x, exp (-a x²) = √(π/a)`. -/
private lemma integral_exp_neg_mul_normSq (a : ℝ) (ha : 0 < a) :
    ∫ z : R3, Real.exp (-(a * ‖z‖ ^ 2)) = (Real.pi / a) ^ (3 / 2 : ℝ) := by
  -- Move from `EuclideanSpace ℝ (Fin 3)` to `Fin 3 → ℝ` (volume preserving).
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (fun z : R3 => Real.exp (-(a * ‖z‖ ^ 2)))]
  -- Write the Gaussian as a product over the three coordinates.
  have hpoint : (fun x : Fin 3 → ℝ =>
        Real.exp (-(a * ‖(WithLp.toLp 2 x : R3)‖ ^ 2)))
      = fun x => ∏ i, Real.exp (-(a * (x i) ^ 2)) := by
    funext x
    rw [← Real.exp_sum]
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hpoint]
  -- Fubini in three variables.
  rw [integral_fintype_prod_volume_eq_pow (f := fun x : ℝ => Real.exp (-(a * x ^ 2)))]
  rw [Fintype.card_fin]
  -- The one-dimensional Gaussian integral, and `(√(π/a))³ = (π/a)^{3/2}`.
  have h1 : (∫ x : ℝ, Real.exp (-(a * x ^ 2))) = Real.sqrt (Real.pi / a) := by
    simpa only [neg_mul] using integral_gaussian a
  have h3 : (Real.sqrt (Real.pi / a)) ^ (3 : ℕ) = (Real.pi / a) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((Real.pi / a) ^ (1 / 2 : ℝ)) 3]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.pi / a) (1 / 2) ((3 : ℕ) : ℝ)]
    rw [show (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) = 3 / 2 by norm_num]
  rw [h1, h3]

theorem integral_heatKernel (t : ℝ) (ht : 0 < t) :
    ∫ z : Work.FTS.PressureOn.R3, Work.FTS.PressureOn.Auxiliary.heatKernel t z = 1 := by
  have ht4 : (0 : ℝ) < 4 * t := by linarith
  have ha : (0 : ℝ) < (4 * t)⁻¹ := inv_pos.mpr ht4
  -- Pull out the constant prefactor and write the exponent as `-(a‖z‖²)`.
  have hsplit : ∫ z : R3, heatKernel t z =
      (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        ∫ z : R3, Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    exact heatKernel_eq_const_mul_exp ht z
  rw [hsplit, integral_exp_neg_mul_normSq ((4 * t)⁻¹) ha]
  -- `π / (4t)^{-1} = 4πt`, and `x^{-3/2} x^{3/2} = 1`.
  have hpi : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by
    rw [div_inv_eq_mul]
    ring
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  rw [hpi, Real.rpow_neg hpos.le (3 / 2 : ℝ)]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hpos (3 / 2 : ℝ)))

end Work.FTS.PressureOn.Auxiliary
