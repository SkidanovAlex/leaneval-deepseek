import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Commons.Measure.Integral

/-- On a finite-dimensional real inner product space the real Gaussian
`exp (-b * ‖x‖²)` is Lebesgue integrable for every `b > 0`. -/
private lemma integrable_exp_neg_mul_sq_norm_aux
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {b : ℝ} (hb : 0 < b) :
    MeasureTheory.Integrable (fun x : V => Real.exp (-b * ‖x‖ ^ 2)) MeasureTheory.volume := by
  have hbc : 0 < (b : ℂ).re := by simpa using hb
  have Hc : Integrable (fun x : V => cexp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2)) volume := by
    simpa using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hbc (0 : ℂ) (0 : V))
  have Hnorm := Hc.norm
  refine MeasureTheory.Integrable.congr Hnorm ?_
  filter_upwards with x
  rw [show (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) = ((-b * ‖x‖ ^ 2 : ℝ) : ℂ) by norm_num]
  exact Complex.norm_exp_ofReal (-b * ‖x‖ ^ 2)

theorem integrable_exp_neg_mul_sq_norm_scaled
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {b : ℝ} (hb : 0 < b) (c : ℝ) (hc : c ≠ 0) :
    MeasureTheory.Integrable (fun x : V => Real.exp (-b * ‖c⁻¹ • x‖ ^ 2)) MeasureTheory.volume := by
  have hcsub : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hcpos : (0 : ℝ) < (c⁻¹) ^ 2 := sq_pos_of_ne_zero hcsub
  have hβ : 0 < b * (c⁻¹) ^ 2 := mul_pos hb hcpos
  have H := integrable_exp_neg_mul_sq_norm_aux (V := V) (b := b * (c⁻¹) ^ 2) hβ
  refine MeasureTheory.Integrable.congr H ?_
  filter_upwards with x
  congr 1
  have hnormx : ‖c⁻¹ • x‖ ^ 2 = (c⁻¹) ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖c⁻¹ • x‖ ^ 2 = (‖c⁻¹‖ * ‖x‖) ^ 2 := by rw [norm_smul]
      _ = ‖c⁻¹‖ ^ 2 * ‖x‖ ^ 2 := by rw [mul_pow]
      _ = |c⁻¹| ^ 2 * ‖x‖ ^ 2 := by rw [Real.norm_eq_abs]
      _ = (c⁻¹) ^ 2 * ‖x‖ ^ 2 := by rw [sq_abs]
  rw [hnormx]
  ring

end Commons.Measure.Integral