import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped Interval

namespace Commons.MeasureTheory.Integral

/-- Cauchy--Schwarz for the Bochner integral on a finite measure space: the square of the integral
of `f` is at most the product of the integral of `f²` and the total mass of the measure. -/
theorem sq_integral_le_integral_sq_mul_measure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * μ.real Set.univ := by
  have hquad : ∀ t : ℝ,
      0 ≤ (∫ x, f x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, f x ∂μ) * t + μ.real Set.univ := by
    intro t
    have hI1 : Integrable (fun x : α => t ^ 2 * (f x) ^ 2) μ := hf2.const_mul (t ^ 2)
    have hI2 : Integrable (fun x : α => (2 * t) * f x) μ := hf.const_mul (2 * t)
    have hI12 : Integrable (fun x : α => t ^ 2 * (f x) ^ 2 + (2 * t) * f x) μ := hI1.add hI2
    have hI3 : Integrable (fun _ : α => (1 : ℝ)) μ := integrable_const 1
    have hnn : 0 ≤ ∫ x, (t * f x + 1) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have hval : ∫ x, (t * f x + 1) ^ 2 ∂μ
        = (∫ x, f x ^ 2 ∂μ) * t ^ 2 + (∫ x, f x ∂μ) * (2 * t) + μ.real Set.univ := by
      calc ∫ x, (t * f x + 1) ^ 2 ∂μ
          = ∫ x, t ^ 2 * (f x) ^ 2 + (2 * t) * f x + 1 ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
        _ = (∫ x, t ^ 2 * (f x) ^ 2 + (2 * t) * f x ∂μ) + (∫ x, (1 : ℝ) ∂μ) :=
            integral_add hI12 hI3
        _ = ((∫ x, t ^ 2 * (f x) ^ 2 ∂μ) + (∫ x, (2 * t) * f x ∂μ))
              + (∫ x, (1 : ℝ) ∂μ) := by
            have h := integral_add hI1 hI2
            rw [h]
        _ = (t ^ 2 * (∫ x, f x ^ 2 ∂μ) + (2 * t) * (∫ x, f x ∂μ))
              + μ.real Set.univ := by
            rw [integral_const_mul, integral_const_mul, integral_const, smul_eq_mul, mul_one]
        _ = (∫ x, f x ^ 2 ∂μ) * t ^ 2 + (∫ x, f x ∂μ) * (2 * t) + μ.real Set.univ := by
            ring
    rw [hval] at hnn
    nlinarith [hnn]
  have hd : discrim (∫ x, f x ^ 2 ∂μ) (2 * ∫ x, f x ∂μ) (μ.real Set.univ) ≤ 0 :=
    discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

theorem sq_interval_integral_le_len_mul_integral_sq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun x => (f x)^2) (Set.Icc a b)) :
    (∫ x in a..b, f x)^2 ≤ (b - a) * ∫ x in a..b, (f x)^2 := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hf2 : IntegrableOn (fun x => (f x)^2) (Set.Ioc a b) :=
    hf.mono_set Set.Ioc_subset_Icc_self
  have hfin : (volume : Measure ℝ) (Set.Ioc a b) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hfininst : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := isFiniteMeasure_restrict.2 hfin
  have hC : (volume.restrict (Set.Ioc a b)).real Set.univ = b - a := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  by_cases hint : Integrable f (volume.restrict (Set.Ioc a b))
  · have hCS := sq_integral_le_integral_sq_mul_measure hint hf2
    rw [hC, mul_comm] at hCS
    exact hCS
  · rw [integral_undef hint]
    have hnn : 0 ≤ ∫ x in Set.Ioc a b, (f x)^2 := integral_nonneg (fun x => sq_nonneg (f x))
    have hmul := mul_nonneg (sub_nonneg.mpr hab) hnn
    simpa using hmul

end Commons.MeasureTheory.Integral