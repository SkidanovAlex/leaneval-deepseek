import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory
open scoped Real

namespace Commons.Measure.Integral

/-- The real Gaussian `v ↦ exp (−b·‖v‖²)` is integrable w.r.t. volume on any
finite-dimensional real inner product space `V`, for every decay rate `b > 0`. -/
theorem integrable_rexp_neg_mul_sq_norm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (b : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun v : V => Real.exp (-b * ‖v‖ ^ 2)) MeasureTheory.volume := by
  -- The complex Gaussian `v ↦ exp (−b·‖v‖²)` (viewed in `ℂ`) is integrable on `V`
  -- by the general Fourier-transform integrability lemma in Mathlib.
  have hB : 0 < (b : ℂ).re := by simpa using hb
  have hc : MeasureTheory.Integrable
      (fun v : V => Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)) MeasureTheory.volume := by
    simpa using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (b : ℂ)) hB (0 : ℂ) (0 : V))
  -- The modulus of the complex Gaussian is exactly our real integrand, since
  -- `‖exp z‖ = exp (z.re)` and the argument is purely real.
  refine hc.norm.congr ?_
  refine ae_of_all _ ?_
  intro v
  change ‖Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)‖ = Real.exp (-b * ‖v‖ ^ 2)
  rw [Complex.norm_exp]
  congr 1
  have hpow : (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by norm_num
  rw [hpow]
  rw [neg_mul]
  rw [← Complex.ofReal_mul]
  rw [Complex.neg_re, Complex.ofReal_re]
  ring

end Commons.Measure.Integral