import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Integral

open MeasureTheory

/-- The Fourier integral `x ↦ ∫ ξ, e^{2πi x ξ} • V ξ` of an integrable `H`-valued function
`V` is continuous.  This is the dominated-convergence continuity of the Fourier transform of an
`L¹` function: for each fixed `ξ` the phase `x ↦ e^{2πi x ξ}` is continuous, and it has modulus
`1`, so it is dominated by the integrable function `ξ ↦ ‖V ξ‖`. -/
theorem continuous_integral_czE_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (V : ℝ → H) (hV : MeasureTheory.Integrable V) :
    Continuous (fun x : ℝ => ∫ ξ : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (x * ξ)) • V ξ) := by
  -- Rewrite the phase as `(2πxξ : ℝ) * I` inside `ℂ`, so that its modulus is `1`.
  have hchar : ∀ x ξ : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * (x * ξ))
        = Complex.exp (((2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) := by
    intro x ξ
    congr 1
    push_cast
    ring
  have hnorm : ∀ x ξ : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (x * ξ))‖ = 1 := by
    intro x ξ
    rw [hchar x ξ, Complex.norm_exp_ofReal_mul_I]
  refine MeasureTheory.continuous_of_dominated
    (F := fun x : ℝ => fun ξ : ℝ => Complex.exp (2 * Real.pi * Complex.I * (x * ξ)) • V ξ)
    (bound := fun ξ : ℝ => ‖V ξ‖) ?_ ?_ ?_ ?_
  · intro x
    exact (Continuous.aestronglyMeasurable (by fun_prop : Continuous
      (fun ξ : ℝ => Complex.exp (2 * Real.pi * Complex.I * (x * ξ))))).smul hV.1
  · intro x
    filter_upwards with ξ
    rw [norm_smul, hnorm x ξ, one_mul]
  · exact hV.norm
  · filter_upwards with ξ
    exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (x * ξ)) • V ξ))

end Commons.Analysis.Integral