import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- If `f : V → ℂ` is not integrable (with respect to Lebesgue measure) on a finite-dimensional
real inner product space `V`, then its Fourier transform vanishes identically. This is because the
Fourier integral of `f` at `w` is convergent iff `f` itself is integrable, and the Bochner
integral of a non-integrable function is `0` by definition. -/
theorem fourier_eq_zero_of_not_integrable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] {f : V → ℂ}
    (hf : ¬ MeasureTheory.Integrable f MeasureTheory.volume) :
    FourierTransform.fourier f = 0 := by
  funext w
  rw [Real.fourier_eq]
  exact MeasureTheory.integral_undef
    (fun h => hf ((Real.fourierIntegral_convergent_iff (μ := MeasureTheory.volume) w).mp h))

end Commons.Analysis.Fourier