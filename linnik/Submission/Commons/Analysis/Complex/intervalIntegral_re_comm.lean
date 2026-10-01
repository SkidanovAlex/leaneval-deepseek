import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Complex

lemma intervalIntegral_re_comm (f : ℝ → ℂ) (a b : ℝ) (hf : Continuous f) :
    (∫ t in a..b, (f t).re) = (∫ t in a..b, f t).re := by
  simpa using (intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hf.intervalIntegrable a b))

end Commons.Analysis.Complex