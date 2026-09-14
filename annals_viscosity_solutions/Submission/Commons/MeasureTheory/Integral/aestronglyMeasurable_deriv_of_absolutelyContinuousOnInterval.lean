import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

namespace Commons.MeasureTheory.Integral

theorem aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    MeasureTheory.AEStronglyMeasurable (deriv f)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
  exact aestronglyMeasurable_deriv f _

end Commons.MeasureTheory.Integral