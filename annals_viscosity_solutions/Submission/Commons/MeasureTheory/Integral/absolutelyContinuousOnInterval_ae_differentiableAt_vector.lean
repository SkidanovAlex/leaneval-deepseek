import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.BoundedVariation

namespace Commons.MeasureTheory.Integral

open Filter Set MeasureTheory
open scoped Topology

/-- An absolutely continuous function on an interval `uIcc a b` with values in a finite-dimensional
real inner product space is differentiable at almost every point of that interval. -/
theorem absolutelyContinuousOnInterval_ae_differentiableAt_vector {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : ℝ → F} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ Set.uIcc a b → DifferentiableAt ℝ f x :=
  hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

end Commons.MeasureTheory.Integral
