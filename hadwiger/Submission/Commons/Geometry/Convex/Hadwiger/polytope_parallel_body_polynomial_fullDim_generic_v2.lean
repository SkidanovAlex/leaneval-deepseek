import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_parallel_body_polynomial_fullDim_generic_v4

open scoped Pointwise

namespace Commons.Geometry.Convex.Hadwiger

/-- The parallel-body volume of a full-dimensional polytope is given by a polynomial of
degree at most `finrank ℝ V` on `t ≥ 0` (Steiner's formula for polytopes, generic version). -/
theorem polytope_parallel_body_polynomial_fullDim_generic_v2
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) (hPint : (interior P).Nonempty) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ Module.finrank ℝ V ∧
      ∀ t : ℝ, 0 ≤ t →
        (MeasureTheory.volume (P + t • Metric.closedBall (0 : V) 1)).toReal = p.eval t :=
  polytope_parallel_body_polynomial_fullDim_generic_v4 u P hP hPint

end Commons.Geometry.Convex.Hadwiger
