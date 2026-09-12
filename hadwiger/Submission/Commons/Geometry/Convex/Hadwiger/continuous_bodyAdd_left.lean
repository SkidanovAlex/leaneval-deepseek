import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_parallel_body_volume

namespace Commons.Geometry.Convex.Hadwiger

theorem continuous_bodyAdd_left {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] (L : ConvexBody V) :
    Continuous (fun K : ConvexBody V => K + L) := by
  exact continuous_add_left (V := V) L

end Commons.Geometry.Convex.Hadwiger
