import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct

open scoped Matrix

namespace Commons.Analysis.CrossProduct

/-- The cross product `u ⨯₃ v` is orthogonal to `u`: the scalar triple
product `u ⬝ (u ⨯₃ v)` vanishes. -/
theorem inner_cross3_self_left (u v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v)) u = 0 := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp

end Commons.Analysis.CrossProduct