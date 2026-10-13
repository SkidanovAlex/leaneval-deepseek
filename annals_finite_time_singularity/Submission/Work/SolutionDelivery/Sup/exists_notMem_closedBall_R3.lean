import Mathlib.Analysis.InnerProductSpace.PiL2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

/-- In a nontrivial normed space every closed ball is a proper subset: for any radius `R`
there is a vector whose distance from the origin exceeds `R`. -/
theorem exists_notMem_closedBall_R3 (R : ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin 3), x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ (EuclideanSpace ℝ (Fin 3)) R
  refine ⟨x, ?_⟩
  intro h
  have hle : ‖x‖ ≤ R := by
    simpa using Metric.mem_closedBall.mp h
  exact absurd hle (not_le.mpr hx)

end Work.SolutionDelivery.Sup
