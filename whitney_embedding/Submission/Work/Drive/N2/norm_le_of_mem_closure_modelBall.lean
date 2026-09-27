import Mathlib
import Submission.Work.Drive.N2.modelBall

namespace Work.Drive.N2

open Set Topology

theorem norm_le_of_mem_closure_modelBall {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ)
    (hsub : closure (Work.Drive.N2.modelBall φ r) ⊆ φ.source) :
    ∀ z ∈ closure (Work.Drive.N2.modelBall φ r), ‖φ z‖ ≤ r := by
  intro z hz
  -- `φ` is continuous on its source, hence on the closure of the model ball.
  have hcont : ContinuousOn φ (closure (modelBall φ r)) := φ.continuousOn.mono hsub
  -- the image of the closure is contained in the closure of the image
  have himg : φ '' closure (modelBall φ r) ⊆ closure (φ '' modelBall φ r) :=
    hcont.image_closure
  have hz' : φ z ∈ closure (φ '' modelBall φ r) := himg ⟨z, hz, rfl⟩
  -- on the model ball the norm is `< r`, so the image lies in the closed ball
  have hsub2 : φ '' modelBall φ r ⊆ Metric.closedBall 0 r := by
    rintro w ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hy.2
  have hcl : closure (φ '' modelBall φ r) ⊆ Metric.closedBall 0 r :=
    closure_minimal hsub2 Metric.isClosed_closedBall
  have := hcl hz'
  rwa [Metric.mem_closedBall, dist_zero_right] at this

end Work.Drive.N2
