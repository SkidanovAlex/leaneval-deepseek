import ChallengeDeps
import Submission.Commons.Geometry.Convex.Hadwiger.parallel_body_valuation
import Submission.Commons.Geometry.Convex.Hadwiger.parallel_body_linearIndependent
set_option maxHeartbeats 4000000

open MeasureTheory Metric
open LeanEval.ConvexGeometry
open scoped Classical Pointwise

namespace Submission

noncomputable section

/-- The closed unit ball as a convex body in `E n`. -/
def unitBallBody (n : ℕ) : ConvexBody (E n) :=
  ⟨Metric.closedBall (0 : E n) 1, convex_closedBall (0 : E n) 1, isCompact_closedBall (0 : E n) 1, nonempty_closedBall.mpr zero_le_one⟩

/-- `K ↦ volume (K + tB)` : a continuous rigid-motion invariant valuation. -/
def parallelVolume (n : ℕ) (t : ℝ) : ConvexBody (E n) → ℝ :=
  fun K => (volume ((K + t • unitBallBody n : ConvexBody (E n)) : Set (E n))).toReal

theorem parallelVolume_mem_valuations (n : ℕ) (t : ℝ) :
    parallelVolume n t ∈ valuations n := by
  have h := Commons.Geometry.Convex.Hadwiger.parallel_body_valuation n t
  change IsValuation (parallelVolume n t)
  dsimp only [parallelVolume, unitBallBody, E, IsValuation] at *
  exact h

/-- The parallel-volume functions at `t = 0, …, n` are linearly independent elements of the
function space. -/
theorem parallelVolume_linearIndependent (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin (n + 1) => parallelVolume n (i : ℝ)) := by
  have h := Commons.Geometry.Convex.Hadwiger.parallel_body_linearIndependent n
  dsimp only [parallelVolume, unitBallBody, E] at h
  exact h

/-- The parallel-volume functions at `t = 0, …, n` are linearly independent elements of the
valuation space. -/
theorem parallelVolume_linearIndependent_valuations (n : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin (n + 1) => (⟨parallelVolume n (i : ℝ), parallelVolume_mem_valuations n (i : ℝ)⟩ : valuations n)) := by
  -- linear independence in the submodule follows from linear independence of the images
  have hLI := parallelVolume_linearIndependent n
  have hcomp : LinearIndependent ℝ
      ((Submodule.subtype (valuations n)) ∘
        (fun i : Fin (n + 1) =>
          (⟨parallelVolume n (i : ℝ), parallelVolume_mem_valuations n (i : ℝ)⟩ : valuations n))) := by
    simpa [Function.comp_def] using hLI
  exact LinearIndependent.of_comp (Submodule.subtype (valuations n)) hcomp

end
end Submission
