import ChallengeDeps
import Submission.UseCommons
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_mem_span_parallelBody
set_option maxHeartbeats 4000000

open MeasureTheory Metric
open LeanEval.ConvexGeometry
open scoped Classical Pointwise

namespace Submission

noncomputable section

/-- Every valuation lies in the span of the parallel-body volume functionals. -/
theorem valuations_le_span (n : ℕ) :
    (valuations n : Submodule ℝ (ConvexBody (E n) → ℝ)) ≤
      Submodule.span ℝ (Set.range (fun i : Fin (n + 1) => parallelVolume n (i : ℝ))) := by
  intro f hf
  have hfval : IsValuation f := by
    change IsValuation f
    exact hf
  have h := Commons.Geometry.Convex.Hadwiger.valuation_mem_span_parallelBody n
  exact h f hfval

/-- The valuation space is exactly the span of the `n+1` parallel-body volume functionals. -/
theorem valuations_eq_span (n : ℕ) :
    (valuations n : Submodule ℝ (ConvexBody (E n) → ℝ)) =
      Submodule.span ℝ (Set.range (fun i : Fin (n + 1) => parallelVolume n (i : ℝ))) := by
  apply le_antisymm
  · exact valuations_le_span n
  · rw [Submodule.span_le]
    rintro g ⟨i, rfl⟩
    exact parallelVolume_mem_valuations n (i : ℝ)

theorem hadwiger_assembly (n : ℕ) : Module.finrank ℝ (valuations n) = n + 1 := by
  rw [valuations_eq_span n]
  have hLI := parallelVolume_linearIndependent n
  rw [finrank_span_eq_card hLI]
  simp

end
end Submission
