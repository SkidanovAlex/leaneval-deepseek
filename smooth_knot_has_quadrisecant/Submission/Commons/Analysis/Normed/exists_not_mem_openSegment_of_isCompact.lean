import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.Normed

open Set
open Metric

/-- Strict convexity of the Euclidean norm: a point strictly inside the open segment
between two distinct points of a real inner product space has norm strictly less than
the larger of the norms of the endpoints. -/
lemma norm_lt_max_of_mem_openSegment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x y z : E} (hz : z ∈ openSegment ℝ x y) (hxy : x ≠ y) :
    ‖z‖ < max ‖x‖ ‖y‖ := by
  have hx : x ∈ closedBall (0 : E) (max ‖x‖ ‖y‖) := by
    rw [mem_closedBall_zero_iff]
    exact le_max_left _ _
  have hy : y ∈ closedBall (0 : E) (max ‖x‖ ‖y‖) := by
    rw [mem_closedBall_zero_iff]
    exact le_max_right _ _
  exact mem_ball_zero_iff.mp (openSegment_subset_ball_of_ne hx hy hxy hz)

/-- In a compact subset of a real inner product space, some point is not
strictly between two other points of the set (a point of maximal distance
from any chosen base point works). -/
theorem exists_not_mem_openSegment_of_isCompact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (C : Set E) (hC : IsCompact C) (hne : C.Nonempty) :
    ∃ q ∈ C, ∀ x y : E, x ∈ C → y ∈ C → x ≠ y → q ∉ openSegment ℝ x y := by
  have hcont : ContinuousOn (fun q : E => ‖q‖) C := continuous_norm.continuousOn
  rcases hC.exists_isMaxOn hne hcont with ⟨q, hqC, hqmax⟩
  refine ⟨q, hqC, ?_⟩
  intro x y hxC hyC hxy hqseg
  have hxle : ‖x‖ ≤ ‖q‖ := hqmax hxC
  have hyle : ‖y‖ ≤ ‖q‖ := hqmax hyC
  have hlt : ‖q‖ < max ‖x‖ ‖y‖ := norm_lt_max_of_mem_openSegment hqseg hxy
  have hmaxle : max ‖x‖ ‖y‖ ≤ ‖q‖ := max_le hxle hyle
  exact (not_lt_of_ge hmaxle) hlt

end Commons.Analysis.Normed