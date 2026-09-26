import Mathlib
import Submission.Work.SG.Defs

/-!
# Lattice points in a ball are finite

A discrete additive subgroup `L ≤ E 3` (equivalently, a subgroup whose induced topology is
discrete) meets every closed ball of finite radius in only finitely many points.

The proof has two ingredients:
* a discrete subgroup of a Hausdorff topological additive group is closed
  (`AddSubgroup.isClosed_of_discreteTopology`);
* in a proper metric space, a set that is discrete and closed meets every bounded set in a
  finite set (`Metric.finite_isBounded_inter_isClosed`).
The closed ball `Metric.closedBall 0 r` is exactly `{v | ‖v‖ ≤ r}` and is bounded, and `E 3` is
finite dimensional, hence proper.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- A discrete additive subgroup of `E 3` is closed in `E 3`. -/
theorem isClosed_of_discrete {L : AddSubgroup (E 3)} [DiscreteTopology L] :
    IsClosed (L : Set (E 3)) :=
  AddSubgroup.isClosed_of_discreteTopology (U := L)

/-- The set of points of a ball of radius `r` is the intersection of the closed ball with `L`. -/
theorem ball_set_eq {L : AddSubgroup (E 3)} (r : ℝ) :
    {v : E 3 | v ∈ L ∧ ‖v‖ ≤ r} = Metric.closedBall (0 : E 3) r ∩ (L : Set (E 3)) := by
  ext v
  simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem finite_ball_lattice {L : AddSubgroup (LeanEval.Geometry.SpaceGroupsProblem.E 3)}
    [DiscreteTopology L] (r : ℝ) :
    {v : LeanEval.Geometry.SpaceGroupsProblem.E 3 | v ∈ L ∧ ‖v‖ ≤ r}.Finite := by
  rw [ball_set_eq (L := L) r]
  exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    Metric.isBounded_closedBall (isClosed_of_discrete (L := L))

end Work.SG
