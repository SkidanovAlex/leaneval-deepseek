import Mathlib
import Submission.Work.Diff.GE.EvolB.Xact_rot_B
import Submission.Work.Diff.GE.react.Q_rot
import Submission.Work.Diff.GE.react.RotKit
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-equivariance of the reaction map, without `sorryAx`

The reaction map of the curvature evolution, `Work.Diff.GE.reactionMap = Work.Diff.GE.rmReact n =
Q - Xact`, is a contraction of the Euclidean metric and therefore commutes with the change of
orthonormal frame.  The workspace files `Submission/Work/Diff/GE/react/rmReact_rot.lean` and
`Submission/Work/Diff/GE/react/Xact_rot.lean` state this but still carry a `sorry` (in
`Work.Diff.GE.react.Xact_rot`); the `EvolB` development may not use them, so this file reproves the
statement from the sorry-free ingredients

* `Work.Diff.GE.react.Q_rot` — equivariance of Hamilton's `Q` (proved),
* `Work.Diff.GE.EvolB.Xact_rot_B` — equivariance of the Ricci-action term `Xact` (proved here
  from the index kit `Submission/Work/Diff/GE/react/RotKit.lean`),
* `Work.Diff.GE.react.rot_sub` — additivity of `rot A` (proved).
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

/-- **`O(n)`-equivariance of `rmReact = Q - Xact`**, with a `sorry`-free proof. -/
theorem rmReact_rot_C (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      Work.Diff.GE.rmReact n (Submission.Diff.Alg.rot A R)
        = Submission.Diff.Alg.rot A (Work.Diff.GE.rmReact n R) := by
  intro A hA R
  simp only [Work.Diff.GE.rmReact]
  rw [Work.Diff.GE.react.Q_rot n A hA R, Xact_rot_B n A hA R, Work.Diff.GE.react.rot_sub]

/-- **`O(n)`-equivariance of `reactionMap`**, with a `sorry`-free proof. -/
theorem reactionMap_rot_C (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      (Work.Diff.GE.reactionMap : Curv4 n → Curv4 n) (Submission.Diff.Alg.rot A R)
        = Submission.Diff.Alg.rot A (Work.Diff.GE.reactionMap R) := by
  intro A hA R
  show Work.Diff.GE.reactionMap (Submission.Diff.Alg.rot A R)
    = Submission.Diff.Alg.rot A (Work.Diff.GE.reactionMap R)
  rw [Work.Diff.GE.EvolA.reactionMap_eq_rmReact, Work.Diff.GE.EvolA.reactionMap_eq_rmReact]
  exact rmReact_rot_C n A hA R

end Work.Diff.GE.EvolB
