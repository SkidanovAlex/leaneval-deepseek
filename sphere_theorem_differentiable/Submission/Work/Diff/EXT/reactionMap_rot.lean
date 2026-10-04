import Mathlib
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.rot_Q
import Submission.Work.Diff.GE.react.RotKit
import Submission.Work.Diff.GE.EvolB.Xact_rot_B

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-equivariance of the reaction map of the fixed-vector curvature evolution

`Work.Diff.GE.reactionMap` (`Submission/Work/Diff/GE/reaction_map_defs.lean`) is the explicit
quadratic map

`reactionMap R = Q R − ∑ₚ (Ric_{ip}R_{pjkl} + Ric_{jp}R_{ipkl} + Ric_{lp}R_{ijkp}
   + Ric_{kp}R_{ijpl})`

on curvature arrays; it is the reaction term of Hamilton's evolution equation for the curvature in
*fixed* vectors, `∂ₜRm = ΔRm + reactionMap(Rm)`.

Here we prove that it commutes with the orthogonal change of orthonormal frame
`rot A R i j k l = ∑ a b c d A i a A j b A k c A l d R a b c d`, `A ∈ O(n)`:

`reactionMap (rot A R) = rot A (reactionMap R)`.

This is the equivariance used to make the maximum principle and the pinching sets of the
Ricci-flow proof `O(n)`-invariant.

## Route

* `reactionMap_eq_Q_sub_Xact`: `reactionMap R = Q R − Xact R`, where `Xact` is the Uhlenbeck
  Ricci-action term of `Work.Diff.Evol.Calc`.  The two definitions differ only by the order of the
  last two Ricci-action terms, so this is an index renaming (`ricF = ricArr` definitionally).
* `Work.Diff.GE.rot_Q` (proved in `Submission/Work/Diff/GE/rot_Q.lean`): `Q` is `O(n)`-equivariant.
* `Work.Diff.GE.EvolB.Xact_rot_B` (proved in `Submission/Work/Diff/GE/EvolB/Xact_rot_B.lean`):
  the Ricci-action term `Xact` is `O(n)`-equivariant.
* `Work.Diff.GE.react.rot_sub`: `rot A` is additive, `rot A (S - T) = rot A S - rot A T`.

No algebraic hypothesis on `R` is needed: the identity is a contraction identity for the Euclidean
metric, valid for every `Curv4 n`.
-/

namespace Work.Diff.EXT

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- `Work.Diff.GE.reactionMap` is Hamilton's term `Q` minus the Uhlenbeck Ricci-action term
`Work.Diff.Evol.Xact`; the two differ only in the order of the last two of the four Ricci-action
summands. -/
theorem reactionMap_eq_Q_sub_Xact (R : Curv4 n) :
    Work.Diff.GE.reactionMap R = Submission.Diff.Alg.Q R - Work.Diff.Evol.Xact R := by
  funext i j k l
  simp only [Pi.sub_apply, Work.Diff.GE.reactionMap, Work.Diff.GE.ricF, Work.Diff.Evol.Xact,
    Work.Diff.Evol.ricArr]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- **`O(n)`-equivariance of the reaction map of the fixed-vector curvature evolution**: for every
orthogonal `A : Matrix (Fin n) (Fin n) ℝ` and every curvature array `R`,
`reactionMap (rot A R) = rot A (reactionMap R)`. -/
theorem reactionMap_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Submission.Diff.Alg.Curv4 n) :
    Work.Diff.GE.reactionMap (Submission.Diff.Alg.rot A R)
      = Submission.Diff.Alg.rot A (Work.Diff.GE.reactionMap R) := by
  rw [reactionMap_eq_Q_sub_Xact (Submission.Diff.Alg.rot A R), reactionMap_eq_Q_sub_Xact R,
    Work.Diff.GE.rot_Q A hA R, Work.Diff.GE.EvolB.Xact_rot_B n A hA R]
  exact (Work.Diff.GE.react.rot_sub A (Submission.Diff.Alg.Q R) (Work.Diff.Evol.Xact R)).symm

end Work.Diff.EXT
