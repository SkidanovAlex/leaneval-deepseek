import Mathlib
import Submission.Work.Diff.GE.fixRmDefs
import Submission.Work.Diff.Evol.Calc
import Submission.Work.Diff.GE.react.RotKit
import Submission.Work.Diff.GE.react.Q_rot
import Submission.Work.Diff.GE.react.Xact_rot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-equivariance of the reaction map `rmReact = Q - Xact`

`Work.Diff.GE.rmReact n R = Q R - Xact R` is the quadratic reaction map of the curvature evolution
in fixed vectors (`∂ₜ R = ΔR + rmReact R`).  It is built from the Euclidean metric by contractions,
so it commutes with the change of orthonormal frame
`rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`, `A ∈ O(n)`:

  `rmReact n (rot A R) = rot A (rmReact n R)`  for every `A ∈ O(n)` and every `R : Curv4 n`.

This is the equivariance used to make the maximum principle and the pinching sets of the
Ricci-flow proof `O(n)`-invariant.

The two quadratic pieces are handled separately and independently:
`Work.Diff.GE.react.Q_rot` (Hamilton's term `Q`, from the `(3,4)`-contraction identity
`Work.Diff.GE.rot_contract`) and `Work.Diff.GE.react.Xact_rot` (the Uhlenbeck Ricci-action terms
`Xact`, from the `(0,2)`-tensoriality of the Ricci contraction `ricArr_rot` and the single-index
contraction identity `contract_Avec` of `Work.Diff.GE.react.RotKit`).  The assembly only needs the
additivity `rot_sub` of `rot A` in the tensor argument.
-/

namespace Work.Diff.GE.react

/-- **`O(n)`-equivariance of the reaction map.**  For every orthogonal `A : Matrix (Fin n) (Fin n) ℝ`
and every curvature array `R`, `rmReact n (rot A R) = rot A (rmReact n R)`. -/
theorem rmReact_rot (n : ℕ) : ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Submission.Diff.Alg.Curv4 n, Work.Diff.GE.rmReact n (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (Work.Diff.GE.rmReact n R) := by
  intro A hA R
  simp only [Work.Diff.GE.rmReact]
  rw [Q_rot n A hA R, Xact_rot n A hA R, rot_sub]

end Work.Diff.GE.react
