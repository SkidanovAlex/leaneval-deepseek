import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Rot2Defs
import Submission.Work.Diff.Alg.Pinch.rot_toolkit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci tensor of a rotated curvature array

Under the change of orthonormal frame `e'ᵢ = ∑ₐ Aᵢₐ eₐ` (`A ∈ O(n)`) the curvature components
transform as `rot A R`, and the Ricci contraction transforms as a `(0,2)`-tensor, i.e. by *two*
copies of `A`:

`ric (rot A R) i j = ∑ a b, A i a * A j b * ric R a b = rot2 A (ric R) i j`.

This is the Ricci case of the `O(n)`-equivariance of the Böhm–Wilking contraction, and is what makes
the difference tensor of the pinching-set construction equivariant.

The work is done by `Work.Diff.GE.react.ricArr_rot` (the `(0,2)`-tensoriality of the Ricci
contraction, from `Work.Diff.GE.react.RotKit`), restated here for the `ric` of this development;
`Work.Diff.Alg.Pinch.rt_ric_rot` is exactly that restatement.
-/

namespace Work.Diff.Alg.Pinch

theorem ric_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Submission.Diff.Alg.Curv4 n) :
    Work.Diff.Alg.Pinch.ric (Submission.Diff.Alg.rot A R)
      = Work.Diff.Alg.Pinch.rot2 A (Work.Diff.Alg.Pinch.ric R) := by
  funext i j
  simp only [rot2]
  exact rt_ric_rot A hA R i j

end Work.Diff.Alg.Pinch
