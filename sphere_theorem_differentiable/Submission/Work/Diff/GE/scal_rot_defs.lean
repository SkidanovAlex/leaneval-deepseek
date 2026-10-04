import Mathlib
import Submission.Work.Diff.GE.deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Helper contraction for `scal_rot`

`Dc N R` is the double contraction of the curvature array `R` with a matrix `N`, contracting the
first with the third and the second with the fourth slot.  For `N = Γ⁻¹`, where `Γ` is the Gram
matrix of a frame, it *is* the scalar curvature in that frame: `N2 Γ R = Dc Γ⁻¹ R` holds by `rfl`.
The point of the reformulation is that the matrix identity
`Dc N (rot A R) = Dc (Aᵀ * N * A) R` has no inverse in it (see `Work.Diff.GE.Dc_rot`).
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- Double contraction of `R : Curv4 n` with the matrix `N`: slots `1` and `3` are contracted with
`N`, and slots `2` and `4` are contracted with `N`. -/
def Dc {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) : ℝ :=
  ∑ i, ∑ a, ∑ j, ∑ b, N i a * N j b * R i j a b

/-- `Dc` is `N2` with the inverse Gram matrix, by definition. -/
lemma N2_eq_Dc {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    N2 N R = Dc N⁻¹ R := rfl

end Work.Diff.GE
