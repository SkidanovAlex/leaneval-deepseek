import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame transport of the isotropic curvature form `EFun`

For an arbitrary matrix `A` acting on `ℝⁿ` and the induced action
`rot A R i j k l = ∑ A i a A j b A k c A l d R a b c d` on `4`-index tensors, the quartic form
`EFun` (the integrand of the `PIC2` condition) is transported by the transpose:

`EFun (rot A R) x y z w = EFun R (Aᵀx) (Aᵀy) (Aᵀz) (Aᵀw)`.

This is immediate from the multilinear identity `R4 (rot A R) x y z w =
R4 R (Aᵀx) (Aᵀy) (Aᵀz) (Aᵀw)` (`Work.Diff.Alg.Pinch.Cone.r4_rot`), applied to the five
contractions appearing in `EFun`.  No orthogonality of `A` is needed.
-/

namespace Work.Diff.Alg.Pinch

open Submission.Diff.Alg

/-- The multilinear identity `R4 (rot A R) x y z w = R4 R (Aᵀx) (Aᵀy) (Aᵀz) (Aᵀw)`, restated with
the transpose written entrywise as `Aᵀ v = fun i => ∑ j, A j i * v j`. -/
theorem r4_rot' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (x y z w : Fin n → ℝ) :
    R4 (rot A R) x y z w
      = R4 R (fun i => ∑ j, A j i * x j) (fun i => ∑ j, A j i * y j)
          (fun i => ∑ j, A j i * z j) (fun i => ∑ j, A j i * w j) :=
  Cone.r4_rot A R x y z w

theorem EFun_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (R : Submission.Diff.Alg.Curv4 n)
    (x y z w : Fin n → ℝ) :
    Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.rot A R) x y z w
      = Work.Diff.Alg.Q2P.EFun R (fun i => ∑ j, A j i * x j) (fun i => ∑ j, A j i * y j)
          (fun i => ∑ j, A j i * z j) (fun i => ∑ j, A j i * w j) := by
  simp only [Work.Diff.Alg.Q2P.EFun, r4_rot']

end Work.Diff.Alg.Pinch
