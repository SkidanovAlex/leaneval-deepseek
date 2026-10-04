import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Common vocabulary for the PIC2 tangential-invariance lemmas

Re-exports the frozen algebraic definitions (`Submission.Diff.Alg`: `Curv4`, `R4`, `Iso`, `Q`,
`IsAlgCurv`, `InPIC2`, ...) together with the quartic form `Work.Diff.Alg.Q2P.EFun`, whose
nonnegativity is `InPIC2` (`Work.Diff.Alg.Q2P.inPIC2_iff`).  Lemmas about the Hamilton reaction
term `Q` and the cone `{R | InPIC2 R}` import this module.
-/

namespace Work.Diff.Alg.Pinch

open Submission.Diff.Alg

/-- `InPIC2` is exactly the pointwise nonnegativity of the quartic form `EFun`. -/
theorem inPIC2_iff_EFun (n : ℕ) (R : Curv4 n) :
    InPIC2 R ↔ ∀ x y z w : Fin n → ℝ, 0 ≤ Q2P.EFun R x y z w :=
  Q2P.inPIC2_iff R

end Work.Diff.Alg.Pinch
