import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for `Work.Diff.Alg.q2p_berger` (Berger's inequality)

Berger's inequality on an orthonormal four-frame `e1, e2, e3, e4` for an algebraic curvature
tensor `R` (with all sectional curvatures between `a` and `b`) is proved by exhibiting the
curvature component `R(e1,e2,e3,e4)` as a finite combination of sectional curvatures of the eight
"diagonal" planes spanned by `(e1 ± e3)/√2`, `(e2 ± e4)/√2` and by `(e1 ± e4)/√2`, `(e2 ± e3)/√2`.

The combination is the *mixed second difference* of the quartic form `(u,v) ↦ R4 R u v u v`:
-/

namespace Work.Diff.Alg.Q2PB

open Submission.Diff.Alg

variable {n : ℕ}

/-- The mixed second difference `Δ_a Δ_b` of the quartic form `(x,y) ↦ R4 R x y x y`, evaluated at
`(c,d)`: `mixDiff R a b c d`. It is the alternating sum of `R4 R (a ± b) (c ± d) (a ± b) (c ± d)`
over the four sign choices. -/
noncomputable def mixDiff (R : Curv4 n) (a b c d : Fin n → ℝ) : ℝ :=
  R4 R (a + b) (c + d) (a + b) (c + d) - R4 R (a + b) (c - d) (a + b) (c - d)
    - R4 R (a - b) (c + d) (a - b) (c + d) + R4 R (a - b) (c - d) (a - b) (c - d)

end Work.Diff.Alg.Q2PB
