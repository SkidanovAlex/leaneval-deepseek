import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Q2PB

open Submission.Diff.Alg

/-- `secK` is homogeneous of degree `4` in the pair of vectors: scaling both vectors by `t` scales
the sectional curvature by `t ^ 4` (each of the four slots of the quartic form `R4` picks up one
factor of `t`). -/
theorem secK_smul {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (t : ℝ) (u v : Fin n → ℝ) :
    Submission.Diff.Alg.secK R (t • u) (t • v) = t ^ 4 * Submission.Diff.Alg.secK R u v := by
  simp only [Submission.Diff.Alg.secK]
  rw [Work.Diff.Alg.Q2P.R4_smul₁, Work.Diff.Alg.Q2P.R4_smul₂,
    Work.Diff.Alg.Q2P.R4_smul₃, Work.Diff.Alg.Q2P.R4_smul₄]
  ring

end Work.Diff.Alg.Q2PB
