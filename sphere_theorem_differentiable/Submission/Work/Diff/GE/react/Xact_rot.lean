import Mathlib
import Submission.Work.Diff.GE.react.RotKit
import Submission.Work.Diff.Evol.Calc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.react

theorem Xact_rot (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ,
      ∀ R : Submission.Diff.Alg.Curv4 n,
        Work.Diff.Evol.Xact (Submission.Diff.Alg.rot A R) =
          Submission.Diff.Alg.rot A (Work.Diff.Evol.Xact R) := by sorry

end Work.Diff.GE.react
