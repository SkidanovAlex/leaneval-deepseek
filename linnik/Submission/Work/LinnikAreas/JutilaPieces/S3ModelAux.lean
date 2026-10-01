/-
# Auxiliary definitions for `S3ModelDS`

`S3ModelDefs` already fixes `Qf`, `wm`, `RS1`, `RS0`, `s3DSabs`.  The evaluation
`s3cont = ζ(2)^{-1}·Σ_{q ≤ N/z}(N/q)·s3DSabs (Qf z N q) (N/(qz))` is a pure identity of finite
sums; in it the logarithm attached to an index `n` at cut-off `Qf z N q` is always

  `log(Qf z N q / n) − 1`,

which occurs four times per summand.  This file gives it a name, so that the pieces of the
evaluation (`S3ModelDSContTerm`, `S3ModelDSInner`) can be stated without repeating the
expression:
-/
import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3ModelDefs

namespace Work.LinnikAreas.JutilaPieces

noncomputable section

/-- `Lq z N q n = log (Qf z N q / n) − 1`, the logarithm attached to the index `n` when the
continuous model is evaluated at the cut-off `Qf z N q`. -/
def Lq (z N q n : ℕ) : ℝ := Real.log (Qf z N q / (n : ℝ)) - 1

end

end Work.LinnikAreas.JutilaPieces
