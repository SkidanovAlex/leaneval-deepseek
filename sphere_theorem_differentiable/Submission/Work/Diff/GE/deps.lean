import Mathlib
import Submission.Diff.Grad
import Submission.Diff.Interfaces
import Submission.Diff.Alg
import Submission.CurvatureVec
import Submission.Curvature
import Submission.Geodesic
import Submission.ChartCurv
import Submission.ChartBounds
import Submission.Work.Diff.GE.norms_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Import hub for the regularization (`REG`) area

Delegated lemmas in `Work.Diff.GE` that need the seeded curvature/chart library and the local
definitions of `Work.Diff.GE.norms_defs` can simply depend on this module.
-/
