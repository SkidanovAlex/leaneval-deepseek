import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Lib
import Submission.Work.Diff.C.riccati_lower_bound
import Submission.Work.Diff.C.log_deriv_lower
import Submission.Work.Diff.C.inner_self_bound_near_zero
import Submission.Work.Diff.C.hasDerivAt_cot_const_mul
import Submission.JacobiGlobal
import Submission.IndexFTC
import Submission.IndexIntrinsic2
import Submission.RauchK
import Submission.RauchCompareK
import Submission.ConjCut
import Submission.IndexMin
import Submission.HopfRinow2
import Submission.InjRadius
import Submission.CutKlingenberg
import Submission.Gauss
import Submission.GExpLocalInj
import Submission.XuLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C: import bundle for the lower Hessian comparison (`Work.Diff.C.hess_lower_v2`)

This module only collects the imports used by the lower Hessian comparison for the distance
function and by the sub-lemmas delegated for it.  It contains no mathematics.
-/
