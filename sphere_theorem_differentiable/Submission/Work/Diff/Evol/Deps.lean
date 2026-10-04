import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.T.hasDerivAt_metric_inner_moving
import Submission.Work.Diff.T.metric_family_deriv
import Submission.Work.Diff.Evol.Calc
import Submission.Work.Diff.Evol.RicDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared imports for the `Evol` area (Hamilton's curvature evolution)

Re-exports the frozen contract modules (`Submission.Diff.Interfaces`, `Submission.Diff.Evol`,
`Submission.Diff.Grad`), the proved first-variation material of the `T` area
(`LCVariation`, the derivative of the metric family, the product rule for a moving point against the
moving metric) and the local definitions of the area (`Calc`, `RicDeriv`), so that delegated
lemmas can be stated with a single import.
-/
