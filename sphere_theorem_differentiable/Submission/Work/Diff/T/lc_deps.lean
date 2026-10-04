import Mathlib
import Submission.Diff.Interfaces
import Submission.Geodesic
import Submission.ChartConnection
import Submission.ChartCurv
import Submission.ChartCurvCont
import Submission.Commons.Analysis.Calculus.hasDerivAt_deriv_partial_swap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Re-export module for the `Work.Diff.T` area (contract T2, `LCVariation`): imports the frozen
interfaces and the seeded chart/Christoffel machinery. -/
