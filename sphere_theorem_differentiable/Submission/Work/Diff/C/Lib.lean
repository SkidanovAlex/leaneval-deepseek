import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.HingePiece
import Submission.GlobalBM
import Submission.HopfRinow2
import Submission.ChartIndep
import Submission.ChartCurvCont
import Submission.CurveField
import Submission.GExpVelocity
import Submission.GeodesicExtend
import Submission.Minimal
import Submission.EDist
import Submission.GlobalExp
import Submission.Geodesic
import Submission.Gauss
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve
import Submission.Commons.Analysis.Calculus.deriv_deriv_nonneg_of_isLocalMin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C: shared import bundle

This module only collects the imports that the lemmas of area C (`dist_eikonal`, `hess_upper`,
`hess_lower`, ...) and their delegated sub-lemmas use, so that delegated statements are stated
against the right vocabulary. It contains no mathematics.
-/
