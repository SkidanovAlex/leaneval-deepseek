import Mathlib
import Submission.Diff.Interfaces
import Submission.Geodesic
import Submission.Gauss
import Submission.GExpFlow
import Submission.ChartCurv
import Submission.ChartBounds
import Submission.Curvature
import Submission.CurvatureVec
import Submission.Work.Diff.T.metric_pairing_smooth
import Submission.Work.Diff.T.metric_family_deriv
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
import Submission.Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT` area: shared imports for the continuity-of-Ricci lemmas

This module only *re-exports* the seeded library and the Mathlib/Commons lemmas that the lemmas of
the `EXT/ricAt_continuousAt` development use: the frozen interfaces (`Submission.Diff.Interfaces`),
the chart frame and Christoffel machinery (`Submission.Geodesic`, `Submission.ChartCurv`,
`Submission.ChartBounds`), the algebraic curvature library (`Submission.Curvature`,
`Submission.CurvatureVec`), the `T`-area smoothness lemmas for jointly smooth metric families, and
the `Commons` lemmas about `mvfderiv`/covariant derivatives.  It contains no mathematics.
-/
