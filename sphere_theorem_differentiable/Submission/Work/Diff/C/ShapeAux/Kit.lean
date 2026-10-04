import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.JacobiGlobal
import Submission.CurveCov
import Submission.CurveField
import Submission.Variation
import Submission.RayJacobi
import Submission.RayJacobiTensor
import Submission.ConjCut
import Submission.GExpVelocity
import Submission.Work.OddBound.longHomotopy.gauss_pairing_fibre
import Submission.Work.OddBound.longHomotopy.covAlong_variation_zero
import Submission.Work.OddBound.longHomotopy.pairing_affine_of_jacobi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Import bundle for the shape-operator auxiliaries (`Work.Diff.C.ShapeAux`)

This module contains no mathematics: it collects the modules that the lemmas of
`Submission/Work/Diff/C/ShapeAux/` (the pieces of `Work.Diff.C.hess_dist_jacobi_shapeOp`) need, so
that they can be listed in `depends_on`.
-/
