import Mathlib
import Submission.Diff.Interfaces
import Submission.Diff.Grad
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.Tangent.contMDiff_finset_sum_smul_section
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Import hub for the `kato_geodesic_frame` development

`Work.Diff.GE.kato_geodesic_frame` (a geodesic orthonormal frame at a point) and the lemmas it is
split into all live in `Submission/Work/Diff/GE/` and share this import hub: the frozen interfaces
(`Submission.Diff.Interfaces`, `Submission.Diff.Grad`), the curvature-in-frames bridge
(`Submission.Work.Diff.GE.Frame`, `...NablaRm`), and the commons smoothness lemmas for sections and
for the application of a smooth connection to a smooth field.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

end Work.Diff.GE
