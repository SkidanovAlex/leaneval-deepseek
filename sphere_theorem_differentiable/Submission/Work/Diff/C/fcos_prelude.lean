/-
# Prelude for the sub-lemmas of `Work.Diff.C.fcos_hess`

This module only collects imports (it contains no mathematics): the vocabulary of area C
(`Submission.Work.Diff.C.Setup`: `rgrad`, `rhess`, `rdist`, `fcos`, `HessBoundRegion`),
the smoothness of the gradient (`Submission.Work.Diff.C.mvfderiv_contMDiffAt`), the
local-to-global smooth extension (`Submission.Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn`),
the smooth local orthonormal frames (`Submission.Work.Diff.GE.smooth_onframe`),
the instance metric as an `SMet` (`Submission.Work.Diff.L.Defs`), and the two general lemmas
`Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields` (mixed directional
derivatives commute up to the Lie bracket) and
`Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq` (every tangent vector
extends to a globally smooth field).
-/
import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.mvfderiv_contMDiffAt
import Submission.Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn
import Submission.Work.Diff.C.hess_upper
import Submission.Work.Diff.GE.smooth_onframe
import Submission.Work.Diff.L.Defs
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
