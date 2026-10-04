import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.rot_qPair
import Submission.Work.Diff.GE.frobSq5_main
import Submission.Work.Diff.GE.N5_eq_QQ2
import Submission.Work.Diff.GE.frobSq5_eq_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# General-basis forms of the frozen curvature quantities

The frozen quantities `rmNormSq`, `qPairAt`, `dRmNormSq` of `Submission.Diff.Grad` are defined
through the `Classical.epsilon`-chosen orthonormal frame `onFrame g x`.  For the continuity proof
of `Work.Diff.GE.continuous_flow_quantities` one needs instead *explicit* expressions in terms of
the components of the curvature in a **fixed** frame, i.e. general-basis (Gram-matrix) forms.

For a basis `e` of `T_xM` with Gram matrix `Γ ij = g(e i, e j)` and components
`C i j k l = Rm(e i, e j, e l, e k) = rmFrame g x e i j k l`, the identities are

* `rmNormSq g x = N4 Γ C` (`N4` is defined in `Work.Diff.GE.norms_defs`);
* `dRmNormSq g x = N5 Γ D` where `D` collects the `∇Rm` components in `e`;
* `qPairAt g x = qPairGen Γ C`, where `qPairGen` is defined below.

This file only contains the *definition* `qPairGen`; the identities are proved separately.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable {n : ℕ}

/-- **The general-basis form of `qPair`.**  If `C` are the curvature components in a basis with
Gram matrix `Γ`, then `qPairGen Γ C` is `⟪Rm, Q(Rm)⟫ = qPair` computed in an orthonormal frame.
The expression is the general-basis transcription of `rot_qPair`'s decomposition
`qPair R = rqA1 R + 2 rqA2 R - 2 rqA3 R` with `rqA*` the three matrix contractions. -/
noncomputable def qPairGen (Γ : Matrix (Fin n) (Fin n) ℝ) (C : Curv4 n) : ℝ :=
  Matrix.trace ((rqM C)ᵀ * rqKr (Γ⁻¹) * rqM C * rqKr (Γ⁻¹) * (rqM C)ᵀ * rqKr (Γ⁻¹))
    + 2 * Matrix.trace ((rqN C)ᵀ * rqKr (Γ⁻¹) * rqN C * rqKr (Γ⁻¹) * (rqN C)ᵀ * rqKr (Γ⁻¹))
    - 2 * Matrix.trace ((rqP C)ᵀ * rqKr (Γ⁻¹) * rqN C * rqKr (Γ⁻¹) * (rqN C)ᵀ * rqKr (Γ⁻¹))

end Work.Diff.GE
