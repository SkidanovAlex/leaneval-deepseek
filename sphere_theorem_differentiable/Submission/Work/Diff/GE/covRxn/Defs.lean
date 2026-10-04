import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.contMDiff_rmP_fields
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.FrameIndep
import Submission.Work.Diff.GE.rot_contract
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.kato_geodesic_frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivative bound for the quadratic reaction `F(Rm)` (assembly)

See `cotangent`.  This file assembles the pieces into
`Work.Diff.GE.covReactionFormAt_le_A`.

## Structure

`Rxn.reactionFormAtE` is the reaction form evaluated in an *explicit* frame `e`, and
`Rxn.reactionW` is the same expression with a frame *field* `W`.  For an equivariant `F`, the value
does not depend on the orthonormal frame, so along a smooth orthonormal frame field `W` (which
exists locally, and which we may take geodesic at `x`) the (a priori non-smooth) function
`y ↦ reactionFormAt F g y (...)` agrees with `Rxn.reactionW F g W A B C D`, which is smooth.  The
derivative is then computed with the product rule: the connection terms coming from the derivative
of the coefficients cancel the four tensorialising slot corrections of the `Ext` pattern (this is
where geodesicity of the frame at `x` is used), and the chain rule gives the contraction of
`fderiv ℝ F (rmC)` with `∇Rm`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.Rxn

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A section of the tangent bundle that is `C^∞`. -/
abbrev SmoothField (X : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% X)

/-- The reaction form `y ↦ F(Rm(y))` evaluated on four vectors in an explicit frame `e` at `x`. -/
noncomputable def reactionFormAtE (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c d : TangentSpace I x) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner x (e i) a * g.inner x (e j) b * g.inner x (e k) c * g.inner x (e l) d)
      * (F (rmFrame g x e)) i j k l

/-- `reactionFormAt` is `reactionFormAtE` computed in the chosen frame `onFrame g x`. -/
lemma reactionFormAt_eq_reactionFormAtE
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    reactionFormAt F g x a b c d = reactionFormAtE F g x (onFrame g x) a b c d := rfl

/-- The curvature components in a frame *field* `W`, as a `Curv4`-valued function of the base
point.  For `W y` orthonormal this is `rmFrame g y (W y)`. -/
noncomputable def rmFrameField (g : SMet I M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y) (y : M) :
    Curv4 (Module.finrank ℝ E) :=
  fun i j k l => rmP g y (W y i) (W y j) (W y k) (W y l)

/-- The reaction form evaluated in a frame *field* `W`, on four field slots, as a function of the
base point. -/
noncomputable def reactionW (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (A B C D : Π y : M, TangentSpace I y) (y : M) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner y (W y i) (A y) * g.inner y (W y j) (B y) * g.inner y (W y k) (C y)
      * g.inner y (W y l) (D y)) * (F (rmFrameField g W y)) i j k l

/-- The four-fold contraction of a curvature array `X` with the frame components of four vectors,
in the chosen frame `onFrame g x`. -/
noncomputable def pairing (g : SMet I M) (x : M) (a b c d : TangentSpace I x)
    (X : Curv4 (Module.finrank ℝ E)) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner x (onFrame g x i) a * g.inner x (onFrame g x j) b * g.inner x (onFrame g x k) c
      * g.inner x (onFrame g x l) d) * X i j k l

/-- The array of components of `∇Rm` at `x` in the direction `v`, in the chosen frame. -/
noncomputable def dRmArr (g : SMet I M) (x : M) (v : TangentSpace I x) :
    Curv4 (Module.finrank ℝ E) :=
  fun i j k l => covRm g x v (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l)

end Work.Diff.GE.Rxn
