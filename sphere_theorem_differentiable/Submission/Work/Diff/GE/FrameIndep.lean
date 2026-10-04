import Mathlib
import Submission.Diff.Grad
import Submission.Diff.Evol
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.rot_frobsq
import Submission.Work.Diff.GE.rot_qPair
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.PP.evolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame independence of the frozen curvature quantities

The frozen quantities `rmNormSq`, `qPairAt` (and `rmC`) of `Submission/Diff/Grad.lean` are computed in
the `Classical.epsilon`-chosen orthonormal frame `onFrame g x`.  Because two `g`-orthonormal frames
differ by an orthogonal matrix `A` (`onFrame_orthogonal_change`), the frame components change by
`rot A` (`rmFrame_eq_rot`), and `rot_frobsq`/`rot_qPair` show that the contractions `frobSq` and
`qPair` are `rot A`-invariant, the *values* of these quantities do not depend on the frame:

* `frobSq_rmFrame_eq_of_isONFrame`, `qPair_rmFrame_eq_of_isONFrame`;
* `rmNormSq_eq_frobSq_rmFrame`, `qPairAt_eq_qPair_rmFrame`: the frozen quantities computed in an
  arbitrary orthonormal frame.

This is what allows the evolution equation `∂ₜ R = ΔR + Q(R)` -- which is available only in an
*Uhlenbeck* frame (a special orthonormal frame) -- to be used for the frozen norm `rmNormSq`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [T2Space M]

/-- `frobSq (rmFrame g x e)` -- the squared Frobenius norm of the curvature in the frame `e` -- is
independent of the orthonormal frame `e`. -/
theorem frobSq_rmFrame_eq_of_isONFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e) (he' : IsONFrame g x e') :
    frobSq (rmFrame g x e) = frobSq (rmFrame g x e') := by
  obtain ⟨A, hA, hAe⟩ := onFrame_orthogonal_change g x e e' he he'
  rw [rmFrame_eq_rot hLC g x e e' A hAe, rot_frobsq A hA]

/-- `qPair (rmFrame g x e) = ⟪Rm, Q(Rm)⟫` is independent of the orthonormal frame `e`. -/
theorem qPair_rmFrame_eq_of_isONFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e) (he' : IsONFrame g x e') :
    qPair (rmFrame g x e) = qPair (rmFrame g x e') := by
  obtain ⟨A, hA, hAe⟩ := onFrame_orthogonal_change g x e e' he he'
  rw [rmFrame_eq_rot hLC g x e e' A hAe, rot_qPair A hA]

/-- The frozen `rmNormSq g x = |Rm|²` may be computed in any orthonormal frame. -/
theorem rmNormSq_eq_frobSq_rmFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    rmNormSq g x = frobSq (rmFrame g x e) :=
  frobSq_rmFrame_eq_of_isONFrame hLC g x (onFrame g x) e (isONFrame_onFrame g x) he

/-- The frozen `qPairAt g x = ⟪Rm, Q(Rm)⟫` may be computed in any orthonormal frame. -/
theorem qPairAt_eq_qPair_rmFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    qPairAt g x = qPair (rmFrame g x e) :=
  qPair_rmFrame_eq_of_isONFrame hLC g x (onFrame g x) e (isONFrame_onFrame g x) he

/-- The rough Laplacian of `Submission/Diff/Evol.lean` agrees with the version of
`Submission/Work/Diff/PP/evolution.lean` (same definition, two namespaces). -/
theorem lapRmFrame_eq_roughLap (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Submission.Diff.lapRmFrame g x e = Work.Diff.PP.roughLap g x e := rfl

end Work.Diff.GE
