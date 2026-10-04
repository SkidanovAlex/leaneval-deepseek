import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.rot_invariance
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|Ric|²` is independent of the orthonormal frame

`Submission.Diff.ricNormSq g x = ricSq (rmC g x)` computes `|Ric|²` in the
`Classical.epsilon`-chosen orthonormal frame `onFrame g x`. This file shows that the same value is
obtained in *any* `g`-orthonormal frame: `ricNormSq g x = ricSq (rmFrame g x e)`.

The proof is the frame-change argument: two orthonormal frames differ by an orthogonal matrix `A`
(`onFrame_orthogonal_change`), the curvature components change by `rot A` (`rmFrame_eq_rot`), and
`ricSq` is invariant under `rot A` for orthogonal `A` (`rot_invariance`).

`rmFrame_eq_rot` is stated with the frozen contract `LCSmooth I M` as hypothesis; here only the
smoothness of `lcOf g` for the *single* metric `g` is available, so we obtain `LCSmooth I M`
outright from `Work.EXT.lcSmooth_noBoundary`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem ricNormSq_eq_ricSq_rmFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (g : Submission.Diff.SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g)
      ((⊤ : ENat) : WithTop ENat))
    (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e) :
    Submission.Diff.ricNormSq g x = Submission.Diff.Alg.ricSq (Submission.Diff.rmFrame g x e) := by
  have hLC : LCSmooth I M := Work.EXT.lcSmooth_noBoundary
  obtain ⟨A, hA, hAe⟩ :=
    onFrame_orthogonal_change g x (onFrame g x) e (isONFrame_onFrame g x) he
  show ricSq (rmFrame g x (onFrame g x)) = ricSq (rmFrame g x e)
  rw [rmFrame_eq_rot hLC g x (onFrame g x) e A hAe,
    (rot_invariance A hA (rmFrame g x (onFrame g x))).2.2.1]

end Work.Diff.GE
