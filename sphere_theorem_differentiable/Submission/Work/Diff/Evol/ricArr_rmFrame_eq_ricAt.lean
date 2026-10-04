import Mathlib
import Submission.Work.Diff.Evol.Deps
import Submission.Work.EXT.ricAt_eq_sum_frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci array of the curvature components in an orthonormal frame

`ricArr R i j = ∑ a, R a i a j` (the trace of the curvature array) and, for the curvature
components `rmFrame g x e` of the metric `g` in the frame `e`,
`rmFrame g x e i j k l = g(R(eᵢ,eⱼ)e_l, e_k)`.  Hence
`ricArr (rmFrame g x e) i j = ∑ a, g(R(e_a, e_i)e_j, e_a)`, which is exactly the trace of the
endomorphism `w ↦ R(w, e_i)e_j` read in the orthonormal frame `e`, i.e. the Ricci tensor
`ricAt (lcOf g) x (e i) (e j)`.

The content is therefore `Work.EXT.ricAt_eq_sum_frame` (proved in
`Submission/Work/EXT/ricAt_eq_sum_frame.lean`), which identifies `ricAt` with the frame trace
`∑ j, g(R(e_j, u)v, e_j)` for an orthonormal frame `e`: the two sums agree definitionally after
unfolding `ricArr` and `rmFrame`.  The smoothness of the Levi-Civita connection required by that
lemma is the first component of the hypothesis `LCSmooth I M`.
-/

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem ricArr_rmFrame_eq_ricAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (i j : Fin (Module.finrank ℝ E)) :
    ricArr (rmFrame g x e) i j = ricAt (lcOf g) x (e i) (e j) := by
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  rw [Work.EXT.ricAt_eq_sum_frame g hcov x e he (e i) (e j)]
  rfl

end Work.Diff.Evol
