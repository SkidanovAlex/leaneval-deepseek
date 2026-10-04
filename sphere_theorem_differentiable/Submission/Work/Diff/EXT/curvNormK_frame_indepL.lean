import Submission.Work.Diff.EXT.curvNormK_frame_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `curvNormK_frame_indepL`: the `...L` alias of `curvNormK_frame_indep`

This module used to be a *copy* of `Submission.Work.Diff.EXT.curvNormK_frame_indep`, identical in
every declaration name and statement, differing only in that it imported `frobSqN_frame_indepL`
(a copy of `frobSqN_frame_indep` in which the `Finset.sum_comm` helper was renamed, to avoid the
then-existing clash with `Work.Diff.GE.rot5` of `GE/norms_defs`).

That clash has been removed on the `GE` side, so the copy is retired: this module re-exports the
original and keeps only the alias `curvNormK_frame_indepL`, which the rest of the `...L` chain
(`covK_linearL`, `ckt_step_aux`, `curvNormK_jointSmooth`) refers to by name.  All other names
(`dirF`, `ckt`, `SmoothF`, `TensProp`, `Kpt`, `mkT`, ...) now come from the original module, so a
single file may import this module together with the `GE`/plain chain.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **Frame independence of `|∇^k Rm|²`** (alias of `Work.Diff.EXT.curvNormK_frame_indep`). -/
theorem curvNormK_frame_indepL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) {g : Submission.Diff.SMet I M} (x : M) (k : ℕ)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) :
    Work.Diff.EXT.curvNormK g x k =
      ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (Work.Diff.EXT.covKRmC g x e k ι i j l m) ^ 2 :=
  curvNormK_frame_indep hLC x k e he

end Work.Diff.EXT
