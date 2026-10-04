import Submission.Work.Diff.EXT.covK_linear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `covK_linearL`: the `...L` alias of `covK_linear`

This module used to be a *copy* of `Submission.Work.Diff.EXT.covK_linear` (auxiliaries `quadF`,
`ckt_quadF`, `smoothF_mkT`, `smoothTField_quadF`, `covK_slot_add`, `covK_slot_smul`, ...), made
"clash-free" only in that it imported `curvNormK_frame_indepL` (a copy of `curvNormK_frame_indep`
in which the `Finset.sum_comm` helper was renamed, to avoid the then-existing clash with
`Work.Diff.GE.rot5` of `GE/norms_defs`).

That clash has been removed on the `GE` side, so the copy is retired: this module re-exports the
original and keeps only the alias `covK_linearL`, which `curvNormK_jointSmooth` and
`covK_valueDepN` refer to by name.  Every other name comes from the original module, so a single
file may now import both the `...L` and the plain/`GE` chains.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **`C^∞(M)`-linearity of `∇^k Rm` in its `k + 4` field slots** (alias of
`Work.Diff.EXT.covK_linear`). -/
theorem covK_linearL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (k : ℕ) :
    KrLinear (I := I) (M := M) g k :=
  covK_linear hLC g k

end Work.Diff.EXT
