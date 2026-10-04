import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.sum_chartMatFun_eq_inner

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Positive semidefiniteness of the chart matrix of a smooth metric

The chart matrix `chartMatFun g x₀ y` of a smooth metric `g` in the coordinate frame of the chart
at `x₀` (see `Submission/Work/Diff/EXT/splice_defs.lean`) is positive semidefinite: for every
coefficient vector `v : Fin (Module.finrank ℝ E) → ℝ`,

`0 ≤ ∑ i, ∑ j, chartMatFun g x₀ y i j * v i * v j`.

The quadratic form is the metric of the linear combination `W = ∑ i, v i • σ i` of the coordinate
frame vectors (`Work.Diff.EXT.sum_chartMatFun_eq_inner`), so this is exactly the positive
semidefiniteness of the metric form `g.inner p` on `TangentSpace I p`, which is the field
`pos` of the Riemannian metric together with linearity in the first slot.

This is the small input consumed by
`Submission/Work/Diff/STE/Lead/det_ne_zero_smul_add_one_of_nonneg_quadForm.lean` (and by the
`posDef_of_quadForm_lower` / `quadA_posDef` family): the chart matrix is the object whose
`ε • 1 + M` form is inverted in the DeTurck/gluing argument, and the `+1` regularisation makes
sense precisely because the quadratic form of `M` is nonnegative.
-/

namespace Work.Diff.STE.Lead

/-- The metric form of a smooth metric is nonnegative on the diagonal.  Immediate from
`ContMDiffRiemannianMetric.pos` for `u ≠ 0` and from linearity in the first slot for `u = 0`. -/
private lemma smet_inner_self_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) (u : TangentSpace I x) : 0 ≤ g.inner x u u := by
  by_cases hu : u = 0
  · subst hu; simp
  · exact (g.pos x u hu).le

lemma chartMatFun_quadForm_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) (v : Fin (Module.finrank ℝ E) → ℝ) :
    0 ≤ ∑ i, ∑ j, Work.Diff.EXT.chartMatFun g x₀ y i j * v i * v j := by
  -- the quadratic form of the matrix is the same sum with the factors `v i * v j` first
  have hswap : (∑ i, ∑ j, Work.Diff.EXT.chartMatFun g x₀ y i j * v i * v j)
      = ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hswap, Work.Diff.EXT.sum_chartMatFun_eq_inner]
  -- ... and by bilinearity the value is the metric form on the frame combination
  set W := ∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (Work.Diff.EXT.bB (E := E) i)
  exact smet_inner_self_nonneg g ((extChartAt I x₀).symm y) W

end Work.Diff.STE.Lead
