import Mathlib
import Submission.Work.Morse.contMDiff_push
import Submission.Work.Morse.Transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The chart expression of a function `f : M → N` into an arbitrary manifold, in the pushed
forward structure, is the chart expression in the original structure composed with `L.symm`. -/
lemma writtenInExtChartAt_push_general
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E'' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (L : E ≃L[ℝ] E') (x : M) (f : M → N) :
    (letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L);
      writtenInExtChartAt (modelWithCornersSelf ℝ E') I' x f)
      = fun z => writtenInExtChartAt I I' x f (L.symm z) := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  funext z
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [extChartAt_push_symm_coe]

/-- Pointwise form of `Work.Morse.contMDiff_push_iff`: smoothness at a point, for a function into
an arbitrary manifold, is invariant under pushing the atlas of `M` forward along
`Work.Morse.modelHomeo I L`. -/
private theorem contMDiffAt_push_aux_general
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E'' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (L : E ≃L[ℝ] E') (f : M → N) (x : M) :
    (letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L);
      ContMDiffAt (modelWithCornersSelf ℝ E') I' ∞ f x) ↔ ContMDiffAt I I' ∞ f x := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  rw [contMDiffAt_iff, contMDiffAt_iff]
  rw [show (↑(extChartAt I' (f x)) ∘ f ∘ ↑(extChartAt (modelWithCornersSelf ℝ E') x).symm)
        = writtenInExtChartAt (modelWithCornersSelf ℝ E') I' x f from rfl,
     show (↑(extChartAt I' (f x)) ∘ f ∘ ↑(extChartAt I x).symm)
        = writtenInExtChartAt I I' x f from rfl]
  rw [writtenInExtChartAt_push_general L x f]
  rw [extChartAt_push_coe L x]
  simp only []
  have h1 := ModelWithCorners.range_eq_univ (modelWithCornersSelf ℝ E')
  have h2 := ModelWithCorners.range_eq_univ I
  rw [h1, h2]
  refine and_congr_right fun _ => ?_
  rw [contDiffWithinAt_univ, contDiffWithinAt_univ]
  exact ContinuousLinearEquiv.contDiffAt_comp_iff (𝕜 := ℝ) (n := ∞)
    (f := writtenInExtChartAt I I' x f)
    (x := (extChartAt I x) x) L.symm

theorem contMDiff_push_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E'' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (L : E ≃L[ℝ] E') (f : M → N) :
    (letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L);
      ContMDiff (modelWithCornersSelf ℝ E') I'
        (WithTop.some (⊤ : WithTop ℕ) : WithTop (WithTop ℕ)) f) ↔
      ContMDiff I I' (WithTop.some (⊤ : WithTop ℕ) : WithTop (WithTop ℕ)) f := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  simp only [ContMDiff]
  exact forall_congr' fun x => contMDiffAt_push_aux_general L f x

end Work.Morse
