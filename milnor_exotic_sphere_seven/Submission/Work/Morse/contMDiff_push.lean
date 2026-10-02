import Mathlib
import Submission.Work.Morse.Transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-- Pointwise form of `Work.Morse.contMDiff_push`: smoothness of a real function at a point is
invariant under pushing the atlas of `M` forward along `Work.Morse.modelHomeo I L`. -/
private theorem contMDiffAt_push_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (L : E ≃L[ℝ] E') (f : M → ℝ) (x : M) :
    (letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L);
      ContMDiffAt (𝓘(ℝ,E')) 𝓘(ℝ,ℝ) ∞ f x) ↔ ContMDiffAt I 𝓘(ℝ,ℝ) ∞ f x := by
  letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L)
  rw [contMDiffAt_iff, contMDiffAt_iff]
  -- rewrite both chart expressions as `writtenInExtChartAt`
  rw [show (↑(extChartAt (modelWithCornersSelf ℝ ℝ) (f x)) ∘ f ∘
        ↑(extChartAt (modelWithCornersSelf ℝ E') x).symm)
        = writtenInExtChartAt (modelWithCornersSelf ℝ E') (modelWithCornersSelf ℝ ℝ) x f
        from rfl,
     show (↑(extChartAt (modelWithCornersSelf ℝ ℝ) (f x)) ∘ f ∘ ↑(extChartAt I x).symm)
        = writtenInExtChartAt I (modelWithCornersSelf ℝ ℝ) x f from rfl]
  -- the pushed chart expression is the original one precomposed with `L.symm`
  rw [writtenInExtChartAt_push L x f]
  -- the centre point is the image of the original centre under `L`
  rw [extChartAt_push_coe L x]
  simp only []
  -- both `range`s are everything (`I.Boundaryless`, and the self model is boundaryless)
  have h1 := ModelWithCorners.range_eq_univ (modelWithCornersSelf ℝ E')
  have h2 := ModelWithCorners.range_eq_univ I
  rw [h1, h2]
  refine and_congr_right fun _ => ?_
  rw [contDiffWithinAt_univ, contDiffWithinAt_univ]
  exact ContinuousLinearEquiv.contDiffAt_comp_iff (𝕜 := ℝ) (n := ∞)
    (f := writtenInExtChartAt I (modelWithCornersSelf ℝ ℝ) x f)
    (x := (extChartAt I x) x) L.symm

/-- Smoothness of a real function is invariant under pushing the atlas of `M` forward along
`Work.Morse.modelHomeo I L` (`Submission.Work.Morse.Transfer`).  Use
`Work.Morse.extChartAt_push_coe`, `Work.Morse.extChartAt_push_symm_coe`,
`Work.Morse.writtenInExtChartAt_push` and `contMDiffAt_iff`; the relevant invariance of `ContDiffAt`
under composition with a continuous linear equivalence is `ContinuousLinearEquiv.contDiffAt_comp_iff`
(or `ContDiffAt.comp` in both directions). -/
theorem contMDiff_push {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (L : E ≃L[ℝ] E') (f : M → ℝ) :
    (letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L);
      ContMDiff (𝓘(ℝ,E')) 𝓘(ℝ,ℝ) ∞ f) ↔ ContMDiff I 𝓘(ℝ,ℝ) ∞ f := by
  letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L)
  simp only [ContMDiff]
  exact forall_congr' fun x => contMDiffAt_push_aux L f x

end Work.Morse
