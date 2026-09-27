import Mathlib
import Submission.Work.Drive.N2.HeightBasics
import Submission.Work.Drive.N2.ChartSplit
import Submission.Work.Projection.Defs
import Submission.Work.Projection.mfderiv_chartAt_decomp

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace in
/-- If `x` is a critical point of the height function `h_v = ⟪v, e ·⟫` of a smooth map `e : M → ℝ⁵`,
then the chart representation `y ↦ ⟪v, F y⟫` (with `F = chartRep e p`) has vanishing derivative at
the image of `x` under the chart at `p`. -/
theorem fderiv_chartHeight_eq_zero_of_isCritical {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin 5)) (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e)
    (v : EuclideanSpace ℝ (Fin 5)) (p x : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (hc : Work.Drive.Morse.IsCritical (Work.Drive.N2.heightFun e v) x) :
    fderiv ℝ (Work.Drive.N2.chartHeight (Work.Projection.chartRep e p) v)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) p) x) = 0 := by
  -- The chart at `p`, and the identification of the chart representation of the height function
  -- with the height function precomposed with the inverse chart.
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) p
  have hG : Work.Drive.N2.chartHeight (Work.Projection.chartRep e p) v
      = Work.Drive.N2.heightFun e v ∘ c.symm := by
    funext y
    simp [Work.Drive.N2.chartHeight, Work.Projection.chartRep, Work.Drive.N2.heightFun, c]
  rw [hG]
  -- Chain rule: the manifold derivative of the composite `h_v ∘ c.symm`.
  have hcs : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm (c x) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) (c.map_source hx)
  have hfd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (Work.Drive.N2.heightFun e v) (c.symm (c x)) :=
    (Work.Drive.N2.contMDiff_heightFun e v he).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (c x) (f := c.symm) (g := Work.Drive.N2.heightFun e v) hfd hcs
  have hzero : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Work.Drive.N2.heightFun e v ∘ c.symm) (c x) = 0 := by
    rw [hchain]
    have h1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Work.Drive.N2.heightFun e v) (c.symm (c x)) = 0 := by
      rw [c.left_inv hx]; exact hc
    rw [h1, ContinuousLinearMap.zero_comp]
  -- On model spaces the manifold derivative is the ordinary derivative.
  have hdiff := mfderiv_eq_fderiv (𝕜 := ℝ) (f := Work.Drive.N2.heightFun e v ∘ c.symm) (x := c x)
  rw [← hdiff]
  exact hzero

end Work.Drive.N2
