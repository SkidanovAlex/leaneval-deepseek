import Mathlib
import Submission.Work.Projection.GeneralDefs

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- The derivative of a smooth map `f` from a boundaryless manifold modelled on `E` to `ℝ^{k+1}`
at a point `x` of the source of the extended chart at `p` factors through the derivative of the
extended chart, the remaining factor being the Fréchet derivative of the chart representation
of `f`. -/
theorem mfderiv_extChartAt_decomp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) ∞ f) (p x : M)
    (hx : x ∈ (extChartAt I p).source) :
    mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x =
      (fderiv ℝ (Work.Projection.chartRepI (I := I) f p) ((extChartAt I p) x)) ∘L
      mfderiv I 𝓘(ℝ, E) (extChartAt I p) x := by
  -- `x` lies in the chart source, since the extended chart has the same source as the chart
  have hx' : x ∈ (chartAt H p).source := by rwa [extChartAt_source] at hx
  -- the extended chart is differentiable at `x`
  have hc : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) x := mdifferentiableAt_extChartAt hx'
  -- its inverse is differentiable at the image point (here `I` is boundaryless, so
  -- differentiability within `range I` is genuine differentiability)
  have hcs : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm ((extChartAt I p) x) := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := p)
      ((extChartAt I p).map_source hx)
    rw [ModelWithCorners.range_eq_univ] at h
    simpa [MDifferentiableAt, MDifferentiableWithinAt, ChartedSpace.LiftPropAt] using h
  -- `f` is differentiable at `x`
  have hfmd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x :=
    (hf x).mdifferentiableAt (by simp)
  -- hence the chart representation of `f` is differentiable at the image of `x`
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1)))
      (Work.Projection.chartRepI (I := I) f p) ((extChartAt I p) x) :=
    MDifferentiableAt.comp_of_eq ((extChartAt I p) x) hfmd hcs ((extChartAt I p).left_inv hx)
  -- chain rule for the composite `chartRepI f p ∘ extChartAt I p`
  have hcomp := mfderiv_comp x hg hc
  -- that composite agrees with `f` near `x`
  have heq : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1)))
      ((Work.Projection.chartRepI (I := I) f p) ∘ (extChartAt I p)) x =
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (k+1))) f x := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [extChartAt_source_mem_nhds' hx] with y hy
    exact Work.Projection.chartRepI_extChartAt (I := I) f p y hy
  rw [← heq, hcomp, mfderiv_eq_fderiv]
  rfl

end Work.Projection
