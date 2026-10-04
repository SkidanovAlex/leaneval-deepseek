import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

/-- **The chart matrix of a fixed smooth metric is continuous at the chart centre.**
For a smooth metric `g : SMet I M` and a chart centre `x₀ : M`, each matrix entry
`y ↦ chartMatFun g x₀ y i j = g.inner ((extChartAt I x₀).symm y) (σ i) (σ j)` is continuous at
`y₀ = (extChartAt I x₀) x₀`.

This is the `T2Space`-free and `I.Boundaryless`-free version of `Submission.Distance.continuousAt_chartGram`:
compose `Mathlib`'s `continuousAt_extChartAt_symm x₀ : ContinuousAt (extChartAt I x₀).symm ((extChartAt I x₀) x₀)`
(which needs no `Boundaryless`) with the continuity at `x₀` of `x ↦ g.inner x (σ i x) (σ j x)`; the latter follows
either from `ContMDiffRiemannianMetric.contMDiff` plus `ContMDiffWithinAt.clm_bundle_apply₂` together with
`Work.Diff.EXT.contMDiffAt_frameVector` (T2-free), or by setting
`letI : RiemannianBundle (fun x => TangentSpace I x) := ⟨g.toRiemannianMetric⟩` and using
`ContMDiffAt.inner_bundle`. -/
theorem continuousAt_chartMatFun_centre
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun y : E => Work.Diff.EXT.chartMatFun g x₀ y i j)
      ((extChartAt I x₀) x₀) := by
  -- the two coordinate frame vectors of the chart at `x₀` are smooth at `x₀`
  have hx0 : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hY : CMDiffAt ∞
      (T% (fun y : M => Submission.Geodesic.frameVector (I := I) x₀ y (bB i))) x₀ :=
    contMDiffAt_frameVector (I := I) x₀ (bB i) hx0
  have hZ : CMDiffAt ∞
      (T% (fun y : M => Submission.Geodesic.frameVector (I := I) x₀ y (bB j))) x₀ :=
    contMDiffAt_frameVector (I := I) x₀ (bB j) hx0
  -- the metric, as a smooth section of the bundle of bilinear forms at `x₀`
  have hψ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g.inner m)) x₀ :=
    g.contMDiff x₀
  -- evaluate it on the two frame vectors
  have hmain : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m
        (g.inner m (Submission.Geodesic.frameVector (I := I) x₀ m (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ m (bB j)))) univ x₀ :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : M => m)
      (v := fun m : M => Submission.Geodesic.frameVector (I := I) x₀ m (bB i))
      (w := fun m : M => Submission.Geodesic.frameVector (I := I) x₀ m (bB j))
      (ψ := fun m : M => g.inner m) (s := univ) (x := x₀) hψ hY hZ
  -- unfold the (trivial) bundle `Bundle.Trivial M ℝ`
  have hsec : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun m : M => g.inner m (Submission.Geodesic.frameVector (I := I) x₀ m (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ m (bB j))) univ x₀ := by
    have := (contMDiffWithinAt_section (IB := I) (F := ℝ) (E := Bundle.Trivial M ℝ)
      (s := fun m : M => g.inner m (Submission.Geodesic.frameVector (I := I) x₀ m (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ m (bB j)))
      (a := univ) (x₀ := x₀) (n := ∞)).mp hmain
    simpa using this
  have hcont : ContinuousAt (fun m : M => g.inner m
      (Submission.Geodesic.frameVector (I := I) x₀ m (bB i))
      (Submission.Geodesic.frameVector (I := I) x₀ m (bB j))) x₀ :=
    (continuousWithinAt_univ _ _).1 hsec.continuousWithinAt
  -- compose with the chart inverse, which is continuous at the chart coordinate of `x₀`
  have hsymm : ContinuousAt (extChartAt I x₀).symm ((extChartAt I x₀) x₀) :=
    continuousAt_extChartAt_symm x₀
  have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  exact hcont.comp_of_eq hsymm hleft

end Work.Diff.EXT
