import Mathlib
import Submission.Work.LeviCivita.ChartMetric

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LeviCivita

open scoped Manifold ContDiff Bundle Topology in
theorem contDiffAt_chartGram
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (a b : E) :
    ContDiffAt ℝ ∞ (fun q : E ↦
      Submission.ChartConnection.chartGram (I := I) x₀ ((extChartAt I x₀).symm q) a b)
      (extChartAt I x₀ p) := by
  -- The chart metric is smooth in the base point on the chart at `x₀`; this is the smoothness of
  -- the inner product of the two (locally smooth) constant-coordinate frame sections.
  have hF : CMDiffAt ∞
      (fun q : M => Submission.ChartConnection.chartGram (I := I) x₀ q a b) p :=
    ContMDiffAt.inner_bundle
      (Submission.Geodesic.contMDiffAt_frameSection (I := I) x₀ a hp)
      (Submission.Geodesic.contMDiffAt_frameSection (I := I) x₀ b hp)
  have hsrc : p ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have htarget : extChartAt I x₀ p ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hsrc
  -- The inverse chart `(extChartAt I x₀).symm` is smooth at `extChartAt I x₀ p`: it is smooth on
  -- the chart target, and `I.Boundaryless` makes the range condition vacuous.
  have hsymm0 : ContMDiffWithinAt 𝓘(ℝ, E) I ∞
      (fun q : E => (extChartAt I x₀).symm q) (Set.range I) (extChartAt I x₀ p) :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) x₀ htarget
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun q : E => (extChartAt I x₀).symm q) (extChartAt I x₀ p) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ] at hsymm0
    exact contMDiffWithinAt_univ.mp hsymm0
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
    (extChartAt I x₀).left_inv hsrc
  have hF' : CMDiffAt ∞
      (fun q : M => Submission.ChartConnection.chartGram (I := I) x₀ q a b)
      ((extChartAt I x₀).symm (extChartAt I x₀ p)) := by
    rw [hleft]; exact hF
  have hcomp := ContMDiffAt.comp _ hF' hsymm
  exact contMDiffAt_iff_contDiffAt.mp hcomp

end Work.LeviCivita
