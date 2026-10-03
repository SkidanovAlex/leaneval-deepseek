import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.ChartedSpace

noncomputable section

open Set Manifold
open scoped Manifold Topology ContDiff

namespace Commons.Geometry.Manifold

/-- Chart transitions of a one-dimensional complex manifold are complex-analytic on
their (open) domain of definition. -/
theorem chart_transition_analyticOnNhd {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (x y : X) :
    AnalyticOnNhd ℂ ((chartAt ℂ x).symm.trans (chartAt ℂ y))
      ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
  let e : OpenPartialHomeomorph ℂ ℂ := (chartAt ℂ x).symm.trans (chartAt ℂ y)
  change AnalyticOnNhd ℂ e e.source
  have hG : e ∈ contDiffGroupoid (1 : ℕ∞ω) (modelWithCornersSelf ℂ ℂ) := by
    dsimp [e]
    exact StructureGroupoid.compatible (contDiffGroupoid (1 : ℕ∞ω) (modelWithCornersSelf ℂ ℂ))
      (chart_mem_atlas ℂ x) (chart_mem_atlas ℂ y)
  have hcd : ContDiffOn ℂ (1 : ℕ∞ω) e e.source := by
    rw [contDiffGroupoid] at hG
    rw [mem_groupoid_of_pregroupoid] at hG
    simpa [contDiffPregroupoid] using hG.1
  have hdiff : DifferentiableOn ℂ e e.source := hcd.differentiableOn_one
  exact (DifferentiableOn.analyticOnNhd (f := (e : ℂ → ℂ)) hdiff e.open_source)

end Commons.Geometry.Manifold

end
