import Mathlib
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

namespace Work.Drive

open scoped Manifold Topology

/-- The transition map between two charts of a one-dimensional complex manifold has non-zero
derivative at every point of its domain of definition.  It is the germ of a local biholomorphism,
so its derivative cannot vanish. -/
theorem deriv_chart_transition_ne_zero {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x y : X} (hy : y ∈ (chartAt ℂ x).source) :
    deriv ((chartAt ℂ x).symm.trans (chartAt ℂ y)) ((chartAt ℂ x) y) ≠ 0 := by
  have hmem : (chartAt ℂ x) y ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.symm_source]
      exact (chartAt ℂ x).map_source hy
    · show (chartAt ℂ x).symm ((chartAt ℂ x) y) ∈ (chartAt ℂ y).source
      rw [(chartAt ℂ x).left_inv hy]
      exact mem_chart_source ℂ y
  have hana : AnalyticAt ℂ
      (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ) ((chartAt ℂ x) y) :=
    Commons.Geometry.Manifold.chart_transition_analyticOnNhd x y _ hmem
  obtain ⟨r, hrpos, hrsub⟩ :=
    Metric.isOpen_iff.mp ((chartAt ℂ x).symm.trans (chartAt ℂ y)).open_source _ hmem
  have hinj : Set.InjOn (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ → ℂ)
      (Metric.ball ((chartAt ℂ x) y) r) :=
    ((chartAt ℂ x).symm.trans (chartAt ℂ y)).injOn.mono hrsub
  exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hrpos hana hinj

end Work.Drive
