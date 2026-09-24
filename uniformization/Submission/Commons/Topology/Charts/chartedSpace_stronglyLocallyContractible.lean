import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Homotopy.LocallyContractible

namespace Commons.Topology.Charts

/-- A normed space over `ℝ` is strongly locally contractible: the open balls around a point
form a neighborhood basis, and each open ball is convex, hence contractible. -/
theorem normedSpace_stronglyLocallyContractible (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : StronglyLocallyContractibleSpace E := by
  refine StronglyLocallyContractibleSpace.of_bases (ι := ℝ)
    (p := fun x r => 0 < r) (s := fun x r => Metric.ball x r) ?_ ?_
  · intro x
    exact Metric.nhds_basis_ball
  · intro x r hr
    exact Metric.contractibleSpace_ball hr

/-- A complex charted space is strongly locally contractible. -/
theorem chartedSpace_stronglyLocallyContractible {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] : StronglyLocallyContractibleSpace X := by
  refine StronglyLocallyContractibleSpace.of_bases (ι := ℝ)
    (p := fun x r => 0 < r ∧ Metric.ball (chartAt ℂ x x) r ⊆ (chartAt ℂ x).target)
    (s := fun x r => (chartAt ℂ x).symm '' Metric.ball (chartAt ℂ x x) r) ?_ ?_
  · intro x
    rw [← (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)]
    exact ((Metric.nhds_basis_ball (x := chartAt ℂ x x)).restrict_subset
      (chart_target_mem_nhds ℂ x)).map _
  · intro x r ⟨hr, hrsub⟩
    exact ((chartAt ℂ x).symm.homeomorphOfImageSubsetSource hrsub rfl).contractibleSpace_iff.mp
      (Metric.contractibleSpace_ball (x := chartAt ℂ x x) hr)

end Commons.Topology.Charts