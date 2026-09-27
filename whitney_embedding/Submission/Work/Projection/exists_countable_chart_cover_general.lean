import Mathlib

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- A nonempty Hausdorff second-countable manifold modelled on `(E, H)` admits a countable family
of points whose charts cover the manifold. -/
theorem exists_countable_chart_cover_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [SecondCountableTopology M] [Nonempty M] :
    ∃ p : ℕ → M, (Set.univ : Set M) ⊆ ⋃ i, (chartAt H (p i)).source := by
  -- The chart sources form an open cover of `M` (each point lies in its own chart source), and a
  -- second-countable space is Lindelöf, so this cover has a countable subcover; the centers of the
  -- charts in that subcover give the desired family.
  obtain ⟨p, hp⟩ := IsLindelof.indexed_countable_subcover (s := Set.univ)
    isLindelof_univ (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source)
    (fun x _ => Set.mem_iUnion.2 ⟨x, mem_chart_source H x⟩)
  exact ⟨p, hp⟩

end Work.Projection
