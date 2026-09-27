import Mathlib

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- A nonempty Hausdorff second-countable `n`-manifold admits a countable family of points whose
charts cover the manifold. -/
theorem exists_countable_chart_cover (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    [Nonempty M] :
    ∃ p : ℕ → M, (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source := by
  -- The chart sources form an open cover, and a second-countable space is Lindelöf, so this cover
  -- has a countable subcover; the centers of that subcover give the desired family.
  obtain ⟨p, hp⟩ := IsLindelof.indexed_countable_subcover (s := Set.univ)
    isLindelof_univ (fun x : M => (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source)
    (fun x _ => Set.mem_iUnion.2 ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin n)) x⟩)
  exact ⟨p, hp⟩

end Work.Projection
