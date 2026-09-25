import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Neighborhood

open Filter Topology

universe u v

namespace Commons.Topology.Profinite

/-- A homomorphism with open kernel into a discrete group is continuous. -/
theorem continuous_of_open_ker {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {F : Type v} [Group F] [TopologicalSpace F] [DiscreteTopology F]
    (ψ : G →* F) (hker : IsOpen (ψ.ker : Set G)) : Continuous ψ := by
  exact continuous_of_continuousAt_one ψ (by
    rw [continuousAt_def]
    intro A hA
    have h1A : (1 : F) ∈ A := by
      have hA' : A ∈ (pure (ψ 1) : Filter F) := by
        simpa [nhds_discrete F] using hA
      have h' : ψ 1 ∈ A := Filter.mem_pure.mp hA'
      simpa using h'
    apply Filter.mem_of_superset (x := (ψ.ker : Set G)) (y := ψ ⁻¹' A)
    · exact hker.mem_nhds (by simp)
    · intro x hx
      have hx1 : ψ x = 1 := by simpa using hx
      simpa [hx1] using h1A)

end Commons.Topology.Profinite