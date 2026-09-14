import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace Commons.Topology.Algebra.Module

/-- A finite-dimensional subspace containing a dense subset of a Hausdorff
topological vector space over a complete nontrivially normed field is the
whole space. -/
theorem eq_top_of_finiteDimensional_of_dense {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E] {s : Set E} (hs : Dense s)
    (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] (hS : s ⊆ (S : Set E)) : S = ⊤ := by
  have hSclosed : IsClosed (S : Set E) := S.closed_of_finiteDimensional
  have hSdense : Dense (S : Set E) := Dense.mono hS hs
  have hS_univ : (S : Set E) = Set.univ :=
    (hSclosed.closure_eq.symm).trans hSdense.closure_eq
  apply le_antisymm
  · exact le_top
  · intro x hx
    change x ∈ (S : Set E)
    rw [hS_univ]
    trivial

end Commons.Topology.Algebra.Module