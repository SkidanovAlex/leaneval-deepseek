import Mathlib
import Submission.Commons.Topology.Plane.exists_dyadic_exhaustion_of_isOpen_complex
import Submission.Commons.Topology.Plane.exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex

/-!
# A finite union of dyadic cells is homotopy equivalent to a 1-dimensional subcomplex

For `n : ℕ` and a finite set `S` of indices, the finite union `K = ⋃ p ∈ S, dyadicCell n p`
of closed dyadic squares of level `n` in `ℂ` is a finite subcomplex of the standard dyadic
square complex.  Every such polyomino carries a 1-dimensional CW subcomplex `G ⊆ K`
(no cells in dimension `≥ 2`) which is homotopy equivalent to `K` — the classical
"spine" of the polyomino.

This is the specialisation to `dyadicCell` of the commons theorem
`Commons.Topology.Plane.exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex`,
which is stated for the (definitionally identical) set `dSq`.
-/

namespace Commons.Topology.Plane

theorem exists_homotopyEquiv_subgraph_oneDimCW_of_union_dyadicCells
    (n : ℕ) (S : Finset (ℤ × ℤ)) :
    ∃ (G : Set ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p))
      (hC : @Topology.CWComplex ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p) _ G),
      (∀ m : ℕ, 2 ≤ m →
        IsEmpty (@Topology.CWComplex.cell ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p) _ G hC m)) ∧
      Nonempty (@ContinuousMap.HomotopyEquiv ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p) ↥G _ _) := by
  obtain ⟨G, hC, hdim, he⟩ :=
    Commons.Topology.Plane.exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex n S
  exact ⟨G, hC, hdim, he⟩

end Commons.Topology.Plane
