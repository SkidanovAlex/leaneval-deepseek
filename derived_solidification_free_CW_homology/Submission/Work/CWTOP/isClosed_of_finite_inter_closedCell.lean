import Mathlib
import Submission.Work.CWTOP.CellDim

namespace Work.CWTOP

/-- A subset of a Hausdorff CW complex `C` whose trace on every closed cell is finite is closed
in the ambient space.

This is the weak (coherent) topology of a CW complex: `Topology.CWComplex.closed` says that
`S ⊆ C` is closed as soon as its intersection with every closed cell is closed, and each such
intersection is finite, hence closed since `X` is Hausdorff (in particular `T1`). -/
theorem isClosed_of_finite_inter_closedCell {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C] {S : Set X} (hSC : S ⊆ C) (hfin : ∀ (n : ℕ) (j : Topology.RelCWComplex.cell C n), (S ∩ Topology.RelCWComplex.closedCell n j).Finite) : IsClosed S := by
  rw [Topology.CWComplex.closed C S hSC]
  intro n j
  exact (hfin n j).isClosed

end Work.CWTOP
