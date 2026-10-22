import Mathlib
import Submission.Work.CWTOP.CellDim

namespace Work.CWTOP

/-- A sequence whose `k`-th term lies in an open cell of dimension `> k` escapes every closed
cell: only the first `d` terms can meet the closed `d`-cell.

The point is that `x k ∈ closedCell d i ⊆ skeleton C d` together with
`x k ∈ openCell n j` and `k < n` forces `n ≤ d` (an open `n`-cell misses the `d`-skeleton),
hence `k < d`. -/
theorem finite_inter_closedCell_of_range {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C] {x : ℕ → X} (hx : ∀ k, ∃ (n : ℕ) (j : Topology.RelCWComplex.cell C n), k < n ∧ x k ∈ Topology.RelCWComplex.openCell n j) {T : Set X} (hT : T ⊆ Set.range x) (d : ℕ) (i : Topology.RelCWComplex.cell C d) : (T ∩ Topology.RelCWComplex.closedCell d i).Finite := by
  -- Only the indices `k < d` can contribute a point of the closed `d`-cell.
  have hkey : ∀ k, x k ∈ Topology.RelCWComplex.closedCell d i → k < d := by
    intro k hk
    obtain ⟨n, j, hkn, hxkj⟩ := hx k
    have hmem : x k ∈ (Topology.RelCWComplex.skeleton C d : Set X) :=
      Topology.RelCWComplex.closedCell_subset_skeleton d i hk
    have hnd : n ≤ d := le_of_mem_openCell_of_mem_skel hxkj hmem
    omega
  have hsub : T ∩ Topology.RelCWComplex.closedCell d i ⊆ x '' {k | k < d} := by
    rintro y ⟨hyT, hyc⟩
    obtain ⟨k, rfl⟩ := hT hyT
    exact ⟨k, hkey k hyc, rfl⟩
  exact (Set.finite_Iio d).image x |>.subset hsub

end Work.CWTOP
