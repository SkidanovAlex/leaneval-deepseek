/-
  WilE5 — the pairwise-disjointness clause of the assembly.

  `theList Me X` is the concatenation, over the good sign cells `σ` of `X`, of the deduplicated
  flat leaves of the profiled recursion run inside the cell `cellSemi X (cell X σ)`.  This file
  proves that the concatenated list is pairwise disjoint:

  * *within one cell*: two flat leaves of the same cell's recursion either are disjoint or have
    equal underlying sets (`Cells.leafDisj`), and `uniqSets` keeps only the first occurrence of
    each set (`Pairwise.pairwise_uniqSets`);
  * *across two different cells*: every leaf of a cell is contained in that cell
    (`cellStrata_subset_cell`, from `flatStratumP_X` + `flatSemiPf_set_eq`), and the cells of
    distinct sign assignments are disjoint (`cells_disjoint`);
  * the two cases are glued by `Cells.flatMapProps` (which also needs `goodCells X` to be
    `Nodup`, true because it is a `filter` of `Finset.univ.toList`).
-/
import Mathlib
import Submission.Work.WilE5.CellList
import Submission.Work.WilE5.Cells.cellBasic
import Submission.Work.WilE5.Cells.leafDisj
import Submission.Work.WilE5.Cells.flatMapProps
import Submission.Work.WilE5.Pairwise.filterProps

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE5

open WilkiesDesign WilkiesDesign.E

/-- A member of `cellStrata Me X C` has its underlying set inside the cell `C`. -/
theorem cellStrata_subset_cell {p q : ℕ} (Me : Polynomial ℕ) (X : SemiPf (p + q))
    (C : Basic (p + q) X.r) {S : Stratum p q} (hS : S ∈ cellStrata Me X C) :
    S.X.set ⊆ (cellSemi X C).set := by
  obtain ⟨k, -, τ, -, rfl⟩ := exists_state_of_mem_cellStrata hS
  rw [flatStratumP_X, flatSemiPfP_eq, Strat.flatSemiPf_set_eq]
  exact Set.inter_subset_left

theorem theListPairwise {p q F : ℕ} (Me : Polynomial ℕ) (X : WilkiesDesign.E.SemiPf (p + q))
    (hX : X.fmt ≤ F) :
    (Work.WilE5.theList Me X).Pairwise (fun S T => Disjoint S.X.set T.X.set) := by
  have hnodup : (goodCells X).Nodup := by
    rw [goodCells, allSigns]
    exact List.Nodup.filter _ (Finset.nodup_toList _)
  refine (Cells.flatMapProps (goodCells X)
      (fun σ => cellStrata Me X (cell X σ)) hnodup ?_ ?_).1
  · -- two leaves of the same cell: disjoint or equal
    intro σ hσ
    refine Pairwise.pairwise_uniqSets ?_
    intro S hS T hT hmeet
    obtain ⟨k, hk, σ', hσ', rfl⟩ := (mem_allStrataP).mp hS
    obtain ⟨k', hk', τ', hτ', rfl⟩ := (mem_allStrataP).mp hT
    have hkF : k ∈ Finset.range (q + 1) := Finset.mem_range.mpr (List.mem_range.mp hk)
    have hkF' : k' ∈ Finset.range (q + 1) := Finset.mem_range.mpr (List.mem_range.mp hk')
    have heq := Cells.leafDisj X (cell X σ)
      (MlOf Me (cellSemi X (cell X σ)).deg p q) (NPhi Me (cellSemi X (cell X σ)).deg p q)
      k hkF k' hkF' σ' hσ' τ' hτ' hmeet
    simpa only [flatStratumP_X] using heq
  · -- leaves of two different cells: contained in disjoint cells
    intro σ hσ σ' hσ' hne S hS T hT
    have h1 : S.X.set ⊆ (cellSemi X (cell X σ)).set := cellStrata_subset_cell Me X _ hS
    have h2 : T.X.set ⊆ (cellSemi X (cell X σ')).set := cellStrata_subset_cell Me X _ hT
    exact Disjoint.mono h1 h2 (cells_disjoint X hne)

end Work.WilE5
