/-
  WilE5 — the *covering* clause of the assembly: the strata of `theList Me X` cover `X`.

  `theList Me X` is the cell-wise concatenation of the deduplicated flat leaves of the profile
  recursion (`CellList.lean`).  This file proves that the union of their underlying sets is
  exactly `X.set`:

  * `⊆` is immediate from `theList_subset` (every leaf of a cell is contained in the cell, and
    the cells kept in `goodCells` are contained in `X.set`);

  * `⊇` uses the *profile covering statement* `Strat.coverP` for the single-disjunct set
    `cellSemi X C` of one cell `C`: every point of a cell is covered by some flat leaf of the
    recursion run *inside that cell*.  The correctness facts needed are that `signAssign X x`
    is a good cell of `X` for `x ∈ X.set` (`Cells.cellBasic`) and that `x` lies in the cell of
    its own sign assignment (`mem_cellSemiPf_self`).  Deduplication by `uniqSets` preserves the
    union (`Pairwise.exists_mem_uniqSets`), so the covered point survives in `cellStrata`.

  The auxiliary `cover_cellStrata` below is the cell-local form of the covering statement.
-/
import Mathlib
import Submission.Work.WilE5.CellList
import Submission.Work.WilE5.Cells.cellBasic
import Submission.Work.WilE5.Cells.flatMapProps
import Submission.Work.WilE5.Pairwise.filterProps
import Submission.Work.WilE5.Strat.coverP

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

/-- **A cell is covered by its own strata.**  The flat leaves of the profile recursion inside the
single-disjunct set `cellSemi X C` (deduplicated by `uniqSets`) cover the cell.

This is `Strat.coverP` transported through `flatStratumP_X` (the underlying set of
`flatStratumP` is `flatSemiPfP`) and `mem_allStrataP`, plus the fact that `uniqSets` only drops
entries whose set already occurs (`Pairwise.exists_mem_uniqSets`). -/
theorem cover_cellStrata {p q : ℕ} (Me : Polynomial ℕ) (X : SemiPf (p + q))
    (C : Basic (p + q) X.r) :
    (cellSemi X C).set ⊆ ⋃ S ∈ cellStrata Me X C, S.X.set := by
  set Z := cellSemi X C
  set Ml := MlOf Me Z.deg p q
  set NΦ := NPhi Me Z.deg p q
  intro x hx
  have hcov := Strat.coverP Z Ml NΦ hx
  simp only [Set.mem_iUnion, exists_prop] at hcov
  obtain ⟨k, hk, τ, hτ, hxτ⟩ := hcov
  have hmemL : flatStratumP Z Ml NΦ τ ∈ allStrataP Z Ml NΦ q := by
    rw [mem_allStrataP]
    exact ⟨k, List.mem_range.mpr (Finset.mem_range.mp hk), τ, hτ, rfl⟩
  obtain ⟨T, hT, hTset⟩ := Pairwise.exists_mem_uniqSets hmemL
  rw [Set.mem_iUnion₂]
  exact ⟨T, hT, by rw [hTset]; exact hxτ⟩

theorem theListUnion {p q F : ℕ} (Me : Polynomial ℕ) (X : WilkiesDesign.E.SemiPf (p + q))
    (hX : X.fmt ≤ F) :
    (⋃ S ∈ Work.WilE5.theList Me X, S.X.set) = X.set := by
  apply Set.Subset.antisymm
  · -- Every leaf lies inside the cell it comes from, hence inside `X.set`.
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨S, hS, hxS⟩ := hx
    exact theList_subset Me X S hS hxS
  · -- A point of `X.set` lies in its own sign cell, which is covered by that cell's strata.
    intro x hx
    have hσ : signAssign X x ∈ goodCells X := signAssign_mem_goodCells X hx
    have hxcell : x ∈ (cellSemi X (cell X (signAssign X x))).set := by
      have hZ : cellSemi X (cell X (signAssign X x)) = cellSemiPf X (signAssign X x) := rfl
      rw [hZ]
      exact mem_cellSemiPf_self X hx.1
    have hx' : x ∈ ⋃ S ∈ cellStrata Me X (cell X (signAssign X x)), S.X.set :=
      cover_cellStrata Me X _ hxcell
    rw [Set.mem_iUnion₂] at hx'
    obtain ⟨S, hS, hxS⟩ := hx'
    rw [Set.mem_iUnion₂]
    exact ⟨S, (mem_theList).mpr ⟨signAssign X x, hσ, hS⟩, hxS⟩

end Work.WilE5
