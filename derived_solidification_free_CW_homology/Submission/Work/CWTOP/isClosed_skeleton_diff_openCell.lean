import Mathlib

namespace Work.CWTOP

open Topology Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-! ## Auxiliary set-theoretic manipulations -/

lemma sdiff_inter_eq_of_subset {α : Type*} {S T U : Set α} (hU : U ⊆ S) :
    (S \ T) ∩ U = U \ T := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨⟨_, hxt⟩, hxu⟩; exact ⟨hxu, hxt⟩
  · rintro ⟨hxu, hxt⟩; exact ⟨⟨hU hxu, hxt⟩, hxu⟩

lemma sdiff_inter_eq_of_subset_disjoint {α : Type*} {S T U : Set α} (hU : U ⊆ S)
    (hdj : Disjoint U T) : (S \ T) ∩ U = U := by
  rw [sdiff_inter_eq_of_subset hU, sdiff_eq_left.mpr hdj]

/-! ## The cell calculus input -/

/-- A closed cell of dimension `< N` does not meet an open `N`-cell. -/
lemma disjoint_closedCell_openCell_of_lt {n N : ℕ} {i : RelCWComplex.cell C n}
    (j : RelCWComplex.cell C N) (h : n < N) :
    Disjoint (RelCWComplex.closedCell n i) (RelCWComplex.openCell N j) :=
  Disjoint.mono_left
    ((RelCWComplex.closedCell_subset_skeletonLT n i).trans
      (RelCWComplex.skeletonLT_mono (by exact_mod_cast h : (n : ℕ∞) + 1 ≤ (N : ℕ∞))))
    (RelCWComplex.disjoint_skeletonLT_openCell (C := C) (D := ∅) (le_refl (N : ℕ∞)))

/-- The closed cell of a cell is disjoint from its own boundary. -/
lemma disjoint_cellFrontier_openCell (N : ℕ) (j : RelCWComplex.cell C N) :
    Disjoint (RelCWComplex.cellFrontier N j) (RelCWComplex.openCell N j) :=
  Disjoint.mono_left (RelCWComplex.cellFrontier_subset_skeletonLT N j)
    (RelCWComplex.disjoint_skeletonLT_openCell (C := C) (D := ∅) (le_refl (N : ℕ∞)))

/-- A closed cell of a cell of the same dimension is disjoint from the open cell of any other cell
of that dimension. -/
lemma disjoint_closedCell_openCell_of_ne {N : ℕ} {i j : RelCWComplex.cell C N} (h : i ≠ j) :
    Disjoint (RelCWComplex.closedCell N i) (RelCWComplex.openCell N j) := by
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell, disjoint_union_left]
  refine ⟨Disjoint.mono_left (RelCWComplex.cellFrontier_subset_skeletonLT N i)
      (RelCWComplex.disjoint_skeletonLT_openCell (C := C) (D := ∅) (le_refl (N : ℕ∞))), ?_⟩
  refine RelCWComplex.disjoint_openCell_of_ne (C := C) (D := ∅) ?_
  intro hh
  exact h (by simpa using hh)

/-- A closed cell is the disjoint union of its boundary and its open cell. -/
lemma closedCell_sdiff_openCell_eq_cellFrontier (N : ℕ) (j : RelCWComplex.cell C N) :
    RelCWComplex.closedCell N j \ RelCWComplex.openCell N j = RelCWComplex.cellFrontier N j := by
  have hdj := disjoint_cellFrontier_openCell (C := C) N j
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell N j,
    union_sdiff_cancel_right (fun x hx => (Set.disjoint_left.mp hdj hx.1 hx.2).elim)]

/-- If `n ≤ N` and the closed `n`-cell `i` is disjoint from the open `N`-cell `j`, then the
`n`-cell contributes its whole closed cell to the `N`-skeleton with the cell `j` removed. -/
lemma skeleton_sdiff_openCell_inter_closedCell_of_disjoint {N n : ℕ} {i : RelCWComplex.cell C n}
    (j : RelCWComplex.cell C N) (hle : n ≤ N)
    (hdj : Disjoint (RelCWComplex.closedCell n i) (RelCWComplex.openCell N j)) :
    ((RelCWComplex.skeleton C N : Set X) \ RelCWComplex.openCell N j)
        ∩ RelCWComplex.closedCell n i = RelCWComplex.closedCell n i :=
  sdiff_inter_eq_of_subset_disjoint
    ((RelCWComplex.closedCell_subset_skeleton n i).trans
      (RelCWComplex.skeleton_mono (by exact_mod_cast hle : (n : ℕ∞) ≤ (N : ℕ∞)))) hdj

/-- The `N`-cell `j` contributes its boundary to the `N`-skeleton with the cell `j` removed. -/
lemma skeleton_sdiff_openCell_inter_closedCell_self (N : ℕ) (j : RelCWComplex.cell C N) :
    ((RelCWComplex.skeleton C N : Set X) \ RelCWComplex.openCell N j)
        ∩ RelCWComplex.closedCell N j = RelCWComplex.cellFrontier N j := by
  rw [sdiff_inter_eq_of_subset (hU := RelCWComplex.closedCell_subset_skeleton N j),
    closedCell_sdiff_openCell_eq_cellFrontier]

/-! ## The main result -/

/-- The `N`-skeleton with a single open `N`-cell removed is closed. -/
theorem isClosed_skeleton_diff_openCell {X : Type*} [TopologicalSpace X] [T2Space X] {C : Set X}
    [CWComplex C] (N : ℕ) (j : RelCWComplex.cell C N) :
    IsClosed (((RelCWComplex.skeleton C N) : Set X) \ RelCWComplex.openCell N j) := by
  refine CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell (C := C) ?_ ?_
  · intro x hx
    exact (RelCWComplex.skeleton C N).subset_complex hx.1
  · intro k _ i
    rcases lt_or_ge N k with hgt | hle
    · -- the `k`-cells with `k > N` are disjoint from the `N`-skeleton
      refine Or.inl (Disjoint.mono_left Set.sdiff_subset ?_)
      exact RelCWComplex.disjoint_skeletonLT_openCell (C := C) (D := ∅) (n := (N : ℕ∞) + 1)
        (m := k) (j := i) (by exact_mod_cast hgt : (N : ℕ∞) + 1 ≤ (k : ℕ∞))
    · rcases lt_or_eq_of_le hle with hkN | hk_eq
      · -- a cell of dimension `k < N` is disjoint from the open `N`-cell `j`
        refine Or.inr ?_
        rw [skeleton_sdiff_openCell_inter_closedCell_of_disjoint (C := C) (N := N) (n := k) (i := i)
          j (le_of_lt hkN) (disjoint_closedCell_openCell_of_lt (C := C) (N := N) (i := i) j hkN)]
        exact RelCWComplex.isClosed_closedCell
      · cases hk_eq
        by_cases hij : i = j
        · -- the removed cell itself contributes only its boundary
          refine Or.inr ?_
          rw [hij, skeleton_sdiff_openCell_inter_closedCell_self (C := C) N j]
          exact RelCWComplex.isClosed_cellFrontier
        · -- the other `N`-cells contribute their whole closed cell
          refine Or.inr ?_
          rw [skeleton_sdiff_openCell_inter_closedCell_of_disjoint (C := C) (N := N) (n := N) (i := i)
            j le_rfl (disjoint_closedCell_openCell_of_ne (C := C) (N := N) hij)]
          exact RelCWComplex.isClosed_closedCell

end Work.CWTOP
