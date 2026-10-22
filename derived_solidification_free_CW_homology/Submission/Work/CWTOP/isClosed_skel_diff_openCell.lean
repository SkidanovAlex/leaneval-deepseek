import Mathlib
import Submission.Work.CWTOP.Basic

/-!
# The `(n+1)`-skeleton with one open `(n+1)`-cell removed is closed

For a CW complex `C` in a Hausdorff space `X`, the set `skel C (n+1) \ openCell (n+1) j` is closed.

Mathematically this set is the carrier of the subcomplex consisting of all cells of dimension `≤ n`
together with the `(n+1)`-cells other than `j`: indeed the boundary `cellFrontier (n+1) j` of the
removed cell lies in the `n`-skeleton, so removing the *open* cell `j` from the `(n+1)`-skeleton
only deletes cells of dimension `n+1` different from `j`. Formally we use the weak topology
criterion `CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell`: for every
cell `(m, i)` either the set is disjoint from `openCell m i` (dimensions `> n+1`, and `m = n+1` with
`i = j`) or its intersection with `closedCell m i` is the whole closed cell `closedCell m i`
(dimensions `≤ n`, and `m = n+1` with `i ≠ j`), hence closed.
-/

open Set Topology

namespace Work.CWTOP

theorem isClosed_skel_diff_openCell {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (n : ℕ) (j : Topology.RelCWComplex.cell C (n + 1)) :
    IsClosed ((Work.CWTOP.skel C (n + 1) : Set X) \ Topology.RelCWComplex.openCell (n + 1) j) := by
  set A : Set X := (skel C (n + 1) : Set X) \ RelCWComplex.openCell (n + 1) j with hA
  have hAmem : ∀ {x : X}, x ∈ A ↔ x ∈ skel C (n + 1) ∧ x ∉ RelCWComplex.openCell (n + 1) j := by
    intro x
    rw [hA]
    exact Iff.rfl
  have hlt_succ : ((n : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) :=
    ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)
  apply CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell (C := C) (A := A)
  · -- the set lies in the complex
    intro x hx
    exact (RelCWComplex.Subcomplex.subset_complex
      (RelCWComplex.skeleton C ((n + 1 : ℕ) : ℕ∞))) (hAmem.mp hx).1
  · intro m _ i
    rcases lt_trichotomy m (n + 1) with hlt | heq | hgt
    · -- lower dimensions: `A` contains the closed cell `closedCell m i`
      right
      have hsub : RelCWComplex.closedCell m i ⊆ A := by
        intro x hx
        refine hAmem.mpr ⟨?_, ?_⟩
        · exact RelCWComplex.skeleton_mono
            (ENat.natCast_le_natCast.mpr ((Nat.le_of_lt_succ hlt).trans (Nat.le_succ n)))
            (RelCWComplex.closedCell_subset_skeleton m i hx)
        · intro hxo
          exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeleton_openCell (C := C)
            (n := ((n : ℕ) : ℕ∞)) (m := n + 1) (j := j) hlt_succ)
            (RelCWComplex.skeleton_mono (ENat.natCast_le_natCast.mpr (Nat.le_of_lt_succ hlt))
              (RelCWComplex.closedCell_subset_skeleton m i hx)) hxo
      rw [Set.inter_eq_right.mpr hsub]
      exact RelCWComplex.isClosed_closedCell
    · -- the removed cell itself: `A` misses its open cell
      subst heq
      by_cases hij : i = j
      · rw [hij]
        left
        have hempty : A ∩ RelCWComplex.openCell (n + 1) j = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro x ⟨hx, hxo⟩
          exact (hAmem.mp hx).2 hxo
        rw [hempty]
        exact isClosed_empty
      · -- another `(n+1)`-cell: `A` contains its closed cell
        right
        have hsub : RelCWComplex.closedCell (n + 1) i ⊆ A := by
          intro x hx
          rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell (n + 1) i] at hx
          refine hAmem.mpr ⟨?_, ?_⟩
          · rcases hx with hx | hx
            · exact RelCWComplex.skeleton_mono (le_of_lt hlt_succ)
                (RelCWComplex.cellFrontier_subset_skeleton n i hx)
            · exact RelCWComplex.openCell_subset_skeleton (n + 1) i hx
          · intro hxo
            rcases hx with hx | hx
            · exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeleton_openCell (C := C)
                (n := ((n : ℕ) : ℕ∞)) (m := n + 1) (j := j) hlt_succ)
                (RelCWComplex.cellFrontier_subset_skeleton n i hx) hxo
            · exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne (C := C)
                (by intro h; exact hij (eq_of_heq (Sigma.mk.inj h).2))) hx hxo
        rw [Set.inter_eq_right.mpr hsub]
        exact RelCWComplex.isClosed_closedCell
    · -- higher dimensions: `A` misses the open cell
      left
      have hempty : A ∩ RelCWComplex.openCell m i = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hx, hxo⟩
        exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeleton_openCell (C := C)
          (n := ((n + 1 : ℕ) : ℕ∞)) (m := m) (j := i)
          (ENat.natCast_lt_natCast.mpr hgt)) (hAmem.mp hx).1 hxo
      rw [hempty]
      exact isClosed_empty

end Work.CWTOP
