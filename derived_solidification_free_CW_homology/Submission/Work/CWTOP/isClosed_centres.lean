import Mathlib
import Submission.Work.CWTOP.Basic

/-!
# The set of cell centres of a fixed dimension is closed

For a CW complex `C` in a Hausdorff space `X`, the set `centres C n` of the images of `0` under the
characteristic maps of the `n`-cells is closed in `X`.

The point is that the cells themselves are *not* an open cover of `X`, so a centre of an `n`-cell can
well lie on the boundary of a higher dimensional cell; however, on each closed `(n+1)`-cell only
finitely many `n`-cells can meet the boundary (closure finiteness), and consequently the centres
behave like isolated points along the cells.  Formally we apply the weak topology criterion
`CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`: for a closed cell of
dimension `m ≠ n` the set of centres is disjoint from the corresponding open cell, while in
dimension `n` it meets the closed cell of `i` in exactly the single point `cellCentre C n i`.
-/

open Set Topology

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C]

/-- A closed `n`-cell contains exactly one centre of an `n`-cell, namely its own. -/
lemma centres_inter_closedCell_eq (n : ℕ) (i : RelCWComplex.cell C n) :
    centres C n ∩ RelCWComplex.closedCell n i = {cellCentre C n i} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxi⟩
    rw [mem_centres] at hx
    obtain ⟨j, hj⟩ := hx
    subst hj
    rw [Set.mem_singleton_iff]
    rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at hxi
    rcases hxi with hf | ho
    · -- the centre of an `n`-cell does not lie in the `n`-skeleton of lower cells
      exact absurd (RelCWComplex.cellFrontier_subset_skeletonLT n i hf)
        (cellCentre_notMem_skeletonLT n j le_rfl)
    · -- two `n`-cells whose open cells are not disjoint coincide
      have h1 : cellCentre C n j ∈ RelCWComplex.openCell n j := cellCentre_mem_openCell n j
      have hsig : (⟨n, j⟩ : Σ l, RelCWComplex.cell C l) = ⟨n, i⟩ :=
        RelCWComplex.eq_of_not_disjoint_openCell (not_disjoint_iff.mpr ⟨_, h1, ho⟩)
      have : j = i := eq_of_heq (Sigma.mk.inj hsig).2
      rw [this]
  · rintro x rfl
    exact ⟨mem_centres.mpr ⟨i, rfl⟩, RelCWComplex.map_zero_mem_closedCell n i⟩

theorem isClosed_centres {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (n : ℕ) : IsClosed (Work.CWTOP.centres C n) := by
  apply CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell (C := C)
    (A := centres C n)
  · -- all centres lie in the complex
    intro x hx
    rw [mem_centres] at hx
    obtain ⟨j, hj⟩ := hx
    subst hj
    exact RelCWComplex.openCell_subset_complex n j (cellCentre_mem_openCell n j)
  · intro m _ i
    rcases eq_or_ne m n with rfl | hmn
    · -- in dimension `n` the centres meet the closed cell in a single point
      right
      rw [centres_inter_closedCell_eq]
      exact isClosed_singleton
    · -- in any other dimension the centres avoid the open cell
      left
      rw [Set.disjoint_left]
      intro x hx hxo
      rw [mem_centres] at hx
      obtain ⟨j, hj⟩ := hx
      subst hj
      exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne (n := n) (m := m)
        (i := j) (j := i) (by intro h; exact hmn (Sigma.mk.inj h).1.symm))
        (cellCentre_mem_openCell n j) hxo

end Work.CWTOP
