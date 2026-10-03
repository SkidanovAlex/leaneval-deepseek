import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.BlockDefs

namespace Work.HornSC.CellBoundaryJordan

/-- If `z` lies on a vertical grid line, strictly inside its row, and is not on a wall of `A`,
and `z` is covered by a cell of `A`, then the whole `2 × 1` block of cells to the left and right
of the vertical line (at the row of `z`) belongs to `A`.

Indeed `z ∈ vSeg (⌊z.re⌋, ⌊z.im⌋)`, so if this segment were a wall of `A` it would lie in
`wallSet A`; hence the two cells adjacent to it have the same membership status in `A`, and one of
them contains `z` and hence lies in `A`. -/
lemma block_of_vertical_edge {A : Finset (ℤ × ℤ)} {z : ℂ} {p : ℤ × ℤ}
    (hp : p ∈ A) (hzp : z ∈ cell p)
    (hx : z.re = (⌊z.re⌋ : ℝ)) (hy : (⌊z.im⌋ : ℝ) < z.im)
    (hw : z ∉ wallSet A) :
    RectBlock A (⌊z.re⌋ - 1) (⌊z.re⌋ + 1) ⌊z.im⌋ (⌊z.im⌋ + 1) := by
  intro p' q' hp'lo hp'hi hq'lo hq'hi
  -- `z` sits in the row `⌊z.im⌋` (strictly above the floor), so `q' = ⌊z.im⌋`.
  have hq : q' = ⌊z.im⌋ := by omega
  subst hq
  -- `z` lies on the vertical grid segment through the floors of its coordinates,
  -- which is therefore not a wall of `A`.
  have hseg : z ∈ vSeg (⌊z.re⌋, ⌊z.im⌋) := mem_vSeg_floor hx
  have hnot : ¬ vWallAt A (⌊z.re⌋, ⌊z.im⌋) := not_vWallAt_of_mem_vSeg hw hseg
  -- The second index of `p` is `⌊z.im⌋`.
  have hp2 : p.2 = ⌊z.im⌋ := mem_cell_snd_eq_floor hzp hy
  -- The two cells adjacent to the segment are `(⌊z.re⌋, ⌊z.im⌋)` and `(⌊z.re⌋ - 1, ⌊z.im⌋)`;
  -- `z` is covered by one of them, and `¬ vWallAt` forces the other one in as well.
  have hA1 : (⌊z.re⌋, ⌊z.im⌋) ∈ A := by
    rcases mem_cell_fst_cases hzp with h1 | h1
    · have hpe : p = (⌊z.re⌋, ⌊z.im⌋) := Prod.ext h1 hp2
      rwa [hpe] at hp
    · have hbase : (⌊z.re⌋ - 1, ⌊z.im⌋) ∈ A := by
        have hpe : p = (⌊z.re⌋ - 1, ⌊z.im⌋) := Prod.ext h1 hp2
        rwa [hpe] at hp
      by_contra hc
      exact hnot (Or.inr ⟨hc, hbase⟩)
  have hA0 : (⌊z.re⌋ - 1, ⌊z.im⌋) ∈ A := by
    by_contra hc
    exact hnot (Or.inl ⟨hA1, hc⟩)
  -- Finally `p'` is one of the two first indices of the block.
  rcases (show p' = ⌊z.re⌋ ∨ p' = ⌊z.re⌋ - 1 by omega) with h | h
  · rw [h]; exact hA1
  · rw [h]; exact hA0

end Work.HornSC.CellBoundaryJordan
