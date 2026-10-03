import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.BlockDefs

namespace Work.HornSC.CellBoundaryJordan

/-- If `z` lies on a horizontal grid line, strictly inside its unit column, and is not on the wall
set of `A`, then both cells of the lattice rectangle `[⌊z.re⌋,⌊z.re⌋+1) × [⌊z.im⌋-1,⌊z.im⌋+1)`
(i.e. the two cells above and below the grid line in `z`'s column) belong to `A`. -/
lemma block_of_horizontal_edge {A : Finset (ℤ × ℤ)} {z : ℂ} {p : ℤ × ℤ}
    (hp : p ∈ A) (hzp : z ∈ cell p)
    (hx : (⌊z.re⌋ : ℝ) < z.re) (hy : z.im = (⌊z.im⌋ : ℝ))
    (hw : z ∉ wallSet A) :
    RectBlock A ⌊z.re⌋ (⌊z.re⌋ + 1) (⌊z.im⌋ - 1) (⌊z.im⌋ + 1) := by
  -- `z` lies on the horizontal grid segment at `(⌊z.re⌋, ⌊z.im⌋)`, so that segment is not a wall.
  have hnot : ¬ hWallAt A (⌊z.re⌋, ⌊z.im⌋) :=
    not_hWallAt_of_mem_hSeg hw (mem_hSeg_floor hy)
  -- `z` is strictly inside its column, so `p` has first index `⌊z.re⌋`.
  have hp1 : p.1 = ⌊z.re⌋ := mem_cell_fst_eq_floor hzp hx
  -- `p.2` is either `⌊z.im⌋` (the upper cell) or `⌊z.im⌋ - 1` (the lower cell).
  have hupper : (⌊z.re⌋, ⌊z.im⌋) ∈ A := by
    rcases mem_cell_snd_cases hzp with h | h
    · have hpeq : p = (⌊z.re⌋, ⌊z.im⌋) := Prod.ext hp1 h
      rwa [hpeq] at hp
    · have hpeq : p = (⌊z.re⌋, ⌊z.im⌋ - 1) := Prod.ext hp1 h
      have hlow : (⌊z.re⌋, ⌊z.im⌋ - 1) ∈ A := by rwa [hpeq] at hp
      exact mem_north_of_not_hWallAt hnot hlow
  have hlower : (⌊z.re⌋, ⌊z.im⌋ - 1) ∈ A := mem_south_of_not_hWallAt hnot hupper
  intro p' q' hp'1 hp'2 hq'1 hq'2
  have hp' : p' = ⌊z.re⌋ := by omega
  have hq' : q' = ⌊z.im⌋ ∨ q' = ⌊z.im⌋ - 1 := by omega
  rcases hq' with h | h
  · rw [h, hp']; exact hupper
  · rw [h, hp']; exact hlower

end Work.HornSC.CellBoundaryJordan
