import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.BlockDefs
import Submission.Work.HornSC.CellBoundaryJordan.rect_subset_cellUnion
import Submission.Work.HornSC.CellBoundaryJordan.exists_ball_subset_of_rect
import Submission.Work.HornSC.CellBoundaryJordan.block_of_vertical_edge
import Submission.Work.HornSC.CellBoundaryJordan.block_of_horizontal_edge
import Submission.Work.HornSC.CellBoundaryJordan.block_of_corner

/-!
# `cellUnion A` is a neighbourhood of every non-wall point

Given a finite family `A` of lattice cells, every point of `cellUnion A` which does not lie on a
wall of `A` has a whole ball around it inside `cellUnion A`.

The local picture: if `z ∈ cellUnion A` and `z ∉ wallSet A`, then near `z` the cells of `A` fill a
whole lattice rectangle around `z`.  Which rectangle is dictated by the position of `z` in the unit
grid, with four cases (strict interior, vertical grid line, horizontal grid line, lattice point).
The three non-interior cases use that the grid segments through `z` are not walls of `A`, hence the
cells across them have the same membership status in `A`; the one cell of `A` covering `z` then
propagates to the whole block.

The four `block_of_*` lemmas are proved in the sibling files; `block_of_interior` (the easy case) is
recorded here.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- If `z` lies strictly inside the unit cell containing it, then the only cell of the block
`[⌊z.re⌋, ⌊z.re⌋+1) × [⌊z.im⌋, ⌊z.im⌋+1)` is the floor cell of `z`, which contains `z`. -/
lemma block_of_interior {A : Finset (ℤ × ℤ)} {z : ℂ} {p : ℤ × ℤ}
    (hp : p ∈ A) (hzp : z ∈ cell p)
    (hx : (⌊z.re⌋ : ℝ) < z.re) (hy : (⌊z.im⌋ : ℝ) < z.im) :
    RectBlock A ⌊z.re⌋ (⌊z.re⌋ + 1) ⌊z.im⌋ (⌊z.im⌋ + 1) := by
  have e1 := mem_cell_fst_eq_floor hzp hx
  have e2 := mem_cell_snd_eq_floor hzp hy
  intro p' q hp1 hp2 hq1 hq2
  have hp' : p' = p.1 := by omega
  have hq' : q = p.2 := by omega
  rw [hp', hq']
  exact hp

lemma ball_subset_cellUnion_of_notMem_wallSet {A : Finset (ℤ × ℤ)} {z : ℂ}
    (hz : z ∈ cellUnion A) (hw : z ∉ wallSet A) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w - z‖ < r → w ∈ cellUnion A := by
  obtain ⟨p, hp, hzp⟩ := exists_cell_mem_of_mem_cellUnion hz
  -- locate the block of cells of `A` filling a neighbourhood of `z`
  have key : ∃ a c b d : ℤ, a < c ∧ b < d ∧ (a : ℝ) < z.re ∧ z.re < (c : ℝ) ∧
      (b : ℝ) < z.im ∧ z.im < (d : ℝ) ∧ RectBlock A a c b d := by
    obtain hx | hx := lt_or_eq_of_le (Int.floor_le z.re)
    · -- `⌊z.re⌋ < z.re`, so `z` is strictly inside its column
      obtain hy | hy := lt_or_eq_of_le (Int.floor_le z.im)
      · -- strictly inside its cell: the single cell is the floor cell
        exact ⟨⌊z.re⌋, ⌊z.re⌋ + 1, ⌊z.im⌋, ⌊z.im⌋ + 1, by omega, by omega, hx,
          by push_cast; linarith [Int.lt_floor_add_one z.re], hy,
          by push_cast; linarith [Int.lt_floor_add_one z.im],
          block_of_interior hp hzp hx hy⟩
      · -- on the horizontal grid line through `z`
        exact ⟨⌊z.re⌋, ⌊z.re⌋ + 1, ⌊z.im⌋ - 1, ⌊z.im⌋ + 1, by omega, by omega, hx,
          by push_cast; linarith [Int.lt_floor_add_one z.re],
          by push_cast; linarith [hy], by push_cast; linarith [hy],
          block_of_horizontal_edge hp hzp hx hy.symm hw⟩
    · -- `z.re` is an integer: `z` lies on a vertical grid line
      obtain hy | hy := lt_or_eq_of_le (Int.floor_le z.im)
      · -- and strictly inside its row
        exact ⟨⌊z.re⌋ - 1, ⌊z.re⌋ + 1, ⌊z.im⌋, ⌊z.im⌋ + 1, by omega, by omega,
          by push_cast; linarith [hx], by push_cast; linarith [hx], hy,
          by push_cast; linarith [Int.lt_floor_add_one z.im],
          block_of_vertical_edge hp hzp hx.symm hy hw⟩
      · -- at a lattice point
        exact ⟨⌊z.re⌋ - 1, ⌊z.re⌋ + 1, ⌊z.im⌋ - 1, ⌊z.im⌋ + 1, by omega, by omega,
          by push_cast; linarith [hx], by push_cast; linarith [hx],
          by push_cast; linarith [hy], by push_cast; linarith [hy],
          block_of_corner hp hzp hx.symm hy.symm hw⟩
  obtain ⟨a, c, b, d, hac, hbd, h3, h4, h5, h6, hblk⟩ := key
  -- the block is a rectangle contained in `cellUnion A`; a rectangle grows a ball at `z`
  exact exists_ball_subset_of_rect h3 h4 h5 h6
    (fun w h1 h2 h3' h4' => rect_subset_cellUnion hac hbd hblk ⟨h1, h2, h3', h4'⟩)

end Work.HornSC.CellBoundaryJordan
