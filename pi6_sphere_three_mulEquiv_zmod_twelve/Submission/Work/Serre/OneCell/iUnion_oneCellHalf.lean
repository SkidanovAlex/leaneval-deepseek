import Mathlib
import Submission.Work.Serre.OneCell.Halves
import Submission.Work.Serre.OneCell.OneCellGeom

/-!
# The union of the two halves of the open `1`-cells

`cellInnerOne = (-1,1)` is the disjoint union of its two halves `cellHalf true = (0,1)` and
`cellHalf false = (-1,0)`, and correspondingly the union of the images `oneCellHalf i ε` of the
halves of all the cells is `cellInnerUnionOne \ oneCellCentresOne`: the union of the open cells
with the cell centres removed.

The proof is set-theoretic: a point of a half-cell `χᵢ '' cellHalf ε` lies in the open cell
`cellInteriorOne i` and is not a centre (the characteristic map is injective on `cellInnerOne` and
`cellHalf ε` avoids `0`; different cells are disjoint), and conversely a point `χᵢ x` of an open
cell which is not a centre has `x ≠ 0`, hence `x > 0` or `x < 0`, so it lies in one of the two
halves.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- No point of a half of the open model interval is the centre. -/
private theorem cellHalf_ne_centreOne {ε : Bool} {x : cellDiskOne} (hx : x ∈ cellHalf ε) :
    x ≠ cellDiskOneCentreOne := by
  intro h
  have h0 : (x : ℝ) = 0 := by rw [h]; rfl
  have hx' : (if ε then (0 : ℝ) < (x : ℝ) else (x : ℝ) < 0) := hx.2
  cases ε <;> simp_all

/-- Every interior point of the model interval other than the centre lies in one of the two
halves. -/
private theorem exists_cellHalf_of_mem_cellInnerOne {x : cellDiskOne}
    (hx : x ∈ cellInnerOne) (hne : x ≠ cellDiskOneCentreOne) : ∃ ε : Bool, x ∈ cellHalf ε := by
  have hx0 : (x : ℝ) ≠ 0 := by
    intro h0
    exact hne (Subtype.ext (by rw [h0]; rfl))
  rcases lt_or_gt_of_ne hx0 with h | h
  · exact ⟨false, hx, by simpa using h⟩
  · exact ⟨true, hx, by simpa using h⟩

theorem iUnion_oneCellHalf (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) :
    (⋃ p : ι × Bool, Work.Serre.OneCell.oneCellHalfPiece Y ι f p) =
      Work.Serre.OneCell.cellInnerUnionOne Y ι f \ Work.Serre.OneCell.oneCellCentresOne Y ι f := by
  ext z
  constructor
  · -- a point of a half-cell is an interior point of the cell and is not a centre
    intro hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨⟨i, ε⟩, hz⟩ := hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨Set.mem_iUnion.mpr ⟨i, x, cellHalf_subset_cellInnerOne ε hx, rfl⟩, ?_⟩
    rintro ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      have hj' : oneCellMap Y ι f i cellDiskOneCentreOne = oneCellMap Y ι f i x := by
        rw [← hj]; rfl
      have hcx : cellDiskOneCentreOne = x :=
        oneCellMap_injOn_inner f i (by simp [cellDiskOneCentreOne, cellInnerOne])
          (cellHalf_subset_cellInnerOne ε hx) hj'
      exact cellHalf_ne_centreOne hx hcx.symm
    · have h1 : oneCellMap Y ι f i x ∈ cellInteriorOne Y ι f i :=
        ⟨x, cellHalf_subset_cellInnerOne ε hx, rfl⟩
      have h2 : oneCellMap Y ι f i x ∈ cellInteriorOne Y ι f j := by
        rw [← hj]; exact oneCellCentreOne_mem_cellInteriorOne f j
      exact (Set.disjoint_left.mp (disjoint_cellInteriorOne f hij)) h1 h2
  · -- an interior point of a cell which is not a centre is not the centre of its cell, so it
    -- lies in one of the two halves
    rintro ⟨hz, hzne⟩
    rw [mem_cellUnionOne] at hz
    obtain ⟨i, x, hx, rfl⟩ := hz
    have hxc : x ≠ cellDiskOneCentreOne := by
      intro h
      exact hzne ⟨i, by
        show oneCellMap Y ι f i cellDiskOneCentreOne = oneCellMap Y ι f i x
        rw [h]⟩
    obtain ⟨ε, hε⟩ := exists_cellHalf_of_mem_cellInnerOne hx hxc
    exact Set.mem_iUnion.mpr ⟨(i, ε), ⟨x, hε, rfl⟩⟩

end

end Work.Serre.OneCell
