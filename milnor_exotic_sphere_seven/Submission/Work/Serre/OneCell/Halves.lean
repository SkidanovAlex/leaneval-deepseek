import Mathlib
import Submission.Work.Serre.OneCell.Defs
import Submission.Work.Serre.OneCell.OneCellGeom
import Submission.Work.Serre.OneCell.Prelim

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two halves of an open `1`-cell

`cellInnerOne = (-1,1)` is the disjoint union of its positive and negative halves, and the union of
the open cells `cellInnerUnionOne` is the disjoint union of the images `oneCellHalf i ε` of these
halves.  This file fixes the vocabulary and the elementary openness/disjointness facts; the
identification of the union with `cellInnerUnionOne \ oneCellCentresOne` and the contraction of
each half onto the point `±1/2` are the inputs of the per-cell vanishing lemmas of the local model.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- The **positive (`ε = true`) or negative (`ε = false`) half** of the open model interval. -/
def cellHalf (ε : Bool) : Set cellDiskOne :=
  {x | x ∈ cellInnerOne ∧ (if ε then (0 : ℝ) < (x : ℝ) else (x : ℝ) < 0)}

@[simp] theorem mem_cellHalf {ε : Bool} {x : cellDiskOne} :
    x ∈ cellHalf ε ↔ x ∈ cellInnerOne ∧
      (if ε then (0 : ℝ) < (x : ℝ) else (x : ℝ) < 0) := Iff.rfl

theorem cellHalf_subset_cellInnerOne (ε : Bool) : cellHalf ε ⊆ cellInnerOne :=
  fun _ hx => hx.1

theorem isOpen_cellInnerOne : IsOpen cellInnerOne :=
  isOpen_lt continuous_subtype_val.norm continuous_const

theorem isOpen_cellHalf (ε : Bool) : IsOpen (cellHalf ε) := by
  have h1 : IsOpen {x : cellDiskOne | (0 : ℝ) < (x : ℝ)} :=
    isOpen_lt continuous_const continuous_subtype_val
  have h2 : IsOpen {x : cellDiskOne | (x : ℝ) < 0} :=
    isOpen_lt continuous_subtype_val continuous_const
  cases ε with
  | false =>
    have h : cellHalf false = cellInnerOne ∩ {x : cellDiskOne | (x : ℝ) < 0} := by
      ext x; simp [cellHalf]
    rw [h]; exact isOpen_cellInnerOne.inter h2
  | true =>
    have h : cellHalf true = cellInnerOne ∩ {x : cellDiskOne | (0 : ℝ) < (x : ℝ)} := by
      ext x; simp [cellHalf]
    rw [h]; exact isOpen_cellInnerOne.inter h1

/-- The image of a half of the open model interval under the characteristic map of a cell. -/
def oneCellHalf (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y))
    (i : ι) (ε : Bool) : Set (attachOneCells Y ι f) :=
  oneCellMap Y ι f i '' cellHalf ε

/-- The halves of all the open cells, indexed by `ι × Bool`. -/
def oneCellHalfPiece (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y))
    (p : ι × Bool) : Set (attachOneCells Y ι f) := oneCellHalf Y ι f p.1 p.2

@[simp] theorem mem_oneCellHalf {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellSphereZero, Y)} {i : ι} {ε : Bool} {z : attachOneCells Y ι f} :
    z ∈ oneCellHalf Y ι f i ε ↔ ∃ x : cellDiskOne, x ∈ cellHalf ε ∧ oneCellMap Y ι f i x = z :=
  Iff.rfl

theorem isOpen_oneCellHalf (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) (ε : Bool) :
    IsOpen (oneCellHalf Y ι f i ε) :=
  isOpen_cellImage f i (cellHalf_subset_cellInnerOne ε) (isOpen_cellHalf ε)

/-- A half of a cell is contained in the open cell. -/
theorem oneCellHalf_subset_cellInteriorOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) (ε : Bool) :
    oneCellHalf Y ι f i ε ⊆ cellInteriorOne Y ι f i := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, cellHalf_subset_cellInnerOne ε hx, rfl⟩

/-- The open model interval is a disjoint union of its two halves, and the open cells are pairwise
disjoint, so the halves of all the cells are pairwise disjoint. -/
theorem pairwiseDisjoint_oneCellHalf (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) :
    Pairwise fun p q : ι × Bool => Disjoint (oneCellHalfPiece Y ι f p)
      (oneCellHalfPiece Y ι f q) := by
  rintro ⟨i, ε⟩ ⟨j, δ⟩ hne
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rcases eq_or_ne i j with hij | hij
  · subst hij
    have hεδ : ε ≠ δ := by
      intro h; exact hne (by simp [h])
    have hxy' : x = y :=
      oneCellMap_injOn_inner f i (cellHalf_subset_cellInnerOne ε hx)
        (cellHalf_subset_cellInnerOne δ hy) hxy.symm
    subst hxy'
    have h1 := hx.2
    have h2 := hy.2
    cases ε <;> cases δ <;> simp_all <;> linarith
  · exact (Set.disjoint_left.mp (disjoint_cellInteriorOne f hij))
      (oneCellHalf_subset_cellInteriorOne Y ι f i ε ⟨x, hx, rfl⟩)
      (oneCellHalf_subset_cellInteriorOne Y ι f j δ ⟨y, hy, hxy⟩)

/-! ## The open cells as a cover -/

/-- The open cells are open. -/
theorem isOpen_cellInteriorOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) : IsOpen (cellInteriorOne Y ι f i) :=
  isOpen_cellImage f i (fun _ hx => hx) isOpen_cellInnerOne

/-- The union of the open cells is, definitionally, the union of the cell interiors. -/
theorem cellInnerUnionOne_eq_iUnion_cellInteriorOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) :
    cellInnerUnionOne Y ι f = ⋃ i, cellInteriorOne Y ι f i := rfl

/-! ## The point `±1/2` -/

/-- The point `1/2` (for `ε = true`) or `-1/2` (for `ε = false`) of the model interval, as a point
of the corresponding half. -/
def cellHalfPt (ε : Bool) : ↥(cellHalf ε) := by
  cases ε with
  | false =>
    exact ⟨⟨-(1 / 2), by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]; norm_num⟩,
      by
        refine ⟨?_, ?_⟩
        · show ‖((-(1 / 2) : ℝ))‖ < 1
          rw [Real.norm_eq_abs]; norm_num
        · show ((-(1 / 2) : ℝ)) < 0
          norm_num⟩
  | true =>
    exact ⟨⟨(1 / 2), by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]; norm_num⟩,
      by
        refine ⟨?_, ?_⟩
        · show ‖((1 / 2) : ℝ)‖ < 1
          rw [Real.norm_eq_abs]; norm_num
        · show ((0 : ℝ)) < (1 / 2)
          norm_num⟩

theorem cellHalfPt_coe (ε : Bool) : (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ) =
    if ε then (1 / 2 : ℝ) else -(1 / 2) := by cases ε <;> rfl

/-- The point `±1/2` of the `i`-th half-cell. -/
def oneCellHalfPt (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y))
    (i : ι) (ε : Bool) : ↥(oneCellHalf Y ι f i ε) :=
  ⟨oneCellMap Y ι f i (cellHalfPt ε), ⟨cellHalfPt ε, (cellHalfPt ε).2, rfl⟩⟩

@[simp] theorem oneCellHalfPt_coe (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) (ε : Bool) :
    ((oneCellHalfPt Y ι f i ε : ↥(oneCellHalf Y ι f i ε)) : attachOneCells Y ι f) =
      oneCellMap Y ι f i (cellHalfPt ε) := rfl

end

end Work.Serre.OneCell
