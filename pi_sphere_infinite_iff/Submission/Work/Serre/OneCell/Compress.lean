import Mathlib
import Submission.Work.Serre.OneCell.Defs
import Submission.Work.Serre.OneCell.OneCellGeom
import Submission.Work.Serre.E2dEngine

/-!
# The compressibility of the open cells, and of the union of the open cells

The local model of the `1`-cell step needs two compression facts:

* `compressRel_cellInteriorOne` — the open cell compresses onto its centre (it is an interval);
* `compressRel_cellInnerUnionOne` — the union of the open cells compresses onto the set of the
centres (each cell is contracted to its own centre).

Both are obtained from explicit contractions, built from the cell chart `cellChart` (a chosen
continuous inverse of the characteristic map on the open cell).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphereZero, Y)}

/-! ## The cell chart -/

/-- The chart of the `i`-th cell: a continuous inverse of the characteristic map on the open cell,
chosen once and for all. -/
noncomputable def cellChart (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) :
    C(↥(cellInteriorOne Y ι f i), ↥cellInnerOne) :=
  Classical.choose (exists_chart f i)

theorem cellChart_apply (i : ι) (x : ↥(cellInteriorOne Y ι f i)) :
    oneCellMap Y ι f i (cellChart Y ι f i x) = (x : attachOneCells Y ι f) :=
  (Classical.choose_spec (exists_chart f i)).1 x

theorem cellChart_symm (i : ι) (x : ↥cellInnerOne) :
    cellChart Y ι f i ⟨oneCellMap Y ι f i x, ⟨x, x.2, rfl⟩⟩ = x :=
  (Classical.choose_spec (exists_chart f i)).2 x

/-! ## The contraction of the model interval

The open model interval `(-1,1)` is convex, so the straight line to the centre `0` contracts it
onto `0`, fixing `0`. -/

theorem norm_smul_le_one {a : cellDiskOne} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖t • (a : ℝ)‖ ≤ 1 := by
  have han : ‖(a : ℝ)‖ ≤ 1 := by simpa [dist_eq_norm, sub_zero] using Metric.mem_closedBall.mp a.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg ((a : cellDiskOne) : ℝ)]

theorem norm_smul_lt_one {a : cellDiskOne} (ha : a ∈ cellInnerOne) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖t • (a : ℝ)‖ < 1 := by
  have han : ‖(a : ℝ)‖ < 1 := ha
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg ((a : cellDiskOne) : ℝ)]

/-- The straight-line contraction of the open model interval to its centre. -/
noncomputable def cellInnerContract : C(↥cellInnerOne × I, ↥cellInnerOne) where
  toFun p :=
    ⟨⟨(1 - (p.2 : ℝ)) • (((p.1 : ↥cellInnerOne) : cellDiskOne) : ℝ),
        Metric.mem_closedBall.mpr (by
          simpa [dist_eq_norm, sub_zero] using
            norm_smul_le_one (a := ((p.1 : ↥cellInnerOne) : cellDiskOne))
              (t := 1 - (p.2 : ℝ)) (by linarith [(p.2 : I).2.2])
              (by linarith [(p.2 : I).2.1]))⟩,
      norm_smul_lt_one (p.1.2) (t := 1 - (p.2 : ℝ)) (by linarith [(p.2 : I).2.2])
        (by linarith [(p.2 : I).2.1])⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)))

@[simp] theorem cellInnerContract_zero (x : ↥cellInnerOne) : cellInnerContract (x, 0) = x := by
  refine Subtype.ext (Subtype.ext ?_)
  show (1 - ((0 : I) : ℝ)) • ((x : cellDiskOne) : ℝ) = ((x : cellDiskOne) : ℝ)
  simp

@[simp] theorem cellInnerContract_one (x : ↥cellInnerOne) :
    cellInnerContract (x, 1) = ⟨cellDiskOneCentreOne,
      (by simp [cellDiskOneCentreOne, cellInnerOne] : cellDiskOneCentreOne ∈ cellInnerOne)⟩ := by
  refine Subtype.ext (Subtype.ext ?_)
  show (1 - ((1 : I) : ℝ)) • ((x : cellDiskOne) : ℝ) = ((cellDiskOneCentreOne : cellDiskOne) : ℝ)
  simp [cellDiskOneCentreOne]

theorem cellInnerContract_self (t : I) :
    cellInnerContract (⟨cellDiskOneCentreOne,
        (by simp [cellDiskOneCentreOne, cellInnerOne] : cellDiskOneCentreOne ∈ cellInnerOne)⟩,
        t) =
      ⟨cellDiskOneCentreOne,
        (by simp [cellDiskOneCentreOne, cellInnerOne] : cellDiskOneCentreOne ∈ cellInnerOne)⟩ := by
  refine Subtype.ext (Subtype.ext ?_)
  show (1 - (t : ℝ)) • ((cellDiskOneCentreOne : cellDiskOne) : ℝ) = 0
  simp [cellDiskOneCentreOne]

end

end Work.Serre.OneCell

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphereZero, Y)}

/-! ## The contraction of a single open cell -/

/-- The straight-line contraction of the `i`-th open cell onto its centre. -/
noncomputable def cellContract (i : ι) :
    C(↥(cellInteriorOne Y ι f i) × I, ↥(cellInteriorOne Y ι f i)) where
  toFun p :=
    ⟨oneCellMap Y ι f i (cellInnerContract (cellChart Y ι f i p.1, p.2)),
      ⟨cellInnerContract (cellChart Y ι f i p.1, p.2),
        (cellInnerContract (cellChart Y ι f i p.1, p.2)).2, rfl⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (oneCellMap Y ι f i).continuous.comp (continuous_subtype_val.comp
      (cellInnerContract.continuous.comp
        ((cellChart Y ι f i).continuous.comp continuous_fst |>.prodMk continuous_snd)))

@[simp] theorem cellContract_zero (i : ι) (x : ↥(cellInteriorOne Y ι f i)) :
    cellContract i (x, 0) = x := by
  refine Subtype.ext ?_
  show oneCellMap Y ι f i (cellInnerContract (cellChart Y ι f i x, 0)) = (x : attachOneCells Y ι f)
  rw [cellInnerContract_zero, cellChart_apply]

theorem cellContract_one_mem (i : ι) (x : ↥(cellInteriorOne Y ι f i)) :
    (cellContract i (x, 1) : attachOneCells Y ι f) = oneCellCentreOne Y ι f i := by
  show oneCellMap Y ι f i (cellInnerContract (cellChart Y ι f i x, 1)) = oneCellCentreOne Y ι f i
  rw [cellInnerContract_one]
  rfl

theorem cellContract_centre (i : ι) (y : ↥(cellInteriorOne Y ι f i))
    (hy : (y : attachOneCells Y ι f) = oneCellCentreOne Y ι f i) (t : I) :
    cellContract i (y, t) = y := by
  have hc : cellChart Y ι f i y = ⟨cellDiskOneCentreOne,
      (by simp [cellDiskOneCentreOne, cellInnerOne] : cellDiskOneCentreOne ∈ cellInnerOne)⟩ := by
    refine Subtype.ext ?_
    refine oneCellMap_injOn_inner f i (cellChart Y ι f i y).2
      (by simp [cellDiskOneCentreOne, cellInnerOne]) ?_
    rw [cellChart_apply, hy]
    rfl
  refine Subtype.ext ?_
  show oneCellMap Y ι f i (cellInnerContract (cellChart Y ι f i y, t)) = (y : attachOneCells Y ι f)
  rw [hc, cellInnerContract_self]
  exact hy.symm

/-- **The open cell compresses onto its centre.** -/
theorem compressRel_cellInteriorOne (i : ι) (d : ℕ) :
    Work.RatHurewicz.CompressRel ↥(cellInteriorOne Y ι f i)
      {x : ↥(cellInteriorOne Y ι f i) |
        (x : attachOneCells Y ι f) = oneCellCentreOne Y ι f i} d :=
  Work.Serre.compressRel_of_deformation (cellContract (Y := Y) (f := f) i)
    (fun x => cellContract_zero i x)
    (fun x => cellContract_one_mem i x)
    (fun y hy t => cellContract_centre i y hy t) d

end

end Work.Serre.OneCell

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphereZero, Y)}

/-! ## The contraction of the union of the open cells -/

/-- The cell containing a point of the union of the open cells. -/
noncomputable def cellOf (x : ↥(cellInnerUnionOne Y ι f)) : ι :=
  Classical.choose (Set.mem_iUnion.mp x.2)

theorem cellOf_spec (x : ↥(cellInnerUnionOne Y ι f)) :
    (x : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f (cellOf (Y := Y) (ι := ι) (f := f) x) :=
  Classical.choose_spec (Set.mem_iUnion.mp x.2)

theorem cellOf_eq (i : ι) (x : ↥(cellInnerUnionOne Y ι f))
    (hx : (x : attachOneCells Y ι f) ∈ cellInteriorOne Y ι f i) : cellOf (Y := Y) (ι := ι) (f := f) x = i := by
  by_contra hne
  have hd := Set.disjoint_left.mp
    (disjoint_cellInteriorOne (Y := Y) (f := f) (i := cellOf (Y := Y) (ι := ι) (f := f) x) (j := i) hne)
  exact hd (cellOf_spec (Y := Y) (ι := ι) (f := f) x) hx

end

end Work.Serre.OneCell
