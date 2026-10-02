import Mathlib
import Submission.Work.Serre.OneCell.Halves

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Each half of an open `1`-cell is compressible to its midpoint

`oneCellHalf Y ι f i ε` is the image in `Z = attachOneCells Y ι f` of the positive (`ε = true`)
or negative (`ε = false`) half of the open model interval `(-1,1)`, under the characteristic map
of the `i`-th cell (`Work.Serre.OneCell.oneCellHalf`).

The half `cellHalf ε` is an interval, hence convex, and its midpoint `cellHalfPt ε = ±1/2` lies in
it.  The straight-line contraction of the half onto `±1/2` (fixing `±1/2`) descends along the
characteristic map (which is injective on the open interval) to a contraction of `oneCellHalf`
onto `oneCellHalfPt`, fixing that point.  The compression property of the pair in every dimension
is then the general fact `Work.Serre.compressRel_singleton_of_contraction`.

The bulk of the work is the model half: the midpoint `±1/2` is a convex combination
`(1-t) x + t·(±1/2)` of data already in the half, which is `(|x| ≤ 1, x > 0)` (resp. `x < 0`), and
the characteristic map is injective on the open interval, so the chart `exists_chart` of the open
cell restricts to a continuous inverse on the half.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphereZero, Y)}

/-! ## The straight-line contraction of the model half -/

/-- The affine combination `(1-t) x + t·(±1/2)` of a point of the half with the midpoint. -/
def halfComb (ε : Bool) (x : ↥(cellHalf ε)) (t : unitInterval) : ℝ :=
  (1 - (t : ℝ)) * ((x : cellDiskOne) : ℝ) +
    (t : ℝ) * (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ)

theorem halfComb_eq (ε : Bool) (x : ↥(cellHalf ε)) (t : unitInterval) :
    halfComb ε x t = (1 - (t : ℝ)) * ((x : cellDiskOne) : ℝ) +
      (t : ℝ) * (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ) := rfl

/-- The midpoint of the half is `±1/2`, and the sign is the sign of the half. -/
theorem halfComb_pt_val (ε : Bool) :
    (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ) = if ε = true then 1 / 2 else -(1 / 2) :=
  cellHalfPt_coe ε

/-- The affine combination bound on the real line. -/
theorem halfComb_abs_affine_le (a b : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |(1 - t) * a + t * b| ≤ (1 - t) * |a| + t * |b| := by
  calc |(1 - t) * a + t * b| ≤ |(1 - t) * a| + |t * b| := abs_add_le _ _
    _ = (1 - t) * |a| + t * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t),
          abs_of_nonneg ht0]

theorem halfComb_abs_lt_one (ε : Bool) (x : ↥(cellHalf ε)) (t : unitInterval) :
    |halfComb ε x t| < 1 := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hx : |((x : cellDiskOne) : ℝ)| < 1 := (mem_cellHalf.mp x.2).1
  have hp : |(((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ)| < 1 :=
    (mem_cellHalf.mp (cellHalfPt ε).2).1
  have htri : |halfComb ε x t| ≤ (1 - (t : ℝ)) * |((x : cellDiskOne) : ℝ)| +
      (t : ℝ) * |(((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ)| :=
    halfComb_abs_affine_le ((x : cellDiskOne) : ℝ)
      (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ) ht0 ht1
  have hle : (1 - (t : ℝ)) * |((x : cellDiskOne) : ℝ)| +
      (t : ℝ) * |(((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ)| < 1 := by
    by_cases ht : (t : ℝ) = 1
    · rw [ht]; simp only [sub_self, zero_mul, one_mul, zero_add]; exact hp
    · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 ht
      have h1 : 0 < 1 - (t : ℝ) := by linarith
      have ha : (1 - (t : ℝ)) * |((x : cellDiskOne) : ℝ)| < (1 - (t : ℝ)) * 1 :=
        mul_lt_mul_of_pos_left hx h1
      have hb : (t : ℝ) * |(((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ)| ≤ (t : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hp) ht0
      linarith
  linarith

/-- The affine combination of two points of the half lies in the half (the half is convex). -/
theorem halfComb_mem_closedBall (ε : Bool) (x : ↥(cellHalf ε)) (t : unitInterval) :
    halfComb ε x t ∈ Metric.closedBall (0 : ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact le_of_lt (halfComb_abs_lt_one ε x t)

theorem halfComb_sign_pos (x : ↥(cellHalf true)) (t : unitInterval) : 0 < halfComb true x t := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hx : 0 < ((x : cellDiskOne) : ℝ) := by
    simpa using (mem_cellHalf.mp x.2).2
  have hp : 0 < (((cellHalfPt true : ↥(cellHalf true)) : cellDiskOne) : ℝ) := by
    rw [halfComb_pt_val]; norm_num
  rw [halfComb]
  by_cases ht : (t : ℝ) = 1
  · rw [ht]; simp only [sub_self, zero_mul, zero_add, one_mul]; exact hp
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 ht
    have h1 : 0 < 1 - (t : ℝ) := by linarith
    have ha : 0 < (1 - (t : ℝ)) * ((x : cellDiskOne) : ℝ) := mul_pos h1 hx
    have hb : 0 ≤ (t : ℝ) * (((cellHalfPt true : ↥(cellHalf true)) : cellDiskOne) : ℝ) :=
      mul_nonneg ht0 (le_of_lt hp)
    linarith

theorem halfComb_sign_neg (x : ↥(cellHalf false)) (t : unitInterval) : halfComb false x t < 0 := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hx : ((x : cellDiskOne) : ℝ) < 0 := by
    simpa using (mem_cellHalf.mp x.2).2
  have hp : (((cellHalfPt false : ↥(cellHalf false)) : cellDiskOne) : ℝ) < 0 := by
    rw [halfComb_pt_val]; norm_num
  rw [halfComb]
  by_cases ht : (t : ℝ) = 0
  · rw [ht]; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact hx
  · have hgt : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hb : (t : ℝ) * (((cellHalfPt false : ↥(cellHalf false)) : cellDiskOne) : ℝ) < 0 :=
      mul_neg_of_pos_of_neg hgt hp
    have ha : (1 - (t : ℝ)) * ((x : cellDiskOne) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hx)
    linarith

theorem halfComb_mem_cellHalf (ε : Bool) (x : ↥(cellHalf ε)) (t : unitInterval) :
    (⟨halfComb ε x t, halfComb_mem_closedBall ε x t⟩ : cellDiskOne) ∈ cellHalf ε := by
  have hn : (⟨halfComb ε x t, halfComb_mem_closedBall ε x t⟩ : cellDiskOne) ∈ cellInnerOne := by
    show ‖((⟨halfComb ε x t, halfComb_mem_closedBall ε x t⟩ : cellDiskOne) : ℝ)‖ < 1
    rw [Real.norm_eq_abs]
    exact halfComb_abs_lt_one ε x t
  refine mem_cellHalf.mpr ⟨hn, ?_⟩
  cases ε with
  | false =>
    show ((⟨halfComb false x t, halfComb_mem_closedBall false x t⟩ : cellDiskOne) : ℝ) < 0
    exact halfComb_sign_neg x t
  | true =>
    show (0 : ℝ) < ((⟨halfComb true x t, halfComb_mem_closedBall true x t⟩ : cellDiskOne) : ℝ)
    exact halfComb_sign_pos x t

theorem halfComb_zero (ε : Bool) (x : ↥(cellHalf ε)) :
    halfComb ε x 0 = ((x : cellDiskOne) : ℝ) := by
  rw [halfComb]
  norm_num

theorem halfComb_one (ε : Bool) (x : ↥(cellHalf ε)) :
    halfComb ε x 1 = (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ) := by
  rw [halfComb]
  norm_num

theorem halfComb_pt (ε : Bool) (t : unitInterval) :
    halfComb ε (cellHalfPt ε) t = (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ) := by
  rw [halfComb]; ring

/-- **The straight-line contraction of the half onto its midpoint.** -/
noncomputable def cellHalfContract (ε : Bool) :
    C(↥(cellHalf ε) × unitInterval, ↥(cellHalf ε)) where
  toFun p :=
    ⟨⟨halfComb ε p.1 p.2, halfComb_mem_closedBall ε p.1 p.2⟩, halfComb_mem_cellHalf ε p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))).add
      ((continuous_subtype_val.comp continuous_snd).mul continuous_const))

theorem cellHalfContract_zero (ε : Bool) (x : ↥(cellHalf ε)) :
    cellHalfContract ε (x, 0) = x := by
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  show halfComb ε x 0 = ((x : cellDiskOne) : ℝ)
  rw [halfComb_zero]

theorem cellHalfContract_one (ε : Bool) (x : ↥(cellHalf ε)) :
    cellHalfContract ε (x, 1) = cellHalfPt ε := by
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  show halfComb ε x 1 = (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ)
  rw [halfComb_one]

theorem cellHalfContract_pt (ε : Bool) (t : unitInterval) :
    cellHalfContract ε (cellHalfPt ε, t) = cellHalfPt ε := by
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  show halfComb ε (cellHalfPt ε) t = (((cellHalfPt ε : ↥(cellHalf ε)) : cellDiskOne) : ℝ)
  rw [halfComb_pt]

/-! ## The chart of a half

The half is contained in the open cell, and the chart `exists_chart` of the open cell inverts the
characteristic map there; restricted to the half it lands in the half again, by the injectivity of
the characteristic map on the open model interval. -/

theorem halfIncl_subset_cellInteriorOne (i : ι) (ε : Bool) :
    oneCellHalf Y ι f i ε ⊆ cellInteriorOne Y ι f i := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, cellHalf_subset_cellInnerOne ε hx, rfl⟩

/-- The inclusion of a half-cell into the open cell it spans. -/
noncomputable def halfIncl (i : ι) (ε : Bool) :
    C(↥(oneCellHalf Y ι f i ε), ↥(cellInteriorOne Y ι f i)) where
  toFun x := ⟨(x : attachOneCells Y ι f), halfIncl_subset_cellInteriorOne i ε x.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp] theorem halfIncl_coe (i : ι) (ε : Bool) (x : ↥(oneCellHalf Y ι f i ε)) :
    (halfIncl i ε x : attachOneCells Y ι f) = (x : attachOneCells Y ι f) := rfl

/-- The chart of the `i`-th open cell: a chosen continuous inverse of the characteristic map. -/
noncomputable def halfModelChart (i : ι) :
    C(↥(cellInteriorOne Y ι f i), ↥cellInnerOne) :=
  Classical.choose (exists_chart f i)

theorem halfModelChart_apply (i : ι) (x : ↥(cellInteriorOne Y ι f i)) :
    oneCellMap Y ι f i (halfModelChart i x) = (x : attachOneCells Y ι f) :=
  (Classical.choose_spec (exists_chart f i)).1 x

/-- The chart of the `i`-th open cell, read on the half: it lands in the half again. -/
theorem halfModelChart_val_mem (i : ι) (ε : Bool) (x : ↥(oneCellHalf Y ι f i ε)) :
    ((halfModelChart i (halfIncl i ε x) : ↥cellInnerOne) : cellDiskOne) ∈ cellHalf ε := by
  obtain ⟨z, hz, hzx⟩ := x.2
  have h1 : oneCellMap Y ι f i ((halfModelChart i (halfIncl i ε x) : ↥cellInnerOne) : cellDiskOne) =
      oneCellMap Y ι f i z := by
    rw [halfModelChart_apply, halfIncl_coe]
    exact hzx.symm
  have h2 := oneCellMap_injOn_inner f i (halfModelChart i (halfIncl i ε x)).2
      (cellHalf_subset_cellInnerOne ε hz) h1
  rw [h2]
  exact hz

/-- The inverse of the characteristic map on the `i`-th half. -/
noncomputable def halfChart (i : ι) (ε : Bool) :
    C(↥(oneCellHalf Y ι f i ε), ↥(cellHalf ε)) where
  toFun x :=
    ⟨((halfModelChart i (halfIncl i ε x) : ↥cellInnerOne) : cellDiskOne),
      halfModelChart_val_mem i ε x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ (fun x => halfModelChart_val_mem i ε x)
    show Continuous fun x : ↥(oneCellHalf Y ι f i ε) =>
      ((halfModelChart i (halfIncl i ε x) : ↥cellInnerOne) : cellDiskOne)
    exact continuous_subtype_val.comp
      ((halfModelChart i).continuous.comp (halfIncl i ε).continuous)

theorem halfChart_apply (i : ι) (ε : Bool) (x : ↥(oneCellHalf Y ι f i ε)) :
    oneCellMap Y ι f i ↑(halfChart i ε x) = (x : attachOneCells Y ι f) :=
  halfModelChart_apply i (halfIncl i ε x)

theorem halfChart_pt (i : ι) (ε : Bool) :
    halfChart i ε (oneCellHalfPt Y ι f i ε) = cellHalfPt ε := by
  refine Subtype.ext ?_
  refine oneCellMap_injOn_inner f i ?_ ?_ ?_
  · exact cellHalf_subset_cellInnerOne ε (halfChart i ε (oneCellHalfPt Y ι f i ε)).2
  · exact cellHalf_subset_cellInnerOne ε (cellHalfPt ε).2
  · rw [halfChart_apply, oneCellHalfPt_coe]

/-! ## The contraction of a half-cell -/

/-- **The contraction of the `i`-th half-cell onto its midpoint**, transported from the model
half along the chart. -/
noncomputable def halfContract (i : ι) (ε : Bool) :
    C(↥(oneCellHalf Y ι f i ε) × unitInterval, ↥(oneCellHalf Y ι f i ε)) where
  toFun p :=
    ⟨oneCellMap Y ι f i ↑(cellHalfContract ε (halfChart i ε p.1, p.2)),
      ⟨↑(cellHalfContract ε (halfChart i ε p.1, p.2)),
        (cellHalfContract ε (halfChart i ε p.1, p.2)).2, rfl⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((oneCellMap Y ι f i).continuous.comp
      (continuous_subtype_val.comp ((cellHalfContract ε).continuous.comp
        (((halfChart i ε).continuous.comp continuous_fst).prodMk continuous_snd)))) _

theorem halfContract_zero (i : ι) (ε : Bool) (x : ↥(oneCellHalf Y ι f i ε)) :
    halfContract i ε (x, 0) = x := by
  refine Subtype.ext ?_
  show oneCellMap Y ι f i ↑(cellHalfContract ε (halfChart i ε x, 0)) =
    (x : attachOneCells Y ι f)
  rw [cellHalfContract_zero]
  exact halfChart_apply i ε x

theorem halfContract_one (i : ι) (ε : Bool) (x : ↥(oneCellHalf Y ι f i ε)) :
    ((halfContract i ε (x, 1) : ↥(oneCellHalf Y ι f i ε)) : attachOneCells Y ι f) =
      (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f) := by
  show oneCellMap Y ι f i ↑(cellHalfContract ε (halfChart i ε x, 1)) =
    (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f)
  rw [cellHalfContract_one, oneCellHalfPt_coe]

theorem halfContract_pt (i : ι) (ε : Bool) (t : unitInterval) :
    halfContract i ε (oneCellHalfPt Y ι f i ε, t) = oneCellHalfPt Y ι f i ε := by
  refine Subtype.ext ?_
  show oneCellMap Y ι f i
      ↑(cellHalfContract ε (halfChart i ε (oneCellHalfPt Y ι f i ε), t)) =
    (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f)
  rw [halfChart_pt, cellHalfContract_pt, oneCellHalfPt_coe]

/-! ## The compression property of a half-cell -/

theorem compressRel_oneCellHalf (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) (i : ι) (ε : Bool) (d : ℕ) :
    Work.RatHurewicz.CompressRel ↥(Work.Serre.OneCell.oneCellHalf Y ι f i ε)
      {x : ↥(Work.Serre.OneCell.oneCellHalf Y ι f i ε) |
        (x : Work.Serre.attachOneCells Y ι f) =
          (Work.Serre.OneCell.oneCellHalfPt Y ι f i ε : Work.Serre.attachOneCells Y ι f)} d := by
  have hA : {x : ↥(oneCellHalf Y ι f i ε) | (x : attachOneCells Y ι f) =
      (oneCellHalfPt Y ι f i ε : attachOneCells Y ι f)} = {oneCellHalfPt Y ι f i ε} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact Subtype.ext_iff.symm
  rw [hA]
  exact Work.Serre.compressRel_singleton_of_contraction (oneCellHalfPt Y ι f i ε)
    (halfContract i ε) (fun x => halfContract_zero i ε x)
    (fun x => Subtype.ext (halfContract_one i ε x))
    (fun t => halfContract_pt i ε t) d

end

end Work.Serre.OneCell
