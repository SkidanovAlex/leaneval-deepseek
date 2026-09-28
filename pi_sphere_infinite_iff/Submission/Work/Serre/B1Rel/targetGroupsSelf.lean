import Mathlib
import Submission.Work.Serre.B1Rel.Defs
import Submission.Work.Serre.OneCell.Compress
import Submission.Work.Serre.Csr.ballPairHomology
import Submission.Work.Serre.Csr.Base
import Submission.Work.Serre.CsrSharp.relChainsRHomeomorphCompat

set_option synthInstance.maxHeartbeats 400000

/-!
# The target groups of the sharp rational `1`-cell step (self-contained)

`Work.Serre.B1Rel.oneCellTargetGroupsSelf`: the relative rational homology of the target pair
`(oᵢ, oᵢ ∖ {cᵢ})` of the `i`-th open `1`-cell (open cell, its centre deleted) is `ℚ` in degree `1`
and vanishes in every other degree.

The pair is identified, along the chart of the cell and the linear structure of `ℝ¹`, with the pair
`(B¹, B¹ ∖ {0})` of the open unit ball of `ℝ¹ = EuclideanSpace ℝ (Fin 1)` and its punctured
version, whose relative homology is `Work.Serre.Csr.ballPairHomology` at `D = 1`
(`ℤ` in degree `1`, zero elsewhere); relative homology is invariant under a homeomorphism of pairs
(`Work.Serre.CsrSharp.relChainsRHomeomorphCompat_gen`), and the result is base changed `ℤ → ℚ`
(`Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int`,
`Work.Serre.Csr.relChainsR_homology_iso_ratUnit`).

This module is deliberately self-contained (it only imports the stable `Csr`/`CsrSharp`/`OneCell`
layers), so that the final target `Work.Serre.B1Rel.oneCellStepSharp` does not depend on the
`RatTower` chapter, which is still being reorganised.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

open Work.Serre.OneCell

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(Work.Serre.cellSphereZero, Y)}

/-! ## The norms of the flat one-dimensional model -/

/-- The norm of the point `(r, …)` of `EuclideanSpace ℝ (Fin 1) = ℝ¹` is `‖r‖`. -/
theorem targetNormToLp (r : ℝ) :
    ‖(WithLp.toLp 2 (fun _ : Fin 1 => r) : EuclideanSpace ℝ (Fin 1))‖ = ‖r‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one]
  simp [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

/-- The norm of a point of `EuclideanSpace ℝ (Fin 1)` is the norm of its coordinate. -/
theorem targetNormApply (v : EuclideanSpace ℝ (Fin 1)) : ‖v 0‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one]
  simp [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

/-- A point of the open unit ball of `ℝ¹` has coordinate of norm `< 1`. -/
theorem targetBallCoordLt (z : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) : ‖z.1 0‖ < 1 :=
  lt_of_le_of_lt (le_of_eq (targetNormApply z.1)) (by
    have h2 := Metric.mem_ball.mp z.2
    rwa [dist_eq_norm, sub_zero] at h2)

/-- The point `(r, …)` of `ℝ¹` vanishes if and only if `r = 0`. -/
theorem targetToLpEqZero (r : ℝ) :
    (WithLp.toLp 2 (fun _ : Fin 1 => r) : EuclideanSpace ℝ (Fin 1)) = 0 ↔ r = 0 := by
  constructor
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v.ofLp 0) h
    simpa using h2
  · intro h
    rw [h]
    exact WithLp.toLp_ofLp 2 (0 : EuclideanSpace ℝ (Fin 1))

/-! ## The open model interval is the flat unit ball -/

/-- **The open model interval `(-1,1) ⊆ D¹` is the open unit ball of `ℝ¹`.** -/
def innerBallHomeo : ↥cellInnerOne ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 where
  toFun x := ⟨WithLp.toLp 2 (fun _ : Fin 1 => ((x : Work.Serre.cellDiskOne) : ℝ)), by
    rw [Metric.mem_ball, dist_zero_right, targetNormToLp]
    exact x.2⟩
  invFun z := ⟨⟨z.1 0, by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_lt (targetBallCoordLt z)⟩, targetBallCoordLt z⟩
  left_inv x := rfl
  right_inv z := by
    refine Subtype.ext ?_
    have hf : (fun _ : Fin 1 => z.1.ofLp 0) = z.1.ofLp := by
      funext i
      rw [Subsingleton.elim i 0]
    show WithLp.toLp 2 (fun _ : Fin 1 => z.1.ofLp 0) = z.1
    rw [hf, WithLp.toLp_ofLp]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp
      (continuous_pi (fun _ => (continuous_subtype_val.comp continuous_subtype_val :
        Continuous fun x : ↥cellInnerOne => ((x : Work.Serre.cellDiskOne) : ℝ))))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    exact (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_subtype_val

/-- The underlying point of `EuclideanSpace ℝ (Fin 1)` of `innerBallHomeo t`. -/
theorem innerBallHomeo_coe (t : ↥cellInnerOne) :
    ((innerBallHomeo t : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) :
        EuclideanSpace ℝ (Fin 1))
      = WithLp.toLp 2 (fun _ : Fin 1 => ((t : Work.Serre.cellDiskOne) : ℝ)) := rfl

/-- The centre `0` of the open model interval, as a point of `↥cellInnerOne`. -/
def innerCentre : ↥cellInnerOne :=
  ⟨cellDiskOneCentreOne, by
    rw [mem_cellInnerOne, show ((cellDiskOneCentreOne : Work.Serre.cellDiskOne) : ℝ) = 0 from rfl]
    norm_num⟩

/-- A point of `↥cellInnerOne` is the centre exactly when its coordinate vanishes. -/
theorem innerCentre_iff_coe_eq_zero (t : ↥cellInnerOne) :
    t = innerCentre ↔ ((t : Work.Serre.cellDiskOne) : ℝ) = 0 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)

/-- The flat coordinate of a point of the open model interval vanishes exactly at the centre. -/
theorem targetToLpNeZeroInnerCentre (t : ↥cellInnerOne) :
    (WithLp.toLp 2 (fun _ : Fin 1 => ((t : Work.Serre.cellDiskOne) : ℝ)) :
        EuclideanSpace ℝ (Fin 1)) ≠ 0 ↔ t ≠ innerCentre := by
  rw [ne_eq, ne_eq, targetToLpEqZero]
  constructor
  · intro h ht
    exact h ((innerCentre_iff_coe_eq_zero t).mp ht)
  · intro h hr
    exact h ((innerCentre_iff_coe_eq_zero t).mpr hr)

/-! ## The chart of the open `1`-cell -/

/-- The chart of the open `1`-cell, as a homeomorphism onto the open model interval. -/
def perCellChartHomeoSelf (i : ι) : ↥(cellInteriorOne Y ι f i) ≃ₜ ↥cellInnerOne where
  toFun := cellChart Y ι f i
  invFun t := ⟨oneCellMap Y ι f i t, ⟨t, t.2, rfl⟩⟩
  left_inv y := Subtype.ext (cellChart_apply i y)
  right_inv t := cellChart_symm i t
  continuous_toFun := (cellChart Y ι f i).continuous
  continuous_invFun := Continuous.subtype_mk
    ((oneCellMap Y ι f i).continuous.comp continuous_subtype_val) _

/-- The chart carries the centre of the cell to the centre of the model interval. -/
theorem cellChart_centreSelf (i : ι) :
    cellChart Y ι f i ⟨oneCellCentreOne Y ι f i, oneCellCentreOne_mem_cellInteriorOne f i⟩
      = innerCentre := by
  refine Subtype.ext ?_
  refine oneCellMap_injOn_inner f i (cellChart Y ι f i ⟨_, _⟩).2 innerCentre.2 ?_
  rw [cellChart_apply]
  rfl

/-- The chart respects the punctured subsets: the centre of the cell is exactly the point mapped to
the centre of the model interval. -/
theorem cellChart_ne_centre_iffSelf (i : ι) (y : ↥(cellInteriorOne Y ι f i)) :
    (y : Work.Serre.attachOneCells Y ι f) ≠ oneCellCentreOne Y ι f i ↔
      cellChart Y ι f i y ≠ innerCentre := by
  constructor
  · intro h hc
    exact h (by rw [← cellChart_apply i y, hc]; rfl)
  · intro h hc
    refine h ?_
    have hy : y = ⟨oneCellCentreOne Y ι f i, oneCellCentreOne_mem_cellInteriorOne f i⟩ :=
      Subtype.ext hc
    rw [hy, cellChart_centreSelf]

/-! ## The target pair as a flat ball pair -/

/-- **The per-cell target pair as the flat unit ball pair**: the open `i`-th `1`-cell with its
centre deleted is homeomorphic, as a pair, to the open unit ball of `ℝ¹` with the origin deleted. -/
def perCellBallHomeoSelf (i : ι) :
    ↥(cellInteriorOne Y ι f i) ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  (perCellChartHomeoSelf i).trans innerBallHomeo

theorem perCellBallHomeoSelf_apply (i : ι) (y : ↥(cellInteriorOne Y ι f i)) :
    perCellBallHomeoSelf i y = innerBallHomeo (perCellChartHomeoSelf i y) := rfl

/-- The per-cell ball homeomorphism respects the relative parts. -/
theorem perCellBallHomeoSelf_rel (i : ι) (y : ↥(cellInteriorOne Y ι f i)) :
    y ∈ tgtRelOne Y ι f i ↔ (perCellBallHomeoSelf i y : EuclideanSpace ℝ (Fin 1)) ≠ 0 := by
  have hEq : (perCellBallHomeoSelf i y : EuclideanSpace ℝ (Fin 1))
      = WithLp.toLp 2 (fun _ : Fin 1 =>
          (((cellChart Y ι f i y : ↥cellInnerOne) : Work.Serre.cellDiskOne) : ℝ)) := by
    rw [perCellBallHomeoSelf_apply, innerBallHomeo_coe]
    rfl
  have hmem : y ∈ tgtRelOne Y ι f i ↔
      (y : Work.Serre.attachOneCells Y ι f) ≠ oneCellCentreOne Y ι f i := by
    constructor
    · intro h hc
      exact h.2 (by simp [hc])
    · intro h
      exact ⟨y.2, fun hc => h (Set.mem_singleton_iff.mp hc)⟩
  rw [hmem, hEq, targetToLpNeZeroInnerCentre, cellChart_ne_centre_iffSelf]

/-! ## The target groups -/

theorem oneCellTargetGroupsSelf (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) (i : ι) :
    (∀ m : ℕ, m ≠ 1 → CategoryTheory.Limits.IsZero
      ((Work.Serre.B1Rel.tgtOne Y ι f i).homology m)) ∧
    Nonempty ((Work.Serre.B1Rel.tgtOne Y ι f i).homology 1 ≅ ModuleCat.of ℚ ℚ) := by
  -- the flat model: the open unit ball of `ℝ¹` with its origin deleted
  obtain ⟨hvan, hisoNe⟩ := Work.Serre.Csr.ballPairHomology 1 le_rfl 1 (by norm_num)
  obtain ⟨hiso⟩ := hisoNe
  -- transport along the pair homeomorphism
  have hpair : ∀ m : ℕ, Nonempty ((Work.StemsB.relChainsR ℤ
      (TopCat.of ↥(cellInteriorOne Y ι f i))
      (tgtRelOne Y ι f i)).homology m ≅
      (Work.StemsB.relChainsR ℤ
        (TopCat.of ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1))
        {z : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) |
          (z : EuclideanSpace ℝ (Fin 1)) ≠ 0}).homology m) := fun m =>
    Work.Serre.CsrSharp.relChainsRHomeomorphCompat_gen ℤ _ _
      (tgtRelOne Y ι f i)
      {z : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) |
        (z : EuclideanSpace ℝ (Fin 1)) ≠ 0}
      (perCellBallHomeoSelf i) (perCellBallHomeoSelf_rel i) m
  have hvanX : ∀ m : ℕ, m ≠ 1 → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of ↥(cellInteriorOne Y ι f i))
        (tgtRelOne Y ι f i)).homology m) := by
    intro m hm
    obtain ⟨e⟩ := hpair m
    exact IsZero.of_iso (hvan m hm) e
  have hisoX : Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(cellInteriorOne Y ι f i))
      (tgtRelOne Y ι f i)).homology 1 ≅ ModuleCat.of ℤ ℤ) := by
    obtain ⟨e⟩ := hpair 1
    exact ⟨e ≪≫ hiso⟩
  exact ⟨fun m hm => Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int _ _ m (hvanX m hm),
    Work.Serre.Csr.relChainsR_homology_iso_ratUnit _ _ 1 hisoX⟩

end

end Work.Serre.B1Rel
