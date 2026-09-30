import Mathlib
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.OneCell.Compress

/-!
# Vanishing of the rational homology of an open `1`-cell

The open `i`-th cell `cellInteriorOne Y ι f i` is, by `exists_chart`, an open copy of the open model
interval `cellInnerOne = {x : D¹ | ‖x‖ < 1}`, via the characteristic map.  The model interval is
homeomorphic to the open real interval `(-1,1)` (`homeoCellInnerOneIoo`), which is convex, hence
contractible; so its rational homology vanishes in positive degrees
(`Work.Cohomology.homologyContractible_ring`).  Transporting along the chart
(`isZero_ratH_of_homeo`) gives the statement.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- **The open model interval is the open real interval.**  The inclusion `D¹ → ℝ` restricts to a
homeomorphism `(-1,1) ⊆ D¹ ≅ (-1,1) ⊆ ℝ`. -/
def homeoCellInnerOneIoo : ↥cellInnerOne ≃ₜ ↥(Set.Ioo (-1 : ℝ) 1) where
  toFun := fun x => ⟨((x : cellDiskOne) : ℝ), by
    have hx : ‖((x : cellDiskOne) : ℝ)‖ < 1 := x.2
    rw [Real.norm_eq_abs] at hx
    exact abs_lt.mp hx⟩
  invFun := fun t => ⟨⟨(t : ℝ), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(Set.mem_Ioo.mp t.2).1], by linarith [(Set.mem_Ioo.mp t.2).2]⟩⟩,
    by
      have h : ‖(t : ℝ)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_lt]
        exact Set.mem_Ioo.mp t.2
      exact h⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun :=
    ((continuous_subtype_val (p := fun y : ℝ => y ∈ Metric.closedBall (0 : ℝ) 1)).comp
      (continuous_subtype_val (p := fun z : cellDiskOne => z ∈ cellInnerOne))).subtype_mk
    (fun x => by
      have hx : ‖((x : cellDiskOne) : ℝ)‖ < 1 := x.2
      rw [Real.norm_eq_abs] at hx
      exact abs_lt.mp hx)
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_subtype_val (p := fun y : ℝ => y ∈ Set.Ioo (-1 : ℝ) 1))
    (fun t => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(Set.mem_Ioo.mp t.2).1], by linarith [(Set.mem_Ioo.mp t.2).2]⟩))
    (fun t => by
      have h : ‖(t : ℝ)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_lt]
        exact Set.mem_Ioo.mp t.2
      exact h)

/-- The open model interval is contractible (it is homeomorphic to a convex subset of `ℝ`). -/
theorem contractibleSpace_cellInnerOne : ContractibleSpace ↥cellInnerOne := by
  have hIoo : ContractibleSpace ↥(Set.Ioo (-1 : ℝ) 1) :=
    (convex_Ioo (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  exact homeoCellInnerOneIoo.contractibleSpace

/-- The rational homology of the open model interval vanishes in positive degrees. -/
theorem isZero_ratH_cellInnerOne (k : ℕ) (hk : 0 < k) :
    IsZero (ratH (TopCat.of ↥cellInnerOne) k) := by
  have hc : ContractibleSpace ↥cellInnerOne := contractibleSpace_cellInnerOne
  exact Work.Cohomology.homologyContractible_ring ℚ k hk

theorem isZero_ratH_cellInteriorOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) (i : ι) (k : ℕ) (hk : 0 < k) :
    CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i)) k) := by
  obtain ⟨S, hS1, hS2⟩ := exists_chart (Y := Y) (ι := ι) (f := f) i
  let e : ↥(cellInteriorOne Y ι f i) ≃ₜ ↥cellInnerOne :=
    { toFun := S
      invFun := fun x => ⟨oneCellMap Y ι f i x, ⟨x, x.2, rfl⟩⟩
      left_inv := fun x => Subtype.ext (hS1 x)
      right_inv := fun x => hS2 x
      continuous_toFun := S.continuous
      continuous_invFun := Continuous.subtype_mk
        ((oneCellMap Y ι f i).continuous.comp (continuous_subtype_val
          (p := fun z : cellDiskOne => z ∈ cellInnerOne))) _ }
  exact isZero_ratH_of_homeo e k (isZero_ratH_cellInnerOne k hk)

end

end Work.Serre.OneCell
