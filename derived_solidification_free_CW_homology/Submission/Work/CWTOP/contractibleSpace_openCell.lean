import Mathlib
import Submission.Work.CWTOP.Basic

/-!
# Every open cell of a CW complex is contractible

The characteristic map of the `n`-cell `j` restricts to a homeomorphism from the open unit ball
`ball 0 1 ⊆ Fin n → ℝ` onto the open cell `openCell n j`
(`Work.CWTOP.target_eq_openCell`, `Work.CWTOP.openCellHomeomorph`). The open ball is convex and
non-empty, hence contractible, and contractibility is a homeomorphism invariant. This gives
`Work.CWTOP.contractibleSpace_openCell`.
-/

open Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- The target of the characteristic map of the cell `j` is precisely its open cell. -/
lemma target_eq_openCell (n : ℕ) (j : RelCWComplex.cell C n) :
    (RelCWComplex.map n j).target = RelCWComplex.openCell n j := by
  refine Set.Subset.antisymm ?_ (openCell_subset_target n j)
  intro x hx
  refine ⟨(RelCWComplex.map n j).symm x, ?_, ?_⟩
  · have h := PartialEquiv.map_target (RelCWComplex.map n j) hx
    rwa [RelCWComplex.source_eq] at h
  · exact PartialEquiv.right_inv (RelCWComplex.map n j) hx

/-- The characteristic map of an `n`-cell, restricted to the open unit ball, is a homeomorphism
onto the open cell. -/
noncomputable def openCellHomeomorph (n : ℕ) (j : RelCWComplex.cell C n) :
    ↥(Metric.ball (0 : Fin n → ℝ) 1) ≃ₜ ↥(RelCWComplex.openCell n j) where
  toFun y := ⟨RelCWComplex.map n j y, ⟨(y : Fin n → ℝ), y.2, rfl⟩⟩
  invFun x := ⟨(RelCWComplex.map n j).symm x, by
      have hx : (x : X) ∈ (RelCWComplex.map n j).target := by
        rw [target_eq_openCell]; exact x.2
      have h := PartialEquiv.map_target (RelCWComplex.map n j) hx
      rwa [RelCWComplex.source_eq] at h⟩
  left_inv y := by
    apply Subtype.ext
    exact PartialEquiv.left_inv (RelCWComplex.map n j)
      (by rw [RelCWComplex.source_eq]; exact y.2)
  right_inv x := by
    apply Subtype.ext
    have hx : (x : X) ∈ (RelCWComplex.map n j).target := by
      rw [target_eq_openCell]; exact x.2
    exact PartialEquiv.right_inv (RelCWComplex.map n j) hx
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuousOn_iff_continuous_domRestrict.mp
      ((RelCWComplex.continuousOn n j).mono ball_subset_closedBall))
  continuous_invFun := by
    apply Continuous.subtype_mk
    have h : ContinuousOn (↑(RelCWComplex.map n j).symm) (RelCWComplex.openCell n j) := by
      rw [← target_eq_openCell]
      exact RelCWComplex.continuousOn_symm n j
    exact continuousOn_iff_continuous_domRestrict.mp h

/-- The open unit ball of `Fin n → ℝ` is contractible (it is convex and non-empty). -/
lemma contractibleSpace_ball (n : ℕ) :
    ContractibleSpace ↥(Metric.ball (0 : Fin n → ℝ) 1) :=
  Convex.contractibleSpace (convex_ball 0 1) ⟨0, mem_ball_self zero_lt_one⟩

theorem contractibleSpace_openCell {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (n : ℕ) (j : Topology.RelCWComplex.cell C n) :
    ContractibleSpace (Topology.RelCWComplex.openCell n j) :=
  (openCellHomeomorph n j).contractibleSpace_iff.mp (contractibleSpace_ball n)

end Work.CWTOP
