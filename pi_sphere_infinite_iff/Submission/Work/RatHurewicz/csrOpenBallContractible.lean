import Mathlib
import Submission.Work.Serre.PerCell.exists_homeo_pair
import Submission.Work.RatHurewicz.Cofibre.ConeContract
import Submission.Work.RatHurewicz.Cofibre.BMHyp
import Submission.Work.Serre.csrGeom
import Submission.Work.Serre.Csr.Defs

set_option synthInstance.maxHeartbeats 400000

/-!
# The open half-ball of an attached cell is contractible

For `Z = attachCells n Y ι f` with attaching maps `f : ι → C(S^{n+1}, Y)`, the `i`-th *open
half-ball* `csrOpenBall n Y ι f i` is the image of the open model ball of radius `1/2` under the
characteristic map `cellMap i`.  It is homeomorphic to the open ball of radius `1/2` in
`ℝ^{n+2}` (the homeomorphism `Work.Serre.PerCell.csrOpenBallHomeo`), hence contractible.

This file records that: `↥(csrOpenBall n Y ι f i)` is contractible, so all of its homotopy groups
are trivial and it is path connected.  The proof transports the convexity-contraction of
`Metric.ball (0 : ℝ^{n+2}) (1/2)` along the two homeomorphisms
`↥(Metric.ball 0 (1/2)) ≃ₜ ↥(dOpen n (1/2)) ≃ₜ ↥(csrOpenBall n Y ι f i)`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-! ## The open model ball is homeomorphic to a genuine open ball -/

/-- The open model ball `dOpen n (1/2) = {x : cellDisk n | ‖x‖ < 1/2}` is homeomorphic to the
open ball `Metric.ball (0 : ℝ^{n+2}) (1/2)` of the ambient Euclidean space (they have the same
underlying set, the subtype structure differing only in nesting). -/
def ballDOpenHomeo (n : ℕ) :
    ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 2))) (1/2)) ≃ₜ
      ↥(Work.Serre.dOpen n (1/2)) where
  toFun x := ⟨⟨x.1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h := x.2
      rw [Metric.mem_ball, dist_zero_right] at h
      linarith⟩, by
      show ‖(x.1 : EuclideanSpace ℝ (Fin (n + 2)))‖ < 1/2
      have h := x.2
      rw [Metric.mem_ball, dist_zero_right] at h
      exact h⟩
  invFun y := ⟨(y.1 : Work.RatHurewicz.CellVec n), by
      rw [Metric.mem_ball, dist_zero_right]
      show ‖(y.1 : Work.RatHurewicz.CellVec n)‖ < 1/2
      exact y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The open model ball is contractible** (it is convex and carries the origin). -/
theorem contractible_dOpen (n : ℕ) : ContractibleSpace ↥(Work.Serre.dOpen n (1/2)) := by
  haveI : ContractibleSpace ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 2))) (1/2)) :=
    (convex_ball (0 : EuclideanSpace ℝ (Fin (n + 2))) (1/2)).contractibleSpace
      ⟨0, by simp [Metric.mem_ball]⟩
  exact (ballDOpenHomeo n).symm.contractibleSpace

/-! ## The radial contraction of the open model ball -/

/-- Elementary norm estimate: for `0 ≤ t ≤ 1`, `‖(1 - t) • y‖ ≤ ‖y‖`. -/
lemma norm_smul_one_sub_le {n : ℕ} (y : Work.RatHurewicz.CellVec n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • y‖ ≤ ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
  exact mul_le_of_le_one_left (norm_nonneg y) (by linarith)

/-- The centre of the open model ball, as a point of `↥(dOpen n (1/2))`. -/
def dOpenCentre (n : ℕ) : ↥(Work.Serre.dOpen n (1/2)) :=
  ⟨Work.RatHurewicz.cellDiskCentre n, by
    show ‖(Work.RatHurewicz.cellDiskCentre n : Work.RatHurewicz.CellVec n)‖ < 1/2
    rw [Work.RatHurewicz.cellDiskCentre_coe]
    norm_num⟩

/-- The radial contraction of the open model ball onto its centre: `(y, t) ↦ (1 - t) • y`. -/
def contrD (n : ℕ) :
    C(↥(Work.Serre.dOpen n (1/2)) × unitInterval, ↥(Work.Serre.dOpen n (1/2))) where
  toFun p := ⟨⟨(1 - (p.2 : ℝ)) • (p.1.1 : Work.RatHurewicz.CellVec n), by
      have hy : ‖(p.1.1 : Work.RatHurewicz.CellVec n)‖ < 1/2 := p.1.2
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖(1 - (p.2 : ℝ)) • (p.1.1 : Work.RatHurewicz.CellVec n)‖
          ≤ ‖(p.1.1 : Work.RatHurewicz.CellVec n)‖ :=
            norm_smul_one_sub_le _ p.2.2.1 p.2.2.2
        _ ≤ 1 := by linarith⟩, by
      show ‖(1 - (p.2 : ℝ)) • (p.1.1 : Work.RatHurewicz.CellVec n)‖ < 1/2
      have hy : ‖(p.1.1 : Work.RatHurewicz.CellVec n)‖ < 1/2 := p.1.2
      calc ‖(1 - (p.2 : ℝ)) • (p.1.1 : Work.RatHurewicz.CellVec n)‖
          ≤ ‖(p.1.1 : Work.RatHurewicz.CellVec n)‖ :=
            norm_smul_one_sub_le _ p.2.2.1 p.2.2.2
        _ < 1/2 := hy⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop

theorem contrD_zero (n : ℕ) (y : ↥(Work.Serre.dOpen n (1/2))) :
    contrD n (y, 0) = y := by
  apply Subtype.ext
  apply Subtype.ext
  show (1 - ((0 : unitInterval) : ℝ)) • (y.1 : Work.RatHurewicz.CellVec n)
      = (y.1 : Work.RatHurewicz.CellVec n)
  simp

theorem contrD_one (n : ℕ) (y : ↥(Work.Serre.dOpen n (1/2))) :
    contrD n (y, 1) = dOpenCentre n := by
  apply Subtype.ext
  apply Subtype.ext
  show (1 - ((1 : unitInterval) : ℝ)) • (y.1 : Work.RatHurewicz.CellVec n)
      = ((dOpenCentre n).1 : Work.RatHurewicz.CellVec n)
  simp [dOpenCentre]

theorem contrD_centre (n : ℕ) (t : unitInterval) :
    contrD n (dOpenCentre n, t) = dOpenCentre n := by
  apply Subtype.ext
  apply Subtype.ext
  show (1 - (t : ℝ)) • ((dOpenCentre n).1 : Work.RatHurewicz.CellVec n)
      = ((dOpenCentre n).1 : Work.RatHurewicz.CellVec n)
  simp [dOpenCentre]

/-! ## The open half-ball of an attached cell -/

/-- **The open half-ball of an attached cell is contractible.**  It is homeomorphic to the open
model ball (`Work.Serre.PerCell.csrOpenBallHomeo`), which is convex. -/
theorem contractible_csrOpenBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    ContractibleSpace ↥(Work.Serre.csrOpenBall n Y ι f i) := by
  haveI hC : ContractibleSpace ↥(Work.Serre.dOpen n (1/2)) := contractible_dOpen n
  exact (Work.Serre.PerCell.csrOpenBallHomeo n Y ι f i).contractibleSpace

theorem csrOpenBallContractible (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    ∃ b₀ : ↥(Work.Serre.csrOpenBall n Y ι f i),
      (∀ j : ℕ, Subsingleton (HomotopyGroup (Fin j) ↥(Work.Serre.csrOpenBall n Y ι f i) b₀)) ∧
      PathConnectedSpace ↥(Work.Serre.csrOpenBall n Y ι f i) := by
  let X := ↥(Work.Serre.csrOpenBall n Y ι f i)
  let e : X ≃ₜ ↥(Work.Serre.dOpen n (1/2)) := Work.Serre.PerCell.csrOpenBallHomeo n Y ι f i
  let b₀ : X := e.symm (dOpenCentre n)
  haveI hC : ContractibleSpace ↥(Work.Serre.dOpen n (1/2)) := contractible_dOpen n
  haveI hX : ContractibleSpace X := e.contractibleSpace
  refine ⟨b₀, fun j => ?_, inferInstance⟩
  -- The contraction of `X`, transported from the radial contraction of the open model ball.
  let H : C(X × unitInterval, X) :=
    ⟨fun p => e.symm (contrD n (e p.1, p.2)), by
      exact e.symm.continuous.comp ((contrD n).continuous.comp
        (Continuous.prodMk (e.continuous.comp continuous_fst) continuous_snd))⟩
  refine subsingleton_homotopyGroup_of_contraction H b₀ ?_ ?_ ?_
  · intro x
    show e.symm (contrD n (e x, 0)) = x
    rw [contrD_zero, Homeomorph.symm_apply_apply]
  · intro x
    show e.symm (contrD n (e x, 1)) = b₀
    rw [contrD_one]
  · intro t
    show e.symm (contrD n (e b₀, t)) = b₀
    rw [Homeomorph.apply_symm_apply, contrD_centre]

end

end Work.RatHurewicz
