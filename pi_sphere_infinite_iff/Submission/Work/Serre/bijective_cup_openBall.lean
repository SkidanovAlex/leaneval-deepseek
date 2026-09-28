import Mathlib
import Submission.Work.Serre.thomCylGluing
import Submission.Work.RatHurewicz.cutCoverPiece

/-!
# The local cup isomorphism over an open ball of an attached cell

For the cellular step of the CW-model Thom case (`Work.Serre.thomCylCellStep`) one needs the
*local* bijectivity of the mixed cup product with the extension class `Work.Serre.cellStepU` over
the part of the mapping cylinder lying over an open ball of an attached cell.

This file supplies it (`Work.Serre.bijective_cup_openBall`) as the general-radius `R ∈ (0,1]`
instance of `Work.RatHurewicz.cupBijective_cylPre`: the image
`cellImg f i (cellOpenBallSet (D-2) R)` of the open model ball of radius `R` under the
characteristic map is open (`Work.RatHurewicz.isOpen_cellMap_image`, using `R ≤ 1`), and it is
weakly contractible and path connected, because the characteristic map is a homeomorphism onto its
image on any open part of the open model cell (`Work.RatHurewicz.cellMapImageHomeo`) and the open
ball is convex.  The non-vanishing of the restricted class is
`Work.RatHurewicz.cellwiseNonvanishing`, and `Work.Serre.cellStepU_ne_zero` says that the extension
class itself is non-zero.

The geometric input is the general-`R` version of `Work.RatHurewicz.csrOpenBallContractible` (which
is the case `R = 1/2`); it is proved here as `Work.Serre.cellImgOpenBall_contractible_aux`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## The open model ball as an honest open ball -/

/-- The open model ball `cellOpenBallSet n R` is homeomorphic to the honest open ball
`Metric.ball (0 : CellVec n) R`: the two subtypes have the same underlying points, and `R ≤ 1`
puts the ball inside the closed model cell. -/
def ballCellOpenHomeo (n : ℕ) (R : ℝ) (hR1 : R ≤ 1) :
    ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R) ≃ₜ ↥(cellOpenBallSet n R) where
  toFun x := ⟨⟨x.1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h := x.2
      rw [Metric.mem_ball, dist_zero_right] at h
      linarith⟩, by
      show ‖(x.1 : Work.RatHurewicz.CellVec n)‖ < R
      have h := x.2
      rwa [Metric.mem_ball, dist_zero_right] at h⟩
  invFun y := ⟨(y.1 : Work.RatHurewicz.CellVec n), by
      rw [Metric.mem_ball, dist_zero_right]
      exact y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The centre of the honest open ball. -/
def metricBallCentre (n : ℕ) {R : ℝ} (hR0 : 0 < R) :
    ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R) :=
  ⟨0, by rw [Metric.mem_ball, dist_zero_right]; simpa using hR0⟩

/-- The radial contraction of the honest open ball onto its centre. -/
def modelBallContraction (n : ℕ) (R : ℝ) :
    C(↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R) × unitInterval,
      ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R)) where
  toFun p := ⟨(1 - (p.2 : ℝ)) • p.1.1, by
      rw [Metric.mem_ball, dist_zero_right]
      have hp : ‖(p.1.1 : Work.RatHurewicz.CellVec n)‖ < R := by
        have h := p.1.2; rw [Metric.mem_ball, dist_zero_right] at h; exact h
      calc ‖(1 - (p.2 : ℝ)) • (p.1.1 : Work.RatHurewicz.CellVec n)‖
          ≤ ‖(p.1.1 : Work.RatHurewicz.CellVec n)‖ :=
            Work.RatHurewicz.norm_smul_one_sub_le _ p.2.2.1 p.2.2.2
        _ < R := hp⟩
  continuous_toFun := by fun_prop

theorem modelBallContraction_zero (n : ℕ) (R : ℝ)
    (y : ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R)) :
    modelBallContraction n R (y, 0) = y := by
  apply Subtype.ext
  show (1 - ((0 : unitInterval) : ℝ)) • (y.1 : Work.RatHurewicz.CellVec n)
      = (y.1 : Work.RatHurewicz.CellVec n)
  simp

theorem modelBallContraction_one (n : ℕ) (R : ℝ) (hR0 : 0 < R)
    (y : ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R)) :
    modelBallContraction n R (y, 1) = metricBallCentre n hR0 := by
  apply Subtype.ext
  show (1 - ((1 : unitInterval) : ℝ)) • (y.1 : Work.RatHurewicz.CellVec n)
      = ((metricBallCentre n hR0).1 : Work.RatHurewicz.CellVec n)
  simp [metricBallCentre]

theorem modelBallContraction_centre (n : ℕ) (R : ℝ) (hR0 : 0 < R) (t : unitInterval) :
    modelBallContraction n R (metricBallCentre n hR0, t) = metricBallCentre n hR0 := by
  apply Subtype.ext
  show (1 - (t : ℝ)) • ((metricBallCentre n hR0).1 : Work.RatHurewicz.CellVec n)
      = ((metricBallCentre n hR0).1 : Work.RatHurewicz.CellVec n)
  simp [metricBallCentre]

/-- **The image of an open model ball under the characteristic map is weakly contractible and path
connected**, for every radius `0 < R ≤ 1`: the general-`R` version of
`Work.RatHurewicz.csrOpenBallContractible` (which is the case `R = 1/2`).

The characteristic map is a homeomorphism onto its image on any open part of the open model cell
(`Work.RatHurewicz.cellMapImageHomeo`), and the open model ball of radius `R` is homeomorphic to
the honest open ball `Metric.ball 0 R`, which is convex and nonempty. -/
theorem cellImgOpenBall_contractible_aux (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∃ b₀ : ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)),
      (∀ j : ℕ, Subsingleton (HomotopyGroup (Fin j)
        ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) b₀)) ∧
      PathConnectedSpace ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) := by
  classical
  have hUo : IsOpen (cellOpenBallSet n R) := isOpen_cellOpenBallSet n R
  have hUsub : cellOpenBallSet n R ⊆ Work.RatHurewicz.cellInner n :=
    cellOpenBallSet_subset_cellInner hR1
  let e₂ : ↥(cellOpenBallSet n R) ≃ₜ
      ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) :=
    Work.RatHurewicz.cellMapImageHomeo (n := n) (Γ := Y) (ι := ι) f i hUo hUsub
  let e₁ : ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R) ≃ₜ ↥(cellOpenBallSet n R) :=
    ballCellOpenHomeo n R hR1
  let e : ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R) ≃ₜ
      ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) := e₁.trans e₂
  let c : ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R) := metricBallCentre n hR0
  let b₀ : ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) := e c
  have hM : ContractibleSpace ↥(Metric.ball (0 : Work.RatHurewicz.CellVec n) R) :=
    (convex_ball (0 : Work.RatHurewicz.CellVec n) R).contractibleSpace
      ⟨0, by rw [Metric.mem_ball, dist_zero_right]; simpa using hR0⟩
  have hXt : ContractibleSpace ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) :=
    e.symm.contractibleSpace
  have hHcont : Continuous fun p : ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) ×
      unitInterval => e (modelBallContraction n R (e.symm p.1, p.2)) :=
    e.continuous.comp ((modelBallContraction n R).continuous.comp
      (Continuous.prodMk (e.symm.continuous.comp continuous_fst) continuous_snd))
  let H : C(↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R)) × unitInterval,
      ↥(Work.Serre.cellImg f i (Work.Serre.cellOpenBallSet n R))) :=
    ⟨fun p => e (modelBallContraction n R (e.symm p.1, p.2)), hHcont⟩
  refine ⟨b₀, fun j =>
    Work.RatHurewicz.subsingleton_homotopyGroup_of_contraction H b₀ ?_ ?_ ?_, inferInstance⟩
  · intro x
    show e (modelBallContraction n R (e.symm x, 0)) = x
    rw [modelBallContraction_zero, Homeomorph.apply_symm_apply]
  · intro x
    show e (modelBallContraction n R (e.symm x, 1)) = b₀
    rw [modelBallContraction_one n R hR0]
  · intro t
    show e (modelBallContraction n R (e.symm b₀, t)) = b₀
    have hb : e.symm b₀ = c := Homeomorph.symm_apply_apply e c
    rw [hb, modelBallContraction_centre]

/-! ## The target -/

theorem bijective_cup_openBall (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))
    {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (i : ι) :
    ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥((Work.Serre.cylRetract q) ⁻¹'
          (Work.Serre.cellImg (Γ := Γ) (ι := ι) f i (Work.Serre.cellOpenBallSet (D - 2) R))) =>
        (Work.Thom.mixedCupC ℚ (Work.Serre.glueSub (Set.range (Work.Serre.cylIncl q))
            ((Work.Serre.cylRetract q) ⁻¹'
              (Work.Serre.cellImg (Γ := Γ) (ι := ι) f i (Work.Serre.cellOpenBallSet (D - 2) R))))
            m (r + 1)) x
          ((Work.Thom.relCohMap (Work.Serre.glueInclT ((Work.Serre.cylRetract q) ⁻¹'
              (Work.Serre.cellImg (Γ := Γ) (ι := ι) f i (Work.Serre.cellOpenBallSet (D - 2) R))))
            (Work.Serre.glueSub (Set.range (Work.Serre.cylIncl q))
              ((Work.Serre.cylRetract q) ⁻¹'
                (Work.Serre.cellImg (Γ := Γ) (ι := ι) f i (Work.Serre.cellOpenBallSet (D - 2) R))))
            (Set.range (Work.Serre.cylIncl q)) (fun _ hy => hy) ℚ (r + 1)).hom
            (Work.Serre.cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH))) := by
  classical
  intro m hm
  haveI hΓ' : PathConnectedSpace (Work.RatHurewicz.attachCells (D - 2) Γ ι f) := by
    haveI := hΓ
    exact Work.Serre.CWModel.pathConnectedSpace_attachCells (D - 2) Γ ι f
  obtain ⟨b₀, hVc, hVpc⟩ := cellImgOpenBall_contractible_aux (D - 2) Γ ι f i hR0 hR1
  have hVopen : IsOpen (Work.Serre.cellImg (Γ := Γ) (ι := ι) f i
      (Work.Serre.cellOpenBallSet (D - 2) R)) :=
    Work.RatHurewicz.isOpen_cellMap_image (i := i) (U := Work.Serre.cellOpenBallSet (D - 2) R)
      (Work.Serre.isOpen_cellOpenBallSet (D - 2) R)
      (Work.Serre.cellOpenBallSet_subset_cellInner hR1)
  have hU : Work.Serre.cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH ≠ 0 :=
    Work.Serre.cellStepU_ne_zero r N D hr hN hD hΓ ι f q hq hvan hpc IH
  exact Work.RatHurewicz.cupBijective_cylPre (r := r) (N := N) hr hΓ' q hq hpc hvan hgen
    (Work.Serre.cellImg (Γ := Γ) (ι := ι) f i (Work.Serre.cellOpenBallSet (D - 2) R))
    hVopen b₀ hVc hVpc (Work.Serre.cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) hU m
    (by omega)

end

end Work.Serre
