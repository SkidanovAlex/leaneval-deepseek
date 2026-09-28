import Mathlib
import Submission.Work.Serre.Wedge.Defs
import Submission.Work.Serre.Wedge.Geom
import Submission.Work.Serre.Wedge.LES
import Submission.Work.Serre.Wedge.shellHomotopyEquiv
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.ballPairHomologyTop
import Submission.Work.Cohomology.localCohomology

set_option synthInstance.maxHeartbeats 400000

/-!
# The per-cell computation for the wedge of spheres

The characteristic map of the `i`-th cell is a homeomorphism of the open model cell `cellInner n`
onto the open cell `cellInterior n PUnit ι (wF n ι) i`, and it carries the model shell
`cellShellSet n ρ R` onto the trace of `cellShellImg (wF n ι) ρ R`.  Hence the per-cell relative
homology `H_{n+2}(open cell, shell)` is the relative homology of the model pair
`(cellInner n, cellShellSet n ρ R)`, which the long exact sequence of the pair computes to be `ℤ`
(after `Work.Serre.Wedge.shellHomotopyEquiv`, the shell is a sphere `S^{n+1}`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option maxHeartbeats 8000000

namespace Work.Serre.Wedge

noncomputable section

/-! ## The open model cell is the open ball -/

/-- The open model cell is homeomorphic to the open unit ball of `ℝ^{n+2}`. -/
noncomputable def cellInnerHomeoBall (n : ℕ) :
    ↥(Work.RatHurewicz.cellInner n) ≃ₜ
      ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin (n+2))) 1) where
  toFun x := ⟨((x : Work.RatHurewicz.cellDisk n) : EuclideanSpace ℝ (Fin (n+2))), by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact x.2⟩
  invFun y := ⟨⟨(y : EuclideanSpace ℝ (Fin (n+2))),
      Metric.mem_closedBall.mpr (by
        have hy : ‖(y : EuclideanSpace ℝ (Fin (n+2)))‖ < 1 := by
          have h := y.2
          rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
          exact h
        rw [dist_eq_norm, sub_zero]
        exact le_of_lt hy)⟩, by
      have hy : ‖(y : EuclideanSpace ℝ (Fin (n+2)))‖ < 1 := by
        have h := y.2
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
        exact h
      exact hy⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

/-! ## The section of the characteristic map -/

/-- A continuous section of the characteristic map over the open cell. -/
noncomputable def cellSection (n : ℕ) (ι : Type) (i : ι) :
    C(↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i),
      ↥(Work.RatHurewicz.cellInner n)) :=
  Classical.choose (Work.RatHurewicz.cellInterior_section (n := n) (Y := PUnit) (ι := ι)
    (f := wF n ι) i)

theorem cellSection_spec (n : ℕ) (ι : Type) (i : ι)
    (y : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i)) :
    Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i
        ((cellSection n ι i y : ↥(Work.RatHurewicz.cellInner n)) :
          Work.RatHurewicz.cellDisk n)
      = (y : wX n ι) :=
  Classical.choose_spec (Work.RatHurewicz.cellInterior_section (n := n) (Y := PUnit) (ι := ι)
    (f := wF n ι) i) y

/-- **Two points of open cells of the wedge have the same image only if they are the same point of
the same cell.** -/
theorem cellMap_eq_cellMap_iff {n : ℕ} {ι : Type} {i j : ι}
    {x y : ↥(Work.RatHurewicz.cellInner n)}
    (h : Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i (x : Work.RatHurewicz.cellDisk n)
      = Work.RatHurewicz.cellMap n PUnit ι (wF n ι) j (y : Work.RatHurewicz.cellDisk n)) :
    i = j ∧ x = y := by
  have hrel : Relation.EqvGen (Work.RatHurewicz.attachRel n PUnit ι (wF n ι))
      (Sum.inr (⟨i, (x : Work.RatHurewicz.cellDisk n)⟩ :
        Σ _ : ι, Work.RatHurewicz.cellDisk n))
      (Sum.inr (⟨j, (y : Work.RatHurewicz.cellDisk n)⟩ :
        Σ _ : ι, Work.RatHurewicz.cellDisk n)) := Quotient.exact h
  have h2 := Work.RatHurewicz.eq_of_eqvGen_inr_cellInner (x := (y : Work.RatHurewicz.cellDisk n))
    y.2 hrel
  have h3 := Sum.inr.inj h2
  exact ⟨congrArg Sigma.fst h3, Subtype.ext (congrArg Sigma.snd h3)⟩

/-! ## The open cell is homeomorphic to the open model cell -/

/-- The characteristic map of the `i`-th cell, as a homeomorphism from the open model cell onto
the open cell. -/
noncomputable def cellInteriorHomeo (n : ℕ) (ι : Type) (i : ι) :
    ↥(Work.RatHurewicz.cellInner n) ≃ₜ
      ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) where
  toFun x := ⟨Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i
      (x : Work.RatHurewicz.cellDisk n), ⟨(x : Work.RatHurewicz.cellDisk n), x.2, rfl⟩⟩
  invFun y := cellSection n ι i y
  left_inv x := by
    refine Work.RatHurewicz.cellMap_injective_cellInner (f := wF n ι) i ?_
    show Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i
        ((cellSection n ι i ⟨Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i
            (x : Work.RatHurewicz.cellDisk n), ⟨(x : Work.RatHurewicz.cellDisk n), x.2, rfl⟩⟩ :
          ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n)
      = Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i (x : Work.RatHurewicz.cellDisk n)
    rw [cellSection_spec]
  right_inv y :=
    Subtype.ext (cellSection_spec n ι i y)
  continuous_toFun :=
    Continuous.subtype_mk
      ((Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i).continuous.comp continuous_subtype_val) _
  continuous_invFun := (cellSection n ι i).continuous

/-! ## The shell inside a cell is homeomorphic to the model shell -/

/-- The map from the model shell to the trace of `cellShellImg` on the `i`-th open cell. -/
noncomputable def shellToFun (n : ℕ) (ι : Type) (i : ι) (ρ R : ℝ) (hR : R ≤ 1)
    (y : ↥(Work.Serre.cellShellSet n ρ R)) :
    ↥{z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) ρ R} :=
  ⟨⟨Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i (y : Work.RatHurewicz.cellDisk n),
    ⟨(y : Work.RatHurewicz.cellDisk n), Work.Serre.cellShellSet_subset_cellInner hR y.2, rfl⟩⟩,
    Set.mem_iUnion.mpr ⟨i, (y : Work.RatHurewicz.cellDisk n), y.2, rfl⟩⟩

/-- The inverse of `shellToFun`, using the section of the characteristic map. -/
noncomputable def shellInvFun (n : ℕ) (ι : Type) (i : ι) (ρ R : ℝ) (hR : R ≤ 1)
    (z : ↥{z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) ρ R}) :
    ↥(Work.Serre.cellShellSet n ρ R) :=
  ⟨cellSection n ι i z.1, by
    obtain ⟨j, y, hy, hjy⟩ := Set.mem_iUnion.mp z.2
    have hyin : y ∈ Work.RatHurewicz.cellInner n :=
      Work.Serre.cellShellSet_subset_cellInner hR hy
    have heq : Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i
        ((cellSection n ι i z.1 : ↥(Work.RatHurewicz.cellInner n)) :
          Work.RatHurewicz.cellDisk n)
        = Work.RatHurewicz.cellMap n PUnit ι (wF n ι) j y := by
      rw [cellSection_spec, hjy]
    obtain ⟨-, hxy⟩ := cellMap_eq_cellMap_iff (i := i) (j := j)
      (x := cellSection n ι i z.1) (y := ⟨y, hyin⟩) (by simpa using heq)
    rw [hxy]
    exact hy⟩

theorem shellInvFun_shellToFun (n : ℕ) (ι : Type) (i : ι) (ρ R : ℝ) (hR : R ≤ 1)
    (y : ↥(Work.Serre.cellShellSet n ρ R)) :
    shellInvFun n ι i ρ R hR (shellToFun n ι i ρ R hR y) = y := by
  refine Subtype.ext ?_
  show ((cellSection n ι i (shellToFun n ι i ρ R hR y).1 :
      ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n)
    = (y : Work.RatHurewicz.cellDisk n)
  have h : cellSection n ι i (shellToFun n ι i ρ R hR y).1 =
      ⟨(y : Work.RatHurewicz.cellDisk n), Work.Serre.cellShellSet_subset_cellInner hR y.2⟩ := by
    refine Work.RatHurewicz.cellMap_injective_cellInner (f := wF n ι) i ?_
    show Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i
        ((cellSection n ι i (shellToFun n ι i ρ R hR y).1 :
          ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n)
      = Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i (y : Work.RatHurewicz.cellDisk n)
    rw [cellSection_spec]
    rfl
  exact congrArg Subtype.val h

theorem shellToFun_shellInvFun (n : ℕ) (ι : Type) (i : ι) (ρ R : ℝ) (hR : R ≤ 1)
    (z : ↥{z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) ρ R}) :
    shellToFun n ι i ρ R hR (shellInvFun n ι i ρ R hR z) = z :=
  Subtype.ext (Subtype.ext (cellSection_spec n ι i z.1))

theorem continuous_shellToFun (n : ℕ) (ι : Type) (i : ι) (ρ R : ℝ) (hR : R ≤ 1) :
    Continuous (shellToFun n ι i ρ R hR) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact (Work.RatHurewicz.cellMap n PUnit ι (wF n ι) i).continuous.comp continuous_subtype_val

theorem continuous_shellInvFun (n : ℕ) (ι : Type) (i : ι) (ρ R : ℝ) (hR : R ≤ 1) :
    Continuous (shellInvFun n ι i ρ R hR) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.comp
    ((cellSection n ι i).continuous.comp continuous_subtype_val)

/-- **The model shell is homeomorphic to the trace of `cellShellImg` on the `i`-th open cell.** -/
noncomputable def shellInCellHomeo (n : ℕ) (ι : Type) (i : ι) (ρ R : ℝ) (hR : R ≤ 1) :
    ↥(Work.Serre.cellShellSet n ρ R) ≃ₜ
      ↥{z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) ρ R} where
  toFun := shellToFun n ι i ρ R hR
  invFun := shellInvFun n ι i ρ R hR
  left_inv := shellInvFun_shellToFun n ι i ρ R hR
  right_inv := shellToFun_shellInvFun n ι i ρ R hR
  continuous_toFun := continuous_shellToFun n ι i ρ R hR
  continuous_invFun := continuous_shellInvFun n ι i ρ R hR

/-! ## The homology of the shell -/

theorem shell_homology_top (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    Nonempty ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(Work.Serre.cellShellSet n ρ R))).homology (n+1) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := shellHomotopyEquiv n ρ R hρ hρR hR
  obtain ⟨e2⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv e (n+1)
  exact ⟨e2 ≪≫ Classical.choice (Work.Cohomology.sphereHomologyTop (n+1) (by omega))⟩

theorem shell_homology_zero (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(Work.Serre.cellShellSet n ρ R))).homology (n+2)) := by
  obtain ⟨e⟩ := shellHomotopyEquiv n ρ R hρ hρR hR
  exact Work.Cohomology.isZero_homology_of_homotopyEquiv e (n+2)
    (Work.Cohomology.sphereHomologyZero (n+1) (n+2) (by omega) (by omega) (by omega))

/-- **The homology of the trace of the shell in the `i`-th open cell.** -/
theorem shell_cell_homology_top (n : ℕ) (ι : Type) (i : ι) :
    Nonempty ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
          (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1})).homology (n+1)
      ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e1⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
    ((shellInCellHomeo n ι i (1/2) 1 (le_refl 1)).symm.toHomotopyEquiv) (n+1)
  obtain ⟨e2⟩ := shell_homology_top n (1/2) 1 (by norm_num) (by norm_num) (le_refl 1)
  exact ⟨e1 ≪≫ e2⟩

/-- **The `(n+2)`-nd homology of the trace of the shell in the `i`-th open cell vanishes.** -/
theorem shell_cell_homology_zero (n : ℕ) (ι : Type) (i : ι) :
    IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
          (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1})).homology (n+2)) :=
  Work.Cohomology.isZero_homology_of_homotopyEquiv
    ((shellInCellHomeo n ι i (1/2) 1 (le_refl 1)).symm.toHomotopyEquiv) (n+2)
    (shell_homology_zero n (1/2) 1 (by norm_num) (by norm_num) (le_refl 1))

/-! ## The open cell is contractible -/

theorem contractible_cellInterior (n : ℕ) (ι : Type) (i : ι) :
    ContractibleSpace ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) := by
  haveI h1 : ContractibleSpace ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin (n+2))) 1) :=
    Work.Cohomology.ball_contractible (n+2) 0 1 (by norm_num)
  haveI h2 : ContractibleSpace ↥(Work.RatHurewicz.cellInner n) :=
    Homeomorph.contractibleSpace (cellInnerHomeoBall n)
  exact Homeomorph.contractibleSpace (cellInteriorHomeo n ι i).symm

/-- **The per-cell computation**: the relative homology of the open `i`-th cell modulo the trace
of the shell is `ℤ` in degree `n+2`. -/
theorem cellShellImgHomology (n : ℕ) (ι : Type) (i : ι) :
    Nonempty ((Work.Cohomology.relChains
        (TopCat.of ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))
      {z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1}).homology (n+2)
      ≅ ModuleCat.of ℤ ℤ) := by
  haveI hcont : ContractibleSpace ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) :=
    contractible_cellInterior n ι i
  haveI h1 : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))).homology (n+2)) :=
    Work.Cohomology.homologyContractible (n+2) (by omega)
  haveI h2 : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))).homology (n+1)) :=
    Work.Cohomology.homologyContractible (n+1) (by omega)
  haveI hiso : IsIso (Work.Cohomology.hPairδ
      (TopCat.of ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))
      {z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1} (n+1)) :=
    Work.Cohomology.hPairδ_isIso _ _ (n+1) h1 h2
  obtain ⟨e⟩ := shell_cell_homology_top n ι i
  exact ⟨(asIso (Work.Cohomology.hPairδ
      (TopCat.of ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))
      {z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1} (n+1))) ≪≫ e⟩

end

end Work.Serre.Wedge
