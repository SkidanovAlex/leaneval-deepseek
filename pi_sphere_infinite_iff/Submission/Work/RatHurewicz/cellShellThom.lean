import Mathlib
import Submission.Work.RatHurewicz.cellStepAt
import Submission.Work.RatHurewicz.thomCylAt_of_compress
import Submission.Work.Serre.cellImgQuarterSphereHomeo
import Submission.Work.Serre.thomCylAt_of_homeo
import Submission.Work.Serre.compressRel_cellShellImg
import Submission.Work.Serre.DiscPair.isClosed_cellMap_sphere
import Submission.Work.Serre.CWModelThomAux
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.StemsB.c2oddRangeTwo

set_option synthInstance.maxHeartbeats 400000

/-!
# The shell step of the cellular induction

`Work.Serre.ThomCylCellStepAlt` (the cellular step of the Serre computation) is assembled by
`Work.Serre.thomCylCellStep_of_shellsBall` from *local* inputs over the shell pieces
`cellImg i (cellShellSet (D-2) ρ R)` of an attached cell.  This file provides the shell step:

`Work.RatHurewicz.cellShellThom` — over the shell `{1/8 < ‖y‖ < 3/8}` of a `D`-cell, the Thom
condition `Work.Serre.ThomCylAt` holds as soon as the *sphere case* of the cellular step
`Work.RatHurewicz.SphThom (D - 2) r N` is known (the level `D - 1` statement, one dimension down).

The two ingredients are

* the **seed**: the `1/4`-sphere of the cell is homeomorphic to the model sphere `S^{D-1}`
  (`Work.Serre.cellImgQuarterSphereHomeo`), so the sphere case applies after transporting the
  fibration along the homeomorphism (`Work.Serre.thomCylAt_of_homeo`); this is
  `Work.RatHurewicz.thomCylAt_quarterSphere` below;
* the **compression**: the shell `{1/8 < ‖y‖ < 3/8}` is a thickening of that sphere — the
  radial deformation retraction `Work.Serre.CellShellCompress.shellHom` gives
  `Work.Serre.compressRel_cellShellImg`, the compressibility of the pair, in every dimension — and
  `Work.RatHurewicz.thomCylAt_of_compress` pushes the Thom condition up from the sphere to the
  shell.
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option linter.style.haveILetI false

/-- The `1/4`-sphere of the model cell lies in the shell `{1/8 < ‖·‖ < 3/8}`. -/
theorem quarterSet_subset_cellShellSet (n : ℕ) :
    Work.Serre.quarterSet n ⊆ Work.Serre.cellShellSet n (1 / 8) (3 / 8) := by
  intro y hy
  have hyn : ‖(y : CellVec n)‖ = 1 / 4 := hy
  rw [Work.Serre.mem_cellShellSet]
  exact ⟨by rw [hyn]; norm_num, by rw [hyn]; norm_num⟩

/-- **The sphere case of the cellular step gives the Thom condition over the `1/4`-sphere of an
attached cell.**  The `1/4`-sphere of the `i`-th cell is carried by the characteristic map to a
subspace homeomorphic to the model sphere `cellSphere n` (`Work.Serre.cellImgQuarterSphereHomeo`);
transporting the restricted fibration along that homeomorphism turns the sphere case
`Work.RatHurewicz.SphThom n r N` into the required statement, and
`Work.Serre.thomCylAt_of_homeo` transports the conclusion back. -/
theorem thomCylAt_quarterSphere {n : ℕ} {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) (i : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (hq : Work.StemsB.IsSerreFibration q) (r N : ℕ)
    (hpc : ∀ γ : attachCells n Γ ι f, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : attachCells n Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : attachCells n Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hST : SphThom n r N) :
    Work.Serre.ThomCylAt r N
      (Work.Serre.restrictFibre q (Work.Serre.cellImg (f := f) i (Work.Serre.quarterSet n))) := by
  classical
  set S : Set (attachCells n Γ ι f) :=
    Work.Serre.cellImg (f := f) i (Work.Serre.quarterSet n) with hS
  obtain ⟨e⟩ := Work.Serre.cellImgQuarterSphereHomeo n Γ ι f i
  set p : C(↥(q ⁻¹' S), cellSphere n) :=
    ((⟨e, e.continuous_toFun⟩ : C(↥S, cellSphere n)).comp (Work.Serre.restrictFibre q S)) with hp
  haveI hne : Nonempty (cellSphere n) :=
    ⟨⟨EuclideanSpace.single 0 (1 : ℝ), by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
        norm_num⟩⟩
  -- the fibre of the transported fibration is that of the ambient one
  have hfib : ∀ z : cellSphere n, Work.StemsB.fibre p z ≃ₜ Work.StemsB.fibre q (e.symm z) :=
    fun z => (Work.Serre.CWThom.fibreHomeo_comp_homeo e (Work.Serre.restrictFibre q S) z).trans
      (Work.Serre.CWThom.fibreHomeo_restrictFibre q S (e.symm z))
  -- the fibre data transports
  have hserre : Work.StemsB.IsSerreFibration p :=
    Work.Serre.CWThom.isSerreFibration_comp_homeo e (Work.Serre.isSerreFibration_restrictFibre q hq S)
  have hpc' : PathConnectedSpace (Work.StemsB.fibre p (Classical.arbitrary (cellSphere n))) :=
    Work.Serre.CWThom.pathConnectedSpace_of_homeo
      (hfib (Classical.arbitrary (cellSphere n))).symm (hpc _)
  have hvan' : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p (Classical.arbitrary (cellSphere n)))) t) := by
    intro t ht htr htN
    exact CategoryTheory.Limits.IsZero.of_iso (hvan _ t ht htr htN)
      (Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo
        (hfib (Classical.arbitrary (cellSphere n))) t))
  have hgen' : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre p (Classical.arbitrary (cellSphere n)))) r
      ≅ ModuleCat.of ℚ ℚ) :=
    ⟨(Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo
        (hfib (Classical.arbitrary (cellSphere n))) r)).trans (hgen _).some⟩
  -- the sphere case, and the transport back
  have hmain : Work.Serre.ThomCylAt r N p :=
    hST (↥(q ⁻¹' S)) p (Classical.arbitrary (cellSphere n)) hserre hpc' hvan' hgen'
  have hback : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S) :=
    Work.Serre.thomCylAt_of_homeo r N e p (Work.Serre.restrictFibre q S)
      (fun x => (e.symm_apply_apply (Work.Serre.restrictFibre q S x)).symm) hmain
  rw [hS] at hback
  exact hback

theorem cellShellThom (D : ℕ) (hD : 2 ≤ D) (r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (i : ι)
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hST : Work.RatHurewicz.SphThom (D - 2) r N) :
    Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.cellImg (f := f) i (Work.Serre.cellShellSet (D - 2) (1/8) (3/8)))) := by
  classical
  set S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f) :=
    Work.Serre.cellImg (f := f) i (Work.Serre.quarterSet (D - 2)) with hS
  set V : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f) :=
    Work.Serre.cellImg (f := f) i (Work.Serre.cellShellSet (D - 2) (1 / 8) (3 / 8)) with hV
  have hSV : S ⊆ V := by
    rw [hS, hV]
    exact Set.image_mono (quarterSet_subset_cellShellSet (D - 2))
  have hScl : IsClosed S := by
    rw [hS]
    exact Work.Serre.DiscPair.isClosed_cellMap_sphere (D - 2) Γ ι f i (ρ := 1 / 4) (by norm_num)
  have hVop : IsOpen V := by
    rw [hV]
    exact Work.RatHurewicz.isOpen_cellMap_image
      (Work.Serre.isOpen_cellShellSet (D - 2) (1 / 8) (3 / 8))
      (Work.Serre.cellShellSet_subset_cellInner (by norm_num))
  have hcomp : ∀ d, CompressRel ↥V
      {x : ↥V | (x : Work.RatHurewicz.attachCells (D - 2) Γ ι f) ∈ S} d := by
    intro d
    rw [hV, hS]
    exact Work.Serre.compressRel_cellShellImg (D - 2) Γ ι f (ρ := 1 / 8) (R := 3 / 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) i d
  have hseed : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S) := by
    rw [hS]
    exact thomCylAt_quarterSphere ι f i q hq r N hpc hvan hgen hST
  exact Work.RatHurewicz.thomCylAt_of_compress r N hr q hq S V hSV hScl hVop hcomp hseed

end Work.RatHurewicz
