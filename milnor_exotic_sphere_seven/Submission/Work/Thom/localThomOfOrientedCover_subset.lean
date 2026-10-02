import Mathlib
import Submission.Work.Thom.RealGaugeDefs
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.thomClass_of_finite_cover
import Submission.Work.Thom.pdCohMap_finInter_eq_zero
import Submission.Work.Thom.FiniteCover
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-!
# The local data of `localThomOfOrientedCover` restricts to the chart class

`Work.Thom.localThomOfOrientedCover hn Z hori` is built from the Mayer--Vietoris witness
`Work.Thom.oriWitness` of the finite cover of `B` by the chart sets `Z.baseSet i`.  This module
records that, for a chart index `i` and a subset `W` of its base set, the restriction of that class
to the piece over `W` is the explicit chart class `Work.Thom.localThomOfChart ... i W`.

The proof is the real companion of `Work.Thom.localThomOfComplexCover_pdCohMap_subset`:

* `Work.Thom.localThomOfOrientedCover_tau_eq` identifies the class with the cast of the witness
  along the cover equality `Work.Thom.oriHcover`, and `Work.Thom.pdCohMap_cast_source` transfers
  the restriction across the cast;
* `Work.Thom.oriWitness_restrict` for the singleton `{Fintype.equivFin ι i}` identifies the
  restriction of the witness to the piece of that chart, and `Work.Thom.pdcz_pdCohMap_comp_apply`
  composes the two restrictions;
* the chart indexed by `Finset.Nonempty.choose` of the singleton is the chart `i`
  (`Work.Thom.localThomOfChart_eq_of_det_pos`, the determinant being controlled by the orientation
  hypothesis `hori`), and `Work.Thom.localThomOfChart_restrict` restricts from the chart piece to
  `W`.
-/

theorem localThomOfOrientedCover_subset {n : ℕ} (hn : 1 ≤ n) {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι)
    (hori : ∀ (i j : ι) (x : ↥(Z.baseSet i ∩ Z.baseSet j)),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap))
    (i : ι) {W : Set B} (hW : W ⊆ Z.baseSet i) :
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Set.univ : Set B)) (Z.proj ⁻¹' W)
        (Set.preimage_mono (fun _ _ => Set.mem_univ _)) n).hom
        (Work.Thom.localThomOfOrientedCover hn Z hori).τ
      = (Work.Thom.localThomOfChart Z n (Work.Thom.oriE n) i W hW).τ := by
  -- the witness lives over the union of the chart cover, which is all of `B`
  have hWcov : W ⊆ ⋃ k, Work.Thom.oriU Z k :=
    fun x _ => (Work.Thom.oriHcover Z).symm ▸ Set.mem_univ x
  have hcast : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Set.univ : Set B))
        (Z.proj ⁻¹' W)
        (Set.preimage_mono (fun _ _ => Set.mem_univ _)) n).hom
        ((Work.Thom.oriHcover Z) ▸ Work.Thom.oriWitness hn Z hori)
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k))
        (Z.proj ⁻¹' W)
        (Set.preimage_mono hWcov) n).hom
        (Work.Thom.oriWitness hn Z hori) :=
    Work.Thom.pdCohMap_cast_source Z (Work.Thom.oriHcover Z) hWcov
      (fun _ _ => Set.mem_univ _) (Work.Thom.oriWitness hn Z hori)
  -- the singleton piece of the chart `i`
  let k0 : Fin (Fintype.card ι) := Fintype.equivFin ι i
  have hk0 : Work.Thom.oriCC k0 = i := by
    simp only [k0, Work.Thom.oriCC, Equiv.symm_apply_apply]
  have hS : ({k0} : Finset (Fin (Fintype.card ι))).Nonempty := Finset.singleton_nonempty k0
  have hchoose : hS.choose = k0 := Finset.mem_singleton.mp hS.choose_spec
  have hWfin : W ⊆ Work.Thom.finInter (Work.Thom.oriU Z) {k0} := by
    intro x hx
    rw [Work.Thom.finInter_singleton]
    have h1 : x ∈ Z.baseSet i := hW hx
    simpa only [Work.Thom.oriU, hk0] using h1
  have hchart : Work.Thom.finInter (Work.Thom.oriU Z) {k0} ⊆ Z.baseSet i := by
    intro x hx
    rw [Work.Thom.finInter_singleton] at hx
    simpa only [Work.Thom.oriU, hk0] using hx
  -- the prescribed class of the witness over the singleton is the chart class of index `i`
  have hcC : Work.Thom.oriC Z {k0} hS
      = (Work.Thom.localThomOfChart Z n (Work.Thom.oriE n) i
          (Work.Thom.finInter (Work.Thom.oriU Z) {k0}) hchart).τ := by
    have hWint : Work.Thom.finInter (Work.Thom.oriU Z) {k0} ⊆
        Z.baseSet i ∩ Z.baseSet (Work.Thom.oriCC hS.choose) :=
      fun x hx => ⟨hchart hx, Work.Thom.oriHsub Z {k0} hS hx⟩
    exact Work.Thom.localThomOfChart_eq_of_det_pos Z n hn (Work.Thom.oriE n) i
      (Work.Thom.oriCC hS.choose) (Work.Thom.finInter (Work.Thom.oriU Z) {k0})
      hchart (Work.Thom.oriHsub Z {k0} hS) hWint
      (fun x => hori i (Work.Thom.oriCC hS.choose) ⟨(x : B), hWint x.2⟩)
  have hVU : Z.proj ⁻¹' W ⊆ Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0} :=
    Set.preimage_mono hWfin
  have hUW : Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0} ⊆
      Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k) :=
    Set.preimage_mono (Work.Thom.finInter_nonempty_subset_iUnion hS)
  have hwres : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k))
        (Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0})
        (Set.preimage_mono (Work.Thom.finInter_nonempty_subset_iUnion hS)) n).hom
        (Work.Thom.oriWitness hn Z hori) = Work.Thom.oriC Z {k0} hS :=
    Work.Thom.oriWitness_restrict hn Z hori {k0} hS
  -- the value of the restriction only depends on the sets, not on the inclusion proof
  have hcongr := Work.Thom.pdcz_pdCohMap_apply_congr
    (X := TopCat.of Z.TotalSpace)
    (A := Work.Thom.zeroComplement Z)
    (W := Z.proj ⁻¹' W)
    (U := Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k))
    (Set.preimage_mono hWcov) (hVU.trans hUW) n (Work.Thom.oriWitness hn Z hori)
  have hcomp := Work.Thom.pdcz_pdCohMap_comp_apply
    (X := TopCat.of Z.TotalSpace)
    (A := Work.Thom.zeroComplement Z)
    (V := Z.proj ⁻¹' W)
    (U := Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0})
    (W := Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k))
    hVU hUW n (Work.Thom.oriWitness hn Z hori)
  have hfin := Work.Thom.localThomOfChart_restrict Z n (Work.Thom.oriE n) i W
    (Work.Thom.finInter (Work.Thom.oriU Z) {k0}) hW hchart hWfin
  rw [Work.Thom.localThomOfOrientedCover_tau_eq hn Z hori, hcast]
  calc (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k))
        (Z.proj ⁻¹' W) (Set.preimage_mono hWcov) n).hom
        (Work.Thom.oriWitness hn Z hori)
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k))
        (Z.proj ⁻¹' W) (hVU.trans hUW) n).hom
        (Work.Thom.oriWitness hn Z hori) := hcongr
    _ = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0})
        (Z.proj ⁻¹' W) hVU n).hom
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (⋃ k, Work.Thom.oriU Z k))
        (Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0}) hUW n).hom
        (Work.Thom.oriWitness hn Z hori)) := hcomp.symm
    _ = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0})
        (Z.proj ⁻¹' W) hVU n).hom
        (Work.Thom.oriC Z {k0} hS) :=
      congrArg (fun c => (Work.Cohomology.pdCohMap
        (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0})
        (Z.proj ⁻¹' W) hVU n).hom c) hwres
    _ = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0})
        (Z.proj ⁻¹' W) hVU n).hom
        (Work.Thom.localThomOfChart Z n (Work.Thom.oriE n) i
          (Work.Thom.finInter (Work.Thom.oriU Z) {k0}) hchart).τ :=
      congrArg (fun c => (Work.Cohomology.pdCohMap
        (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' Work.Thom.finInter (Work.Thom.oriU Z) {k0})
        (Z.proj ⁻¹' W) hVU n).hom c) hcC
    _ = (Work.Thom.localThomOfChart Z n (Work.Thom.oriE n) i W hW).τ := hfin

end

end Work.Thom
