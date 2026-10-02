import Mathlib
import Submission.Work.Thom.BundleIsoGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local data of `localThomOfComplexCover` restricts to the chart class

`(Work.Thom.localThomOfComplexCover hm Z)` is built from the Mayer--Vietoris witness
`Work.Thom.covWitness` of the finite cover of `B` by the charts of `Z`.  This module records that,
for a chart index `i` and a subset `W` of its base set, the restriction of the class to the piece
over `W` is the explicit chart class `Work.Thom.localThomOfChart ... i W`.

The proof follows the route recorded in `Submission/Work/Thom/BundleIsoGauge.lean`:

* `Work.Thom.localThomOfComplexCover_tau_eq` identifies the class with the cast of the witness along
  `Work.Thom.covHcover`, and `Work.Thom.pdCohMap_cast_source` transfers the restriction across the
  cast;
* `Work.Thom.covWitness_restrict` for the singleton `{Fintype.equivFin ι i}` identifies the
  restriction of the witness to the piece of that chart, and `Work.Thom.pdcz_pdCohMap_comp_apply`
  composes the two restrictions;
* the chart indexed by `Finset.Nonempty.choose` of the singleton is the chart `i`
  (`Work.Thom.localThomOfChart_eq_of_det_pos`, the determinant being that of the identity), and
  `Work.Thom.localThomOfChart_restrict` restricts from the chart piece to `W`.
-/

namespace Work.Thom

theorem localThomOfComplexCover_pdCohMap_subset {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    {W : Set B} (hW : W ⊆ (Work.Thom.realification Z).baseSet i) :
    (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' (Set.univ : Set B))
        ((Work.Thom.realification Z).proj ⁻¹' W)
        (Set.preimage_mono (fun _ _ => Set.mem_univ _)) (2 * m)).hom
        (Work.Thom.localThomOfComplexCover hm Z).τ
      = (Work.Thom.localThomOfChart (Work.Thom.realification Z) (2 * m) Work.Thom.covE i W hW).τ := by
  -- the class of `localThomOfComplexCover` is the witness over the cover, cast to `Set.univ`
  have hWcov : W ⊆ ⋃ k, Work.Thom.covU Z k :=
    fun x _ => (Work.Thom.covHcover Z).symm ▸ Set.mem_univ x
  have hcast : (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' (Set.univ : Set B))
        ((Work.Thom.realification Z).proj ⁻¹' W)
        (Set.preimage_mono (fun _ _ => Set.mem_univ _)) (2 * m)).hom
        ((Work.Thom.covHcover Z) ▸ Work.Thom.covWitness hm Z)
      = (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k))
        ((Work.Thom.realification Z).proj ⁻¹' W)
        (Set.preimage_mono hWcov) (2 * m)).hom
        (Work.Thom.covWitness hm Z) :=
    Work.Thom.pdCohMap_cast_source (Work.Thom.covZR Z) (Work.Thom.covHcover Z) hWcov
      (fun _ _ => Set.mem_univ _) (Work.Thom.covWitness hm Z)
  -- the singleton piece of the chart `i`
  let k0 : Fin (Fintype.card ι) := Fintype.equivFin ι i
  have hk0 : Work.Thom.covCC k0 = i := by
    simp only [k0, Work.Thom.covCC, Equiv.symm_apply_apply]
  have hS : ({k0} : Finset (Fin (Fintype.card ι))).Nonempty := Finset.singleton_nonempty k0
  have hchoose : hS.choose = k0 := Finset.mem_singleton.mp hS.choose_spec
  have hcc : Work.Thom.covCC hS.choose = i := by rw [hchoose, hk0]
  have hWfin : W ⊆ Work.Thom.finInter (Work.Thom.covU Z) {k0} := by
    intro x hx
    rw [Work.Thom.finInter_singleton]
    have h1 : x ∈ (Work.Thom.covZR Z).baseSet i := hW hx
    simpa only [Work.Thom.covU, hk0] using h1
  have hchart : Work.Thom.finInter (Work.Thom.covU Z) {k0} ⊆
      (Work.Thom.realification Z).baseSet i := by
    intro x hx
    rw [Work.Thom.finInter_singleton] at hx
    simpa only [Work.Thom.covU, Work.Thom.covZR, hk0] using hx
  -- the prescribed class of the witness over the singleton is the chart class of index `i`
  have hcC : Work.Thom.covC Z {k0} hS
      = (Work.Thom.localThomOfChart (Work.Thom.realification Z) (2 * m) Work.Thom.covE i
          (Work.Thom.finInter (Work.Thom.covU Z) {k0}) hchart).τ := by
    have hWint : Work.Thom.finInter (Work.Thom.covU Z) {k0} ⊆
        (Work.Thom.realification Z).baseSet i ∩
        (Work.Thom.realification Z).baseSet (Work.Thom.covCC hS.choose) :=
      fun x hx => ⟨hchart hx, Work.Thom.covHsub Z {k0} hS hx⟩
    exact Work.Thom.localThomOfChart_eq_of_det_pos (Work.Thom.realification Z) (2 * m) (by omega)
      Work.Thom.covE i (Work.Thom.covCC hS.choose) (Work.Thom.finInter (Work.Thom.covU Z) {k0})
      hchart (Work.Thom.covHsub Z {k0} hS) hWint
      (fun x => Work.Thom.det_realification_coordChange_pos Z i (Work.Thom.covCC hS.choose) hWint x)
  have hVU : (Work.Thom.realification Z).proj ⁻¹' W ⊆
      (Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0} :=
    Set.preimage_mono hWfin
  have hUW : (Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0} ⊆
      (Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k) :=
    Set.preimage_mono (Work.Thom.finInter_nonempty_subset_iUnion hS)
  have hwres : (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k))
        ((Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0})
        (Set.preimage_mono (Work.Thom.finInter_nonempty_subset_iUnion hS)) (2 * m)).hom
        (Work.Thom.covWitness hm Z) = Work.Thom.covC Z {k0} hS :=
    Work.Thom.covWitness_restrict hm Z {k0} hS
  -- the value of the restriction only depends on the sets, not on the inclusion proof
  have hcongr := Work.Thom.pdcz_pdCohMap_apply_congr
    (X := TopCat.of (Work.Thom.realification Z).TotalSpace)
    (A := Work.Thom.zeroComplement (Work.Thom.realification Z))
    (W := (Work.Thom.realification Z).proj ⁻¹' W)
    (U := (Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k))
    (Set.preimage_mono hWcov) (hVU.trans hUW) (2 * m) (Work.Thom.covWitness hm Z)
  have hcomp := Work.Thom.pdcz_pdCohMap_comp_apply
    (X := TopCat.of (Work.Thom.realification Z).TotalSpace)
    (A := Work.Thom.zeroComplement (Work.Thom.realification Z))
    (V := (Work.Thom.realification Z).proj ⁻¹' W)
    (U := (Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0})
    (W := (Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k))
    hVU hUW (2 * m) (Work.Thom.covWitness hm Z)
  have hfin := Work.Thom.localThomOfChart_restrict (Work.Thom.realification Z) (2 * m)
    Work.Thom.covE i W (Work.Thom.finInter (Work.Thom.covU Z) {k0}) hW hchart hWfin
  rw [Work.Thom.localThomOfComplexCover_tau_eq hm Z, hcast]
  calc (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k))
        ((Work.Thom.realification Z).proj ⁻¹' W) (Set.preimage_mono hWcov) (2 * m)).hom
        (Work.Thom.covWitness hm Z)
      = (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k))
        ((Work.Thom.realification Z).proj ⁻¹' W) (hVU.trans hUW) (2 * m)).hom
        (Work.Thom.covWitness hm Z) := hcongr
    _ = (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0})
        ((Work.Thom.realification Z).proj ⁻¹' W) hVU (2 * m)).hom
        ((Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' (⋃ k, Work.Thom.covU Z k))
        ((Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0}) hUW (2 * m)).hom
        (Work.Thom.covWitness hm Z)) := hcomp.symm
    _ = (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0})
        ((Work.Thom.realification Z).proj ⁻¹' W) hVU (2 * m)).hom
        (Work.Thom.covC Z {k0} hS) :=
      congrArg (fun c => (Work.Cohomology.pdCohMap
        (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0})
        ((Work.Thom.realification Z).proj ⁻¹' W) hVU (2 * m)).hom c) hwres
    _ = (Work.Cohomology.pdCohMap (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0})
        ((Work.Thom.realification Z).proj ⁻¹' W) hVU (2 * m)).hom
        (Work.Thom.localThomOfChart (Work.Thom.realification Z) (2 * m) Work.Thom.covE i
          (Work.Thom.finInter (Work.Thom.covU Z) {k0}) hchart).τ :=
      congrArg (fun c => (Work.Cohomology.pdCohMap
        (TopCat.of (Work.Thom.realification Z).TotalSpace)
        (Work.Thom.zeroComplement (Work.Thom.realification Z))
        ((Work.Thom.realification Z).proj ⁻¹' Work.Thom.finInter (Work.Thom.covU Z) {k0})
        ((Work.Thom.realification Z).proj ⁻¹' W) hVU (2 * m)).hom c) hcC
    _ = (Work.Thom.localThomOfChart (Work.Thom.realification Z) (2 * m) Work.Thom.covE i W hW).τ
        := hfin

end Work.Thom
