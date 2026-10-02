import Mathlib
import Submission.Work.Thom.BundleIsoGauge
import Submission.Work.Thom.isoGauge_data
import Submission.Work.Thom.localThomOfComplexCover_pdCohMap_subset
import Submission.Work.Thom.localThom_eq_of_cover
import Submission.Work.Thom.step_natural
import Submission.Work.Thom.pdCohMap_finInter_eq_zero
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Isomorphism-invariance of the Euler class of the canonical Thom class

`Work.Thom.thomClassRank m hm Z` is the canonical (choice-free up to uniqueness-backed choices)
Thom class of the realification of a complex bundle `Z` of rank `m` over a base `B`
(`Submission/Work/Thom/thomClassOf.lean`).  This module proves that two **isomorphic** complex
bundles — presented by gluing data over *different* index types — have the **same** Euler class in
`H^{2m}(B;ℤ)`:

`(thomClassRank m hm Z).eulerClass = (thomClassRank m hm Z').eulerClass`.

This is the top-degree case of isomorphism-invariance of the Chern classes, and it is the input of
`Work.Thom.chernClass_BundleIso` (the missing tool of `README.md` ADDENDUM 23): the Euler class of
the canonical Thom class is independent of the presentation of the bundle.

## The proof

Write `Z_R`, `Z'_R` for the realifications and `n = 2*m`.

* The canonical local Thom data of `Z_R` over a chart is the explicit chart class
  `Work.Thom.localThomOfChart` (`Work.Thom.localThomOfComplexCover_pdCohMap_subset`), and the chart
  classes of `Z_R` and of `Z'_R` **correspond under the isomorphism** `e`
  (`Work.Thom.localThomOfChart_iso`, via the `ℂ`-linear gauge `Work.Thom.isoGauge` and the positive
  real determinant of `ℂ`-linear maps).
* Comparing the two canonical classes over the common refinement of the two chart covers
  (`Work.Thom.pairCover`) with `Work.Thom.localThom_eq_of_cover` gives the equality of the local
  data over `Set.univ` (`Work.Thom.localThomOfComplexCover_iso`).
* `Work.Thom.thomClassOf_iso` lifts this to the global canonical Thom class, exactly as in
  `Work.Thom.thomClassOf_comap` (the local data over `Set.univ` determines the Thom class,
  `Work.Thom.thomClassOf_spec`), and the Euler class is the pullback along the zero section
  (`Work.Thom.relCohMap_relToAbs_apply`).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ} {ι ι' : Type}

/-! ## The chart classes of two isomorphic bundles correspond -/

/-- **The explicit chart classes of `Z` and of `Z'` correspond under the isomorphism `e`**: the
pullback of the chart class of `realification Z'` over `W` along `pieceMapIso` is the chart class of
`realification Z` over `W`.

This is `Work.Thom.localThomOfChart_iso` proved through the gauge data
`Submission/Work/Thom/isoGauge_data.lean`: the two charts differ by the `ℂ`-linear gauge
`Work.Thom.isoGauge` (`isoGauge_compHom`), whose fibrewise real determinant is positive
(`det_isoGauge_pos`), so it fixes the model class `Work.Thom.Mpun`
(`Work.Thom.Mpun_gaugeEnd_invariant`). -/
theorem localThomOfChart_iso_via_gauge {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i') :
    (relCohMap (pieceMapIso Z Z' e W)
      (pieceZero (realification Z) W)
      (pieceZero (realification Z') W)
      (pieceMapIso_mem Z Z' e W) ℤ (2 * m)).hom
      (localThomOfChart (realification Z') (2 * m) covE i' W hWi').τ
      = (localThomOfChart (realification Z) (2 * m) covE i W hWi).τ := by
  have hc : Continuous (isoGauge Z Z' e i i' hWi hWi') :=
    continuous_isoGauge Z Z' e i i' hWi hWi'
  have hcomp := isoGauge_compHom Z Z' e i i' hWi hWi' hc
  have hdet : ∀ x, 0 < LinearMap.det ((isoGauge Z Z' e i i' hWi hWi' x).toLinearMap) :=
    fun x => det_isoGauge_pos Z Z' e i i' hWi hWi' x
  have hbijD : ∀ y, Function.Bijective ((isoGauge Z Z' e i i' hWi hWi') y) :=
    fun y => gaugeEnd_bijective_of_det_ne_zero _ (ne_of_gt (hdet y))
  have hmemG : ∀ y ∈ Punct ↥W (2 * m),
      gaugeEnd (isoGauge Z Z' e i i' hWi hWi') hc y ∈ Punct ↥W (2 * m) :=
    gaugeEnd_mem (isoGauge Z Z' e i i' hWi hWi') hc hbijD
  have hgf1 : ∀ p ∈ pieceZero (realification Z) W,
      ((chartHomeo (realification Z') (2 * m) covE i' W hWi' :
        C(↥((realification Z').proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
        (pieceMapIso Z Z' e W)) p ∈ Punct ↥W (2 * m) :=
    fun p hp => chartHomeo_mem (realification Z') (2 * m) covE i' W hWi'
      (pieceMapIso Z Z' e W p) (pieceMapIso_mem Z Z' e W p hp)
  have hgf2 : ∀ p ∈ pieceZero (realification Z) W,
      ((gaugeEnd (isoGauge Z Z' e i i' hWi hWi') hc).comp
        (chartHomeo (realification Z) (2 * m) covE i W hWi :
          C(↥((realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m))))) p
        ∈ Punct ↥W (2 * m) :=
    fun p hp => hmemG _ (chartHomeo_mem (realification Z) (2 * m) covE i W hWi p hp)
  rw [localThomOfChart_tau, localThomOfChart_tau]
  erw [relCohMap_compA_apply (pieceZero (realification Z) W) (pieceZero (realification Z') W)
    (Punct ↥W (2 * m)) (pieceMapIso Z Z' e W)
    (chartHomeo (realification Z') (2 * m) covE i' W hWi' :
      C(↥((realification Z').proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m))))
    (pieceMapIso_mem Z Z' e W)
    (chartHomeo_mem (realification Z') (2 * m) covE i' W hWi') hgf1 ℤ (2 * m) (Mpun (2 * m) ↥W)]
  erw [relCohMap_congrA (pieceZero (realification Z) W) (Punct ↥W (2 * m)) hcomp hgf1 hgf2
    ℤ (2 * m)]
  erw [← relCohMap_compA_apply (pieceZero (realification Z) W) (Punct ↥W (2 * m))
    (Punct ↥W (2 * m)) (chartHomeo (realification Z) (2 * m) covE i W hWi :
      C(↥((realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m))))
    (gaugeEnd (isoGauge Z Z' e i i' hWi hWi') hc)
    (chartHomeo_mem (realification Z) (2 * m) covE i W hWi) hmemG hgf2
    ℤ (2 * m) (Mpun (2 * m) ↥W)]
  erw [Mpun_gaugeEnd_invariant (2 * m) (by omega) (isoGauge Z Z' e i i' hWi hWi') hc hdet]

/-- The cover of `B` by the pieces `baseSet i ∩ baseSet' i'` of two bundles. -/
def pairCover (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') : ι × ι' → Set B :=
  fun p => (realification Z).baseSet p.1 ∩ (realification Z').baseSet p.2

@[simp] theorem pairCover_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (p : ι × ι') :
    pairCover Z Z' p = (realification Z).baseSet p.1 ∩ (realification Z').baseSet p.2 := rfl

theorem localThomOfComplexCover_iso {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') :
    (relCohMap (pieceMapIso Z Z' e Set.univ) (pieceZero (realification Z) Set.univ)
      (pieceZero (realification Z') Set.univ) (pieceMapIso_mem Z Z' e Set.univ) ℤ (2 * m)).hom
      (localThomOfComplexCover hm Z').τ
      = (localThomOfComplexCover hm Z).τ := by
  classical
  have hVopen : ∀ p : ι × ι', IsOpen (pairCover Z Z' p) := fun p =>
    ((realification Z).isOpen_baseSet p.1).inter ((realification Z').isOpen_baseSet p.2)
  have hVsub : ∀ p : ι × ι', pairCover Z Z' p ⊆ (Set.univ : Set B) := fun _ => Set.subset_univ _
  have hcov : (Set.univ : Set B) ⊆ ⋃ p ∈ (Finset.univ : Finset (ι × ι')), pairCover Z Z' p := by
    intro x _
    refine Set.mem_iUnion.mpr ⟨(Z.indexAt x, Z'.indexAt x), ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨by rw [realification_baseSet]; exact Z.mem_baseSet_at x,
      by rw [realification_baseSet]; exact Z'.mem_baseSet_at x⟩
  refine localThom_eq_of_cover (realification Z) (2 * m) (P := Set.univ) (pairCover Z Z')
    hVopen hVsub Finset.univ hcov
    ((localThomOfComplexCover hm Z).τ)
    ((relCohMap (pieceMapIso Z Z' e Set.univ) (pieceZero (realification Z) Set.univ)
      (pieceZero (realification Z') Set.univ) (pieceMapIso_mem Z Z' e Set.univ) ℤ (2 * m)).hom
      (localThomOfComplexCover hm Z').τ)
    ((localThomOfComplexCover hm Z).isThom 0) ?_ ?_
  · intro p _
    have hsub : pairCover Z Z' p ⊆ (realification Z).baseSet p.1 := by
      rw [pairCover_apply]; exact Set.inter_subset_left
    have hchart := (localThomOfChart (realification Z) (2 * m) covE p.1
      (pairCover Z Z' p) hsub).isThom 0
    have hspec := localThomOfComplexCover_pdCohMap_subset hm Z p.1 (W := pairCover Z Z' p) hsub
    rw [pdcz_pdCohMap_apply_congr (TopCat.of (realification Z).TotalSpace)
      (zeroComplement (realification Z)) (Set.preimage_mono (hVsub p))
      (Set.preimage_mono (fun _ _ => Set.mem_univ _)) (2 * m)
      ((localThomOfComplexCover hm Z).τ)]
    rw [hspec]
    exact hchart.1
  · intro p _
    have hsub : pairCover Z Z' p ⊆ (realification Z).baseSet p.1 := by
      rw [pairCover_apply]; exact Set.inter_subset_left
    have hsub' : pairCover Z Z' p ⊆ (realification Z').baseSet p.2 := by
      rw [pairCover_apply]; exact Set.inter_subset_right
    have hZ : (Work.Cohomology.pdCohMap (TopCat.of (realification Z).TotalSpace)
        (zeroComplement (realification Z)) ((realification Z).proj ⁻¹' (Set.univ : Set B))
        ((realification Z).proj ⁻¹' (pairCover Z Z' p)) (Set.preimage_mono (hVsub p)) (2 * m)).hom
        (localThomOfComplexCover hm Z).τ
        = (localThomOfChart (realification Z) (2 * m) covE p.1 (pairCover Z Z' p) hsub).τ := by
      rw [pdcz_pdCohMap_apply_congr (TopCat.of (realification Z).TotalSpace)
        (zeroComplement (realification Z)) (Set.preimage_mono (hVsub p))
        (Set.preimage_mono (fun _ _ => Set.mem_univ _)) (2 * m)
        ((localThomOfComplexCover hm Z).τ)]
      exact localThomOfComplexCover_pdCohMap_subset hm Z p.1 (W := pairCover Z Z' p) hsub
    have hZ' : (Work.Cohomology.pdCohMap (TopCat.of (realification Z').TotalSpace)
        (zeroComplement (realification Z')) ((realification Z').proj ⁻¹' (Set.univ : Set B))
        ((realification Z').proj ⁻¹' (pairCover Z Z' p)) (Set.preimage_mono (hVsub p)) (2 * m)).hom
        (localThomOfComplexCover hm Z').τ
        = (localThomOfChart (realification Z') (2 * m) covE p.2 (pairCover Z Z' p) hsub').τ := by
      rw [pdcz_pdCohMap_apply_congr (TopCat.of (realification Z').TotalSpace)
        (zeroComplement (realification Z')) (Set.preimage_mono (hVsub p))
        (Set.preimage_mono (fun _ _ => Set.mem_univ _)) (2 * m)
        ((localThomOfComplexCover hm Z').τ)]
      exact localThomOfComplexCover_pdCohMap_subset hm Z' p.2 (W := pairCover Z Z' p) hsub'
    have hmem1 : ∀ x ∈ pieceZero (realification Z) (pairCover Z Z' p),
        (pieceMapIso Z Z' e Set.univ) (pieceIncl (realification Z) (pairCover Z Z' p) Set.univ
          (hVsub p) x) ∈ pieceZero (realification Z') Set.univ :=
      fun x hx => pieceMapIso_mem Z Z' e Set.univ _
        (pieceIncl_mem (realification Z) (pairCover Z Z' p) Set.univ (hVsub p) x hx)
    have hmem2 : ∀ x ∈ pieceZero (realification Z) (pairCover Z Z' p),
        (pieceIncl (realification Z') (pairCover Z Z' p) Set.univ (hVsub p))
          (pieceMapIso Z Z' e (pairCover Z Z' p) x) ∈ pieceZero (realification Z') Set.univ :=
      fun x hx => pieceIncl_mem (realification Z') (pairCover Z Z' p) Set.univ (hVsub p) _
        (pieceMapIso_mem Z Z' e (pairCover Z Z' p) x hx)
    have hcompmap : (pieceMapIso Z Z' e Set.univ).comp
          (pieceIncl (realification Z) (pairCover Z Z' p) Set.univ (hVsub p))
        = (pieceIncl (realification Z') (pairCover Z Z' p) Set.univ (hVsub p)).comp
            (pieceMapIso Z Z' e (pairCover Z Z' p)) := by
      apply ContinuousMap.ext; intro q; apply Subtype.ext
      simp only [ContinuousMap.comp_apply, pieceIncl_apply, pieceMapIso_apply]
    rw [hZ]
    rw [pdCohMap_eq_relCohMap (realification Z) (pairCover Z Z' p) Set.univ (hVsub p) (2 * m)]
    erw [relCohMap_compA_apply (pieceZero (realification Z) (pairCover Z Z' p))
      (pieceZero (realification Z) Set.univ) (pieceZero (realification Z') Set.univ)
      (pieceIncl (realification Z) (pairCover Z Z' p) Set.univ (hVsub p))
      (pieceMapIso Z Z' e Set.univ)
      (pieceIncl_mem (realification Z) (pairCover Z Z' p) Set.univ (hVsub p))
      (pieceMapIso_mem Z Z' e Set.univ) hmem1 ℤ (2 * m)
      ((localThomOfComplexCover hm Z').τ)]
    rw [relCohMap_congrA (pieceZero (realification Z) (pairCover Z Z' p))
      (pieceZero (realification Z') Set.univ) hcompmap hmem1 hmem2 ℤ (2 * m)]
    rw [← relCohMap_compA_apply (pieceZero (realification Z) (pairCover Z Z' p))
      (pieceZero (realification Z') (pairCover Z Z' p)) (pieceZero (realification Z') Set.univ)
      (pieceMapIso Z Z' e (pairCover Z Z' p))
      (pieceIncl (realification Z') (pairCover Z Z' p) Set.univ (hVsub p))
      (pieceMapIso_mem Z Z' e (pairCover Z Z' p))
      (pieceIncl_mem (realification Z') (pairCover Z Z' p) Set.univ (hVsub p)) hmem2 ℤ (2 * m)
      ((localThomOfComplexCover hm Z').τ)]
    erw [← pdCohMap_eq_relCohMap (realification Z') (pairCover Z Z' p) Set.univ (hVsub p) (2 * m)]
    erw [hZ']
    rw [localThomOfChart_iso_via_gauge hm Z Z' e p.1 p.2 hsub hsub']


theorem thomClassOf_iso {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') :
    (relCohMap (totalMapIso Z Z' e) (zeroComplement (realification Z))
      (zeroComplement (realification Z')) (fun _ hp => e.hom_ne_zero hp) ℤ (2 * m)).hom
      (thomClassOf hm Z').τ
      = (thomClassOf hm Z).τ := by
  classical
  let pzZ : Set ↥((realification Z).proj ⁻¹' (Set.univ : Set B)) :=
    pieceZero (realification Z) (Set.univ : Set B)
  let pzZ' : Set ↥((realification Z').proj ⁻¹' (Set.univ : Set B)) :=
    pieceZero (realification Z') (Set.univ : Set B)
  let univZ : C(↥((realification Z).proj ⁻¹' (Set.univ : Set B)), (realification Z).TotalSpace) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let univZ' : C(↥((realification Z').proj ⁻¹' (Set.univ : Set B)),
    (realification Z').TotalSpace) := ⟨Subtype.val, continuous_subtype_val⟩
  have hmemT : ∀ x ∈ zeroComplement (realification Z),
      (totalMapIso Z Z' e) x ∈ zeroComplement (realification Z') :=
    fun _ hp => e.hom_ne_zero hp
  have hmemZ : ∀ x ∈ pzZ, univZ x ∈ zeroComplement (realification Z) := fun _ hy => hy
  have hmemZ' : ∀ x ∈ pzZ', univZ' x ∈ zeroComplement (realification Z') := fun _ hy => hy
  have hgf : ∀ x ∈ pzZ, ((totalMapIso Z Z' e).comp univZ) x ∈ zeroComplement (realification Z') :=
    fun x hx => hmemT (univZ x) (hmemZ x hx)
  have hgf' : ∀ x ∈ pzZ, (univZ'.comp (pieceMapIso Z Z' e Set.univ)) x
      ∈ zeroComplement (realification Z') :=
    fun x hx => hmemZ' ((pieceMapIso Z Z' e Set.univ) x) (pieceMapIso_mem Z Z' e Set.univ x hx)
  have hspecZ : (relCohMap univZ pzZ (zeroComplement (realification Z)) hmemZ ℤ (2*m)).hom
      (thomClassOf hm Z).τ = (localThomOfComplexCover hm Z).τ := thomClassOf_spec (hm := hm) Z
  have hspecZ' : (relCohMap univZ' pzZ' (zeroComplement (realification Z')) hmemZ' ℤ (2*m)).hom
      (thomClassOf hm Z').τ = (localThomOfComplexCover hm Z').τ := thomClassOf_spec (hm := hm) Z'
  have hanat : (relCohMap (pieceMapIso Z Z' e Set.univ) pzZ pzZ'
      (pieceMapIso_mem Z Z' e Set.univ) ℤ (2*m)).hom (localThomOfComplexCover hm Z').τ
      = (localThomOfComplexCover hm Z).τ := localThomOfComplexCover_iso hm Z Z' e
  have hcompmap : (totalMapIso Z Z' e).comp univZ
      = univZ'.comp (pieceMapIso Z Z' e Set.univ) := by
    simpa only [univZ, univZ'] using totalMapIso_comp_subtype Z Z' e
  let eZ : ↥((realification Z).proj ⁻¹' (Set.univ : Set B)) ≃ₜ (realification Z).TotalSpace :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, Set.mem_univ p⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun p => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun _ => trivial) }
  have hbij := bijective_relCohMap_of_homeomorphA pzZ (zeroComplement (realification Z)) eZ
    (fun y => Iff.rfl) ℤ (2 * m)
  change (relCohMap (totalMapIso Z Z' e) (zeroComplement (realification Z))
    (zeroComplement (realification Z')) hmemT ℤ (2 * m)).hom (thomClassOf hm Z').τ
    = (thomClassOf hm Z).τ
  refine hbij.1 ?_
  calc (relCohMap univZ pzZ (zeroComplement (realification Z)) hmemZ ℤ (2*m)).hom
        ((relCohMap (totalMapIso Z Z' e) (zeroComplement (realification Z))
          (zeroComplement (realification Z')) hmemT ℤ (2*m)).hom (thomClassOf hm Z').τ)
      = (relCohMap ((totalMapIso Z Z' e).comp univZ) pzZ (zeroComplement (realification Z'))
          hgf ℤ (2*m)).hom (thomClassOf hm Z').τ :=
        relCohMap_compA_apply pzZ (zeroComplement (realification Z))
          (zeroComplement (realification Z')) univZ (totalMapIso Z Z' e) hmemZ hmemT
          hgf ℤ (2*m) (thomClassOf hm Z').τ
    _ = (relCohMap (univZ'.comp (pieceMapIso Z Z' e Set.univ)) pzZ
          (zeroComplement (realification Z')) hgf' ℤ (2*m)).hom
          (thomClassOf hm Z').τ :=
        congrArg (fun φ => φ.hom (thomClassOf hm Z').τ)
          (relCohMap_congrA pzZ (zeroComplement (realification Z')) hcompmap hgf hgf' ℤ (2*m))
    _ = (relCohMap (pieceMapIso Z Z' e Set.univ) pzZ pzZ'
          (pieceMapIso_mem Z Z' e Set.univ) ℤ (2*m)).hom
          ((relCohMap univZ' pzZ' (zeroComplement (realification Z')) hmemZ' ℤ (2*m)).hom
            (thomClassOf hm Z').τ) :=
        (relCohMap_compA_apply pzZ pzZ' (zeroComplement (realification Z'))
          (pieceMapIso Z Z' e Set.univ) univZ' (pieceMapIso_mem Z Z' e Set.univ)
          hmemZ' hgf' ℤ (2*m) (thomClassOf hm Z').τ).symm
    _ = (relCohMap (pieceMapIso Z Z' e Set.univ) pzZ pzZ'
          (pieceMapIso_mem Z Z' e Set.univ) ℤ (2*m)).hom (localThomOfComplexCover hm Z').τ :=
        congrArg (fun z => (relCohMap (pieceMapIso Z Z' e Set.univ) pzZ pzZ'
          (pieceMapIso_mem Z Z' e Set.univ) ℤ (2*m)).hom z) hspecZ'
    _ = (relCohMap univZ pzZ (zeroComplement (realification Z)) hmemZ ℤ (2*m)).hom
          (thomClassOf hm Z).τ := hanat.trans hspecZ.symm

theorem thomClassRank_eulerClass_iso {m : ℕ} {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : Work.Thom.BundleIso Z Z') (hm : 1 ≤ m) :
    (Work.Thom.thomClassRank m hm Z).eulerClass = (Work.Thom.thomClassRank m hm Z').eulerClass := by
  have hmap : (totalMapIso Z Z' e).comp (zeroSection (realification Z))
      = zeroSection (realification Z') := by
    apply ContinuousMap.ext; intro b
    simp only [ContinuousMap.comp_apply, totalMapIso_apply, zeroSection_apply, BundleIso.hom_zero]
  have h := thomClassOf_iso hm Z Z' e
  show (CohMap (zeroSection (realification Z)) ℤ (2*m)).hom
        ((openToAbs (realification Z) (2*m)).hom (thomClassOf hm Z).τ)
      = (CohMap (zeroSection (realification Z')) ℤ (2*m)).hom
        ((openToAbs (realification Z') (2*m)).hom (thomClassOf hm Z').τ)
  rw [← h]
  rw [relCohMap_relToAbs_apply (totalMapIso Z Z' e) (zeroComplement (realification Z))
    (zeroComplement (realification Z')) (fun _ hp => e.hom_ne_zero hp) ℤ (2*m)
    (thomClassOf hm Z').τ]
  rw [CohMap_comp_apply (zeroSection (realification Z)) (totalMapIso Z Z' e) ℤ (2*m) _]
  rw [hmap]


end

end Work.Thom
