import Mathlib
import Submission.Work.Gen.eulerClass_neg_of_realIso
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.thomClassRank_eulerClass_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Whitney

/-!
Mirror of `Submission/Work/Gen/eulerClass_neg_of_realIso.lean` with the sign of the fibrewise
determinant of the real isomorphism reversed.  The only inputs that change are
`Work.Thom.Mpun_gaugeEnd_invariant` (in place of `Work.Gen.Mpun_gaugeEnd_neg`) -- an
orientation-*preserving* gauge fixes the model class `Mpun` -- and the determinant bookkeeping
`det_realIsoGauge_pos` below.
-/

noncomputable section

open Work.Thom Work.TangentClasses Work.Gen

variable {B : Type} [TopologicalSpace B] {m : ℕ} {ι ι' : Type}

/-- **The real determinant of the gauge has the sign of `det (e.hom x)`**: for an everywhere
positive fibrewise determinant the gauge is orientation preserving. -/
theorem det_realIsoGauge_pos
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z')) (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i')
    (hdet : ∀ b : B, 0 < LinearMap.det (e.hom b)) (x : ↥W) :
    LinearMap.det ((realIsoGauge Z Z' e i i' hWi hWi' x).toLinearMap) > 0 := by
  let Cc : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    ((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)).toLinearMap
  let Cc' : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    ((realification Z').coordChange ((realification Z').indexAt (x : B)) i' (x : B)).toLinearMap
  let Ex : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) := e.hom (x : B)
  let Bm : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) := Cc'.comp (Ex.comp Cc)
  have hlin : (realIsoGauge Z Z' e i i' hWi hWi' x).toLinearMap
      = (covE (m := m)).toLinearEquiv.conj Bm := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply]
    change (realIsoGauge Z Z' e i i' hWi hWi' x) v
      = (covE (m := m)) (Bm ((covE (m := m)).symm v))
    rw [realIsoGauge_apply]
    rfl
  have hdetg : LinearMap.det ((realIsoGauge Z Z' e i i' hWi hWi' x).toLinearMap)
      = LinearMap.det Bm := by
    rw [hlin]
    exact LinearMap.det_conj Bm ((covE (m := m)).toLinearEquiv)
  rw [hdetg]
  have hC : 0 < LinearMap.det Cc := by
    have h1 : Cc = (Z.coordChange i (Z.indexAt (x : B)) (x : B)).restrictScalars ℝ := by
      show ((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)).toLinearMap
        = _
      rw [realification_indexAt]
      exact realification_coordChange_toLinearMap Z i (Z.indexAt (x : B)) (x : B)
    rw [h1]
    refine det_restrictScalars_pos ?_
    rw [realification_baseSet] at hWi
    exact coordChange_bijective Z i (Z.indexAt (x : B)) ⟨hWi x.2, Z.mem_baseSet_at _⟩
  have hC' : 0 < LinearMap.det Cc' := by
    have h1 : Cc'
        = (Z'.coordChange (Z'.indexAt (x : B)) i' (x : B)).restrictScalars ℝ := by
      show ((realification Z').coordChange ((realification Z').indexAt (x : B)) i'
        (x : B)).toLinearMap = _
      rw [realification_indexAt]
      exact realification_coordChange_toLinearMap Z' (Z'.indexAt (x : B)) i' (x : B)
    rw [h1]
    refine det_restrictScalars_pos ?_
    rw [realification_baseSet] at hWi'
    exact coordChange_bijective Z' (Z'.indexAt (x : B)) i' ⟨Z'.mem_baseSet_at _, hWi' x.2⟩
  have hE : 0 < LinearMap.det Ex := hdet (x : B)
  have hBm : LinearMap.det Bm
      = LinearMap.det Cc' * LinearMap.det Ex * LinearMap.det Cc := by
    show LinearMap.det (Cc'.comp (Ex.comp Cc)) = _
    rw [LinearMap.det_comp, LinearMap.det_comp]
    ring
  rw [hBm]
  exact mul_pos (mul_pos hC' hE) hC


/-- **The chart classes of two realifications corresponding to an orientation-preserving
isomorphism agree.**  If `e : realification Z ≅ realification Z'` is a real isomorphism of the
realifications with everywhere positive fibrewise determinant, then the pullback of the chart class
of `realification Z'` over `W` along `realPieceMap` is the chart class of `realification Z` over
`W`.

This is the orientation-preserving companion of `Work.Gen.localThomOfChart_realIso_neg`: the two
charts differ by the gauge `Work.Gen.realIsoGauge`, which is here orientation preserving
(`Work.Gen.det_realIsoGauge_pos`), and an orientation-preserving gauge fixes the model class
`Work.Thom.Mpun` (`Work.Thom.Mpun_gaugeEnd_invariant`). -/
theorem localThomOfChart_realIso_pos {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z')) (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i')
    (hdet : ∀ b : B, 0 < LinearMap.det (e.hom b)) :
    (relCohMap (realPieceMap (realification Z) (realification Z') e W)
      (pieceZero (realification Z) W)
      (pieceZero (realification Z') W)
      (realPieceMap_mem (realification Z) (realification Z') e W) ℤ (2 * m)).hom
      (localThomOfChart (realification Z') (2 * m) covE i' W hWi').τ
      = (localThomOfChart (realification Z) (2 * m) covE i W hWi).τ := by
  have hc : Continuous (realIsoGauge Z Z' e i i' hWi hWi') :=
    continuous_realIsoGauge Z Z' e i i' hWi hWi'
  have hcomp := realIsoGauge_compHom Z Z' e i i' hWi hWi' hc
  have hdet' : ∀ x, 0 < LinearMap.det ((realIsoGauge Z Z' e i i' hWi hWi' x).toLinearMap) :=
    fun x => det_realIsoGauge_pos Z Z' e i i' hWi hWi' hdet x
  have hbijD : ∀ y, Function.Bijective ((realIsoGauge Z Z' e i i' hWi hWi') y) :=
    fun y => gaugeEnd_bijective_of_det_ne_zero _ (ne_of_gt (hdet' y))
  have hmemG : ∀ y ∈ Punct ↥W (2 * m),
      gaugeEnd (realIsoGauge Z Z' e i i' hWi hWi') hc y ∈ Punct ↥W (2 * m) :=
    gaugeEnd_mem (realIsoGauge Z Z' e i i' hWi hWi') hc hbijD
  have hgf1 : ∀ p ∈ pieceZero (realification Z) W,
      ((chartHomeo (realification Z') (2 * m) covE i' W hWi' :
        C(↥((realification Z').proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
        (realPieceMap (realification Z) (realification Z') e W)) p ∈ Punct ↥W (2 * m) :=
    fun p hp => chartHomeo_mem (realification Z') (2 * m) covE i' W hWi'
      (realPieceMap (realification Z) (realification Z') e W p)
      (realPieceMap_mem (realification Z) (realification Z') e W p hp)
  have hgf2 : ∀ p ∈ pieceZero (realification Z) W,
      ((gaugeEnd (realIsoGauge Z Z' e i i' hWi hWi') hc).comp
        (chartHomeo (realification Z) (2 * m) covE i W hWi :
          C(↥((realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m))))) p
        ∈ Punct ↥W (2 * m) :=
    fun p hp => hmemG _ (chartHomeo_mem (realification Z) (2 * m) covE i W hWi p hp)
  rw [localThomOfChart_tau, localThomOfChart_tau]
  erw [relCohMap_compA_apply (pieceZero (realification Z) W) (pieceZero (realification Z') W)
    (Punct ↥W (2 * m)) (realPieceMap (realification Z) (realification Z') e W)
    (chartHomeo (realification Z') (2 * m) covE i' W hWi' :
      C(↥((realification Z').proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m))))
    (realPieceMap_mem (realification Z) (realification Z') e W)
    (chartHomeo_mem (realification Z') (2 * m) covE i' W hWi') hgf1 ℤ (2 * m) (Mpun (2 * m) ↥W)]
  erw [relCohMap_congrA (pieceZero (realification Z) W) (Punct ↥W (2 * m)) hcomp hgf1 hgf2
    ℤ (2 * m)]
  erw [← relCohMap_compA_apply (pieceZero (realification Z) W) (Punct ↥W (2 * m))
    (Punct ↥W (2 * m)) (chartHomeo (realification Z) (2 * m) covE i W hWi :
      C(↥((realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m))))
    (gaugeEnd (realIsoGauge Z Z' e i i' hWi hWi') hc)
    (chartHomeo_mem (realification Z) (2 * m) covE i W hWi) hmemG hgf2
    ℤ (2 * m) (Mpun (2 * m) ↥W)]
  erw [Mpun_gaugeEnd_invariant (2 * m) (by omega) (realIsoGauge Z Z' e i i' hWi hWi') hc hdet']

/-- **The canonical local Thom data of `realification Z'` and of `realification Z` agree under an
orientation-preserving isomorphism.** -/
theorem localThomOfComplexCover_realIso_pos {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z'))
    (hdet : ∀ b : B, 0 < LinearMap.det (e.hom b)) :
    (relCohMap (realPieceMap (realification Z) (realification Z') e Set.univ)
      (pieceZero (realification Z) Set.univ)
      (pieceZero (realification Z') Set.univ)
      (realPieceMap_mem (realification Z) (realification Z') e Set.univ) ℤ (2 * m)).hom
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
  have hkey : ((relCohMap (realPieceMap (realification Z) (realification Z') e Set.univ)
        (pieceZero (realification Z) Set.univ) (pieceZero (realification Z') Set.univ)
        (realPieceMap_mem (realification Z) (realification Z') e Set.univ) ℤ (2 * m)).hom
        (localThomOfComplexCover hm Z').τ)
      = (localThomOfComplexCover hm Z).τ := by
    refine localThom_eq_of_cover (realification Z) (2 * m) (P := Set.univ) (pairCover Z Z')
      hVopen hVsub Finset.univ hcov
      ((localThomOfComplexCover hm Z).τ)
      ((relCohMap (realPieceMap (realification Z) (realification Z') e Set.univ)
        (pieceZero (realification Z) Set.univ) (pieceZero (realification Z') Set.univ)
        (realPieceMap_mem (realification Z) (realification Z') e Set.univ) ℤ (2 * m)).hom
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
          ((realification Z).proj ⁻¹' (pairCover Z Z' p)) (Set.preimage_mono (hVsub p))
          (2 * m)).hom
          (localThomOfComplexCover hm Z).τ
          = (localThomOfChart (realification Z) (2 * m) covE p.1 (pairCover Z Z' p) hsub).τ := by
        rw [pdcz_pdCohMap_apply_congr (TopCat.of (realification Z).TotalSpace)
          (zeroComplement (realification Z)) (Set.preimage_mono (hVsub p))
          (Set.preimage_mono (fun _ _ => Set.mem_univ _)) (2 * m)
          ((localThomOfComplexCover hm Z).τ)]
        exact localThomOfComplexCover_pdCohMap_subset hm Z p.1 (W := pairCover Z Z' p) hsub
      have hZ' : (Work.Cohomology.pdCohMap (TopCat.of (realification Z').TotalSpace)
          (zeroComplement (realification Z')) ((realification Z').proj ⁻¹' (Set.univ : Set B))
          ((realification Z').proj ⁻¹' (pairCover Z Z' p)) (Set.preimage_mono (hVsub p))
          (2 * m)).hom
          (localThomOfComplexCover hm Z').τ
          = (localThomOfChart (realification Z') (2 * m) covE p.2 (pairCover Z Z' p) hsub').τ := by
        rw [pdcz_pdCohMap_apply_congr (TopCat.of (realification Z').TotalSpace)
          (zeroComplement (realification Z')) (Set.preimage_mono (hVsub p))
          (Set.preimage_mono (fun _ _ => Set.mem_univ _)) (2 * m)
          ((localThomOfComplexCover hm Z').τ)]
        exact localThomOfComplexCover_pdCohMap_subset hm Z' p.2 (W := pairCover Z Z' p) hsub'
      have hmem1 : ∀ x ∈ pieceZero (realification Z) (pairCover Z Z' p),
          (realPieceMap (realification Z) (realification Z') e Set.univ)
            (pieceIncl (realification Z) (pairCover Z Z' p) Set.univ
              (hVsub p) x) ∈ pieceZero (realification Z') Set.univ :=
        fun x hx => realPieceMap_mem (realification Z) (realification Z') e Set.univ _
          (pieceIncl_mem (realification Z) (pairCover Z Z' p) Set.univ (hVsub p) x hx)
      have hmem2 : ∀ x ∈ pieceZero (realification Z) (pairCover Z Z' p),
          (pieceIncl (realification Z') (pairCover Z Z' p) Set.univ (hVsub p))
            (realPieceMap (realification Z) (realification Z') e (pairCover Z Z' p) x)
            ∈ pieceZero (realification Z') Set.univ :=
        fun x hx => pieceIncl_mem (realification Z') (pairCover Z Z' p) Set.univ (hVsub p) _
          (realPieceMap_mem (realification Z) (realification Z') e (pairCover Z Z' p) x hx)
      have hcompmap : (realPieceMap (realification Z) (realification Z') e Set.univ).comp
            (pieceIncl (realification Z) (pairCover Z Z' p) Set.univ (hVsub p))
          = (pieceIncl (realification Z') (pairCover Z Z' p) Set.univ (hVsub p)).comp
              (realPieceMap (realification Z) (realification Z') e (pairCover Z Z' p)) :=
        pieceIncl_comp_realPieceMap (realification Z) (realification Z') e (hVsub p)
      rw [hZ]
      rw [pdCohMap_eq_relCohMap (realification Z) (pairCover Z Z' p) Set.univ (hVsub p) (2 * m)]
      erw [relCohMap_compA_apply (pieceZero (realification Z) (pairCover Z Z' p))
        (pieceZero (realification Z) Set.univ) (pieceZero (realification Z') Set.univ)
        (pieceIncl (realification Z) (pairCover Z Z' p) Set.univ (hVsub p))
        (realPieceMap (realification Z) (realification Z') e Set.univ)
        (pieceIncl_mem (realification Z) (pairCover Z Z' p) Set.univ (hVsub p))
        (realPieceMap_mem (realification Z) (realification Z') e Set.univ) hmem1 ℤ (2 * m)
        ((localThomOfComplexCover hm Z').τ)]
      rw [relCohMap_congrA (pieceZero (realification Z) (pairCover Z Z' p))
        (pieceZero (realification Z') Set.univ) hcompmap hmem1 hmem2 ℤ (2 * m)]
      rw [← relCohMap_compA_apply (pieceZero (realification Z) (pairCover Z Z' p))
        (pieceZero (realification Z') (pairCover Z Z' p)) (pieceZero (realification Z') Set.univ)
        (realPieceMap (realification Z) (realification Z') e (pairCover Z Z' p))
        (pieceIncl (realification Z') (pairCover Z Z' p) Set.univ (hVsub p))
        (realPieceMap_mem (realification Z) (realification Z') e (pairCover Z Z' p))
        (pieceIncl_mem (realification Z') (pairCover Z Z' p) Set.univ (hVsub p)) hmem2 ℤ (2 * m)
        ((localThomOfComplexCover hm Z').τ)]
      erw [← pdCohMap_eq_relCohMap (realification Z') (pairCover Z Z' p) Set.univ (hVsub p)
        (2 * m)]
      erw [hZ']
      rw [localThomOfChart_realIso_pos hm Z Z' e p.1 p.2 hsub hsub' hdet]
  exact hkey

/-- **The canonical Thom classes agree** under an orientation-preserving isomorphism of the
realifications. -/
theorem thomClassOf_realIso_pos {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z'))
    (hdet : ∀ b : B, 0 < LinearMap.det (e.hom b)) :
    (relCohMap (realTotalMap (realification Z) (realification Z') e)
      (zeroComplement (realification Z))
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
      (realTotalMap (realification Z) (realification Z') e) x ∈ zeroComplement (realification Z') :=
    fun _ hp => e.hom_ne_zero hp
  have hmemZ : ∀ x ∈ pzZ, univZ x ∈ zeroComplement (realification Z) := fun _ hy => hy
  have hmemZ' : ∀ x ∈ pzZ', univZ' x ∈ zeroComplement (realification Z') := fun _ hy => hy
  have hgf : ∀ x ∈ pzZ,
      ((realTotalMap (realification Z) (realification Z') e).comp univZ) x
        ∈ zeroComplement (realification Z') :=
    fun x hx => hmemT (univZ x) (hmemZ x hx)
  have hgf' : ∀ x ∈ pzZ,
      (univZ'.comp (realPieceMap (realification Z) (realification Z') e Set.univ)) x
        ∈ zeroComplement (realification Z') :=
    fun x hx => hmemZ' _
      (realPieceMap_mem (realification Z) (realification Z') e Set.univ x hx)
  have hspecZ := thomClassOf_spec (hm := hm) Z
  have hspecZ' := thomClassOf_spec (hm := hm) Z'
  have hspecZ'' : (relCohMap univZ pzZ (zeroComplement (realification Z)) hmemZ
      ℤ (2 * m)).hom (thomClassOf hm Z).τ = (localThomOfComplexCover hm Z).τ := hspecZ
  have hanat := localThomOfComplexCover_realIso_pos hm Z Z' e hdet
  have hcompmap : (realTotalMap (realification Z) (realification Z') e).comp univZ
      = univZ'.comp (realPieceMap (realification Z) (realification Z') e Set.univ) := by
    simpa only [univZ, univZ'] using
      realTotalMap_comp_subtype (realification Z) (realification Z') e
  let eZ : ↥((realification Z).proj ⁻¹' (Set.univ : Set B)) ≃ₜ (realification Z).TotalSpace :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, Set.mem_univ p⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun p => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun _ => trivial) }
  have hbij := bijective_relCohMap_of_homeomorphA pzZ (zeroComplement (realification Z)) eZ
    (fun y => Iff.rfl) ℤ (2 * m)
  refine hbij.1 ?_
  calc (relCohMap univZ pzZ (zeroComplement (realification Z)) hmemZ ℤ (2 * m)).hom
        ((relCohMap (realTotalMap (realification Z) (realification Z') e)
          (zeroComplement (realification Z)) (zeroComplement (realification Z')) hmemT
          ℤ (2 * m)).hom (thomClassOf hm Z').τ)
      = (relCohMap ((realTotalMap (realification Z) (realification Z') e).comp univZ) pzZ
          (zeroComplement (realification Z')) hgf ℤ (2 * m)).hom (thomClassOf hm Z').τ :=
        relCohMap_compA_apply pzZ (zeroComplement (realification Z))
          (zeroComplement (realification Z')) univZ
          (realTotalMap (realification Z) (realification Z') e) hmemZ hmemT
          hgf ℤ (2 * m) (thomClassOf hm Z').τ
    _ = (relCohMap (univZ'.comp (realPieceMap (realification Z) (realification Z') e Set.univ))
          pzZ (zeroComplement (realification Z')) hgf' ℤ (2 * m)).hom
          (thomClassOf hm Z').τ :=
        congrArg (fun φ => φ.hom (thomClassOf hm Z').τ)
          (relCohMap_congrA pzZ (zeroComplement (realification Z')) hcompmap hgf hgf' ℤ (2 * m))
    _ = (relCohMap (realPieceMap (realification Z) (realification Z') e Set.univ) pzZ pzZ'
          (realPieceMap_mem (realification Z) (realification Z') e Set.univ) ℤ (2 * m)).hom
          ((relCohMap univZ' pzZ' (zeroComplement (realification Z')) hmemZ' ℤ (2 * m)).hom
            (thomClassOf hm Z').τ) :=
        (relCohMap_compA_apply pzZ pzZ' (zeroComplement (realification Z'))
          (realPieceMap (realification Z) (realification Z') e Set.univ) univZ'
          (realPieceMap_mem (realification Z) (realification Z') e Set.univ)
          hmemZ' hgf' ℤ (2 * m) (thomClassOf hm Z').τ).symm
    _ = (relCohMap (realPieceMap (realification Z) (realification Z') e Set.univ) pzZ pzZ'
          (realPieceMap_mem (realification Z) (realification Z') e Set.univ) ℤ (2 * m)).hom
          (localThomOfComplexCover hm Z').τ :=
        congrArg (fun z => (relCohMap (realPieceMap (realification Z) (realification Z') e Set.univ)
          pzZ pzZ' (realPieceMap_mem (realification Z) (realification Z') e Set.univ)
          ℤ (2 * m)).hom z) hspecZ'
    _ = (localThomOfComplexCover hm Z).τ := hanat
    _ = (relCohMap univZ pzZ (zeroComplement (realification Z)) hmemZ ℤ (2 * m)).hom
          ((thomClassOf hm Z).τ) := by
        rw [hspecZ'']

/-
**ORIENTATION-PRESERVING ISOMORPHISMS OF THE REALIFICATIONS PRESERVE THE CANONICAL EULER CLASS.**

This is the `det > 0` companion of the proved result `Work.Gen.eulerClass_neg_of_realIso`
(`Submission/Work/Gen/eulerClass_neg_of_realIso.lean`), which gives
`(thomClassRank m hm Z').eulerClass = - (thomClassRank m hm Z).eulerClass` when the fibrewise
determinant is everywhere *negative*.  Both are needed to control the top Chern class of the
conjugate bundle: the fibrewise conjugation on `EuclideanSpace ℂ (Fin m)` has real determinant
`(-1)^m`, so the even and the odd case of `c_m(Z̄) = (-1)^m c_m(Z)` need the two lemmas.

The proof mirrors `Submission/Work/Gen/eulerClass_neg_of_realIso.lean` line by line, replacing
every use of the orientation-reversing input by the orientation-preserving one:

1. `Work.Gen.localThomOfChart_realIso_neg` has the companion `localThomOfChart_realIso_pos` below,
   built on `Work.Thom.localThomOfChart_eq_of_det_pos`
   (`Submission/Work/Thom/isOrientedOver_of_det_pos.lean`) -- the chart classes *agree* (rather than
   differ by a sign) when the gauge has positive determinant.
2. `Work.Gen.Mpun_gaugeEnd_neg` has the companion `Work.Thom.Mpun_gaugeEnd_invariant`
   (`isOrientedOver_of_det_pos.lean`), which says an everywhere-positive-determinant gauge fixes the
   model class `Mpun`.
3. Consequently the whole chain of `localThomOfComplexCover` / `thomClassOf_realIso_pos` /
   `eulerClass_eq_of_realIso_det_pos` transposes, and the conclusion loses its minus sign.
The determinant-positivity bookkeeping is `det_realIsoGauge_pos` below, the positive companion of
`Work.Gen.det_realIsoGauge_neg` (`Submission/Work/Gen/RealIsoGaugeLemmas.lean`, where the two
`coordChange` factors are `ℂ`-linear hence have positive real determinant).
-/
theorem eulerClass_eq_of_realIso_det_pos {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : Work.Thom.BundleIso (Work.Thom.realification Z) (Work.Thom.realification Z'))
    (hdet : ∀ b, 0 < LinearMap.det (e.hom b)) :
    (Work.Thom.thomClassRank m hm Z').eulerClass
      = (Work.Thom.thomClassRank m hm Z).eulerClass := by
  have hmap : (realTotalMap (realification Z) (realification Z') e).comp
        (zeroSection (realification Z)) = zeroSection (realification Z') := by
    apply ContinuousMap.ext
    intro b
    simp only [ContinuousMap.comp_apply, realTotalMap_apply, BundleIso.toTotalSpace_apply,
      zeroSection_apply, BundleIso.hom_zero]
  have h := thomClassOf_realIso_pos hm Z Z' e hdet
  show (CohMap (zeroSection (realification Z')) ℤ (2 * m)).hom
        ((openToAbs (realification Z') (2 * m)).hom (thomClassOf hm Z').τ)
      = (CohMap (zeroSection (realification Z)) ℤ (2 * m)).hom
        ((openToAbs (realification Z) (2 * m)).hom (thomClassOf hm Z).τ)
  rw [← hmap]
  rw [← CohMap_comp_apply (zeroSection (realification Z))
    (realTotalMap (realification Z) (realification Z') e) ℤ (2 * m) _]
  rw [← relCohMap_relToAbs_apply (realTotalMap (realification Z) (realification Z') e)
    (zeroComplement (realification Z)) (zeroComplement (realification Z'))
    (fun _ hp => e.hom_ne_zero hp) ℤ (2 * m) (thomClassOf hm Z').τ]
  rw [h]



end

end Work.Whitney
