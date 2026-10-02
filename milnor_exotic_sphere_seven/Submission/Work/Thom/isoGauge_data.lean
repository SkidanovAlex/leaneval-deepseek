import Mathlib
import Submission.Work.Thom.BundleIsoGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ} {ι ι' : Type}

/-! ## The three components of `Work.Thom.isoGauge_data`

For two complex bundles `Z`, `Z'` over a common base, a bundle isomorphism `e : Z ≅ Z'` and a set
`W ⊆ (realification Z).baseSet i ∩ (realification Z').baseSet i'`, the gauge `isoGauge Z Z' e i i'`
(see `Submission/Work/Thom/BundleIsoGauge.lean`) compares the chart `i` of `realification Z` with the
chart `i'` of `realification Z'` through `e`.  This file provides the three facts needed to compare
the local Thom classes of the two charts:

* `Work.Thom.continuous_isoGauge` — `isoGauge` is continuous (it is a composite of the chart
  trivialisations with the bundle isomorphism, whose *middle* factor `e.hom` prevents the
  discontinuous factors from being separated);
* `Work.Thom.isoGauge_compHom` — the defining **intertwining identity** of the gauge:
  `(chartHomeo Z' …) ∘ pieceMapIso = (gaugeEnd (isoGauge …)) ∘ (chartHomeo Z …)`;
* `Work.Thom.det_isoGauge_pos` — `isoGauge` has **positive real determinant** (it is the
  realification of a `ℂ`-linear bijection, conjugated by `covE`).
-/

/-- The chart index of a point of `W ⊆ Z.baseSet i` lies in `Z.baseSet i`. -/
theorem mem_baseSet_i_of_mem {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι} {i : ι}
    {W : Set B} (hWi : W ⊆ (realification Z).baseSet i) (b : B) (hb : b ∈ W) :
    b ∈ Z.baseSet i := by
  rw [← realification_baseSet]
  exact hWi hb

/-- **Continuity of the gauge `isoGauge`.**

`isoGauge` is the composite of the inverse chart of `Z` (in the chart `i`), the fibrewise linear
map `e.hom`, and the chart of `Z'` (in the chart `i'`), all transported to `ℝ^{2m}` by `covE`.  The
first and last factors are only continuous as maps *into* the total spaces, so the argument goes
through the total spaces: the composite

`↥W × ℂᵐ --chart⁻¹--> Z.TotalSpace --e--> Z'.TotalSpace --chart--> B × ℂᵐ`

is continuous, hence so is its second component. -/
theorem continuous_isoGauge
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i') :
    Continuous (isoGauge Z Z' e i i' hWi hWi') := by
  apply continuous_clm_of_continuous_apply
  have hbaseZ : ∀ q : ↥W × EuclideanSpace ℂ (Fin m), (q.1 : B) ∈ (Z.baseSet i) :=
    fun q => mem_baseSet_i_of_mem hWi _ q.1.2
  have hbaseZ' : ∀ q : ↥W × EuclideanSpace ℂ (Fin m), (q.1 : B) ∈ (Z'.baseSet i') :=
    fun q => mem_baseSet_i_of_mem hWi' _ q.1.2
  have hG1 : Continuous fun q : ↥W × EuclideanSpace ℂ (Fin m) =>
      (⟨(q.1 : B), (Z.localTriv i).symm (q.1 : B) q.2⟩ : Z.TotalSpace) := by
    have hsymm := @Bundle.Trivialization.continuousOn_symm B (EuclideanSpace ℂ (Fin m)) Z.Fiber
      ‹TopologicalSpace B› (inferInstance : TopologicalSpace (EuclideanSpace ℂ (Fin m)))
      (Z.toTopologicalSpace) (fun x => ⟨0⟩) (Z.localTriv i)
    refine hsymm.comp_continuous
      (f := fun q : ↥W × EuclideanSpace ℂ (Fin m) => ((q.1 : B), q.2)) ?_ ?_
    · exact Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd
    · intro q; exact ⟨hbaseZ q, Set.mem_univ q.2⟩
  have hG : Continuous fun q : ↥W × EuclideanSpace ℂ (Fin m) =>
      e.toTotalSpace (⟨(q.1 : B), (Z.localTriv i).symm (q.1 : B) q.2⟩ : Z.TotalSpace) :=
    e.continuous_hom.comp hG1
  have hGmem : ∀ q : ↥W × EuclideanSpace ℂ (Fin m),
      e.toTotalSpace (⟨(q.1 : B), (Z.localTriv i).symm (q.1 : B) q.2⟩ : Z.TotalSpace) ∈
        (Z'.localTriv i').source := by
    intro q
    rw [VectorBundleCore.mem_localTriv_source]
    exact hbaseZ' q
  have hH : Continuous fun q : ↥W × EuclideanSpace ℂ (Fin m) =>
      (Z'.localTriv i')
        (e.toTotalSpace (⟨(q.1 : B), (Z.localTriv i).symm (q.1 : B) q.2⟩ : Z.TotalSpace)) :=
    (Z'.localTriv i').continuousOn.comp_continuous hG hGmem
  let K : ↥W × EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin m) :=
    fun q => ((Z'.localTriv i')
      (e.toTotalSpace (⟨(q.1 : B), (Z.localTriv i).symm (q.1 : B) q.2⟩ : Z.TotalSpace))).2
  have hK : Continuous K := hH.snd
  have hKval : ∀ q : ↥W × EuclideanSpace ℂ (Fin m), K q =
      (Z'.coordChange (Z'.indexAt (q.1 : B)) i' (q.1 : B))
        (e.hom (q.1 : B) (Z.coordChange i (Z.indexAt (q.1 : B)) (q.1 : B) q.2)) := by
    intro q
    have hbZ : (q.1 : B) ∈ (Z.localTriv i).baseSet := by
      show (q.1 : B) ∈ Z.baseSet i
      exact mem_baseSet_i_of_mem hWi _ q.1.2
    show ((Z'.localTriv i')
      (e.toTotalSpace (⟨(q.1 : B), (Z.localTriv i).symm (q.1 : B) q.2⟩ : Z.TotalSpace))).2 = _
    rw [VectorBundleCore.localTriv_apply]
    dsimp only
    rw [BundleIso.toTotalSpace_apply]
    dsimp only
    rw [VectorBundleCore.localTriv_symm_apply Z i hbZ]
  have hΦ : Continuous fun p : ↥W × EuclideanSpace ℝ (Fin (2 * m)) =>
      (p.1, (covE (m := m)).symm p.2) :=
    Continuous.prodMk continuous_fst ((covE (m := m)).symm.continuous.comp continuous_snd)
  have hfinal : Continuous fun p : ↥W × EuclideanSpace ℝ (Fin (2 * m)) =>
      (covE (m := m)) (K (p.1, (covE (m := m)).symm p.2)) :=
    (covE (m := m)).continuous.comp (hK.comp hΦ)
  refine hfinal.congr (fun p => ?_)
  rw [isoGauge_apply]
  refine congrArg (fun w => (covE (m := m)) w) ?_
  rw [hKval (p.1, (covE (m := m)).symm p.2)]
  rw [realification_coordChange, realification_indexAt]
  rw [realification_coordChange, realification_indexAt]

/-- **The determinant of the gauge is positive.**

`isoGauge … x` is the realification of the `ℂ`-linear map
`(Z'.coordChange (Z'.indexAt x) i' x) ∘ e.hom x ∘ (Z.coordChange i (Z.indexAt x) x)`, conjugated by
the (real) linear equivalence `covE : ℂᵐ ≃ ℝ^{2m}`; since each factor is a `ℂ`-linear bijection, the
real determinant is `|det_ℂ|² > 0` (`Work.Thom.det_restrictScalars_pos`,
`Work.Thom.coordChange_bijective`). -/
theorem det_isoGauge_pos
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i') (x : ↥W) :
    0 < LinearMap.det ((isoGauge Z Z' e i i' hWi hWi' x).toLinearMap) := by
  let A : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    (Z'.coordChange (Z'.indexAt (x : B)) i' (x : B)).toLinearMap.comp
      ((e.hom (x : B)).comp (Z.coordChange i (Z.indexAt (x : B)) (x : B)).toLinearMap)
  have hlin : (isoGauge Z Z' e i i' hWi hWi' x).toLinearMap
      = (covE (m := m)).toLinearEquiv.conj (A.restrictScalars ℝ) := by
    refine LinearMap.ext (fun v => ?_)
    change isoGauge Z Z' e i i' hWi hWi' x v
      = ((covE (m := m)).toLinearEquiv.conj (A.restrictScalars ℝ)) v
    rw [isoGauge_apply, LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    refine congrArg (fun w => (covE (m := m)) w) ?_
    have hA : ∀ w : EuclideanSpace ℂ (Fin m),
        A w = (Z'.coordChange (Z'.indexAt (x : B)) i' (x : B))
          ((e.hom (x : B)) ((Z.coordChange i (Z.indexAt (x : B)) (x : B)) w)) := fun w => rfl
    rw [hA]
    rw [realification_coordChange, realification_indexAt]
    rw [realification_coordChange, realification_indexAt]
    rfl
  have hx : (x : B) ∈ Z.baseSet i := mem_baseSet_i_of_mem hWi _ x.2
  have hx' : (x : B) ∈ Z'.baseSet i' := mem_baseSet_i_of_mem hWi' _ x.2
  have hAbij : Function.Bijective A := by
    have h1 : Function.Bijective (fun u : EuclideanSpace ℂ (Fin m) =>
        (Z'.coordChange (Z'.indexAt (x : B)) i' (x : B)) u) :=
      coordChange_bijective Z' (Z'.indexAt (x : B)) i' ⟨Z'.mem_baseSet_at _, hx'⟩
    have h2 : Function.Bijective (fun u : EuclideanSpace ℂ (Fin m) => (e.hom (x : B)) u) :=
      ⟨fun a b h => (e.left_inv (x : B) a).symm.trans
          ((congrArg (e.inv (x : B)) h).trans (e.left_inv (x : B) b)),
       fun b => ⟨e.inv (x : B) b, e.right_inv (x : B) b⟩⟩
    have h3 : Function.Bijective (fun u : EuclideanSpace ℂ (Fin m) =>
        (Z.coordChange i (Z.indexAt (x : B)) (x : B)) u) :=
      coordChange_bijective Z i (Z.indexAt (x : B)) ⟨hx, Z.mem_baseSet_at _⟩
    exact h1.comp (h2.comp h3)
  have hdet : LinearMap.det ((isoGauge Z Z' e i i' hWi hWi' x).toLinearMap)
      = LinearMap.det (A.restrictScalars ℝ) := by
    rw [hlin]
    exact LinearMap.det_conj (A.restrictScalars ℝ) ((covE (m := m)).toLinearEquiv)
  rw [hdet]
  exact det_restrictScalars_pos hAbij

/-- **The intertwining identity of the gauge.**

The chart homeomorphism of `Z'` in the chart `i'`, precomposed with the piece map of `e`, is the
gauge endomorphism `(x, v) ↦ (x, isoGauge … x v)` postcomposed with the chart homeomorphism of `Z`
in the chart `i`.  Pointwise, both maps send `p` to

`(⟨x, p.2⟩, covE ((Z'.coordChange (Z'.indexAt x) i' x) (e.hom x p.1.2)))`,

where `x = Z.proj p.1`; the identification of the two expressions uses the cocycle identity
`(Z.coordChange i (Z.indexAt x) x) ((Z.coordChange (Z.indexAt x) i x) v) = v`. -/
theorem isoGauge_compHom
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i')
    (hc : Continuous (isoGauge Z Z' e i i' hWi hWi')) :
    (chartHomeo (realification Z') (2 * m) covE i' W hWi' :
      C(↥((realification Z').proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
        (pieceMapIso Z Z' e W)
      = (gaugeEnd (isoGauge Z Z' e i i' hWi hWi') hc :
              C(↥W × EuclideanSpace ℝ (Fin (2 * m)), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
          (chartHomeo (realification Z) (2 * m) covE i W hWi :
            C(↥((realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))) := by
  apply ContinuousMap.ext
  intro p
  change (chartHomeo (realification Z') (2 * m) covE i' W hWi') (pieceMapIso Z Z' e W p)
      = gaugeEnd (isoGauge Z Z' e i i' hWi hWi') hc
          (chartHomeo (realification Z) (2 * m) covE i W hWi p)
  have hq : pieceMapIso Z Z' e W p =
      (⟨⟨(realification Z).proj p.1, e.hom ((realification Z).proj p.1) p.1.2⟩, p.2⟩ :
        ↥((realification Z').proj ⁻¹' W)) := by
    apply Subtype.ext
    rw [pieceMapIso_apply]
  rw [hq, chartHomeo_apply]
  rw [gaugeEnd_apply, chartHomeo_apply]
  rw [isoGauge_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hcoc : ((realification Z).coordChange i
        ((realification Z).indexAt ((realification Z).proj p.1)) ((realification Z).proj p.1))
        (((realification Z).coordChange ((realification Z).indexAt ((realification Z).proj p.1)) i
          ((realification Z).proj p.1)) p.1.2)
      = p.1.2 := by
    have hmem' : (realification Z).proj p.1 ∈
        (realification Z).baseSet ((realification Z).indexAt ((realification Z).proj p.1))
          ∩ (realification Z).baseSet i
          ∩ (realification Z).baseSet ((realification Z).indexAt ((realification Z).proj p.1)) :=
      ⟨⟨(realification Z).mem_baseSet_at _, hWi p.2⟩, (realification Z).mem_baseSet_at _⟩
    have h1 := VectorBundleCore.coordChange_comp (realification Z)
      ((realification Z).indexAt ((realification Z).proj p.1)) i
      ((realification Z).indexAt ((realification Z).proj p.1)) ((realification Z).proj p.1) hmem'
      p.1.2
    have h2 := VectorBundleCore.coordChange_self (realification Z)
      ((realification Z).indexAt ((realification Z).proj p.1)) ((realification Z).proj p.1)
      ((realification Z).mem_baseSet_at _) p.1.2
    exact h1.trans h2
  rw [hcoc]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext; rfl
  · rfl

theorem isoGauge_data {m : ℕ} (hm : 1 ≤ m) {B : Type} [TopologicalSpace B] {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : Work.Thom.BundleIso Z Z') (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (Work.Thom.realification Z).baseSet i)
    (hWi' : W ⊆ (Work.Thom.realification Z').baseSet i') :
    ∃ hc : Continuous (Work.Thom.isoGauge Z Z' e i i' hWi hWi'),
      ((chartHomeo (Work.Thom.realification Z') (2 * m) Work.Thom.covE i' W hWi' :
          C(↥((Work.Thom.realification Z').proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
          (Work.Thom.pieceMapIso Z Z' e W))
        = ((Work.Thom.gaugeEnd (Work.Thom.isoGauge Z Z' e i i' hWi hWi') hc :
            C(↥W × EuclideanSpace ℝ (Fin (2 * m)), ↥W × EuclideanSpace ℝ (Fin (2 * m)))).comp
          (chartHomeo (Work.Thom.realification Z) (2 * m) Work.Thom.covE i W hWi :
            C(↥((Work.Thom.realification Z).proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin (2 * m)))))
      ∧ (∀ x, 0 < LinearMap.det ((Work.Thom.isoGauge Z Z' e i i' hWi hWi' x).toLinearMap)) := by
  refine ⟨continuous_isoGauge Z Z' e i i' hWi hWi', ?_, ?_⟩
  · exact isoGauge_compHom Z Z' e i i' hWi hWi' (continuous_isoGauge Z Z' e i i' hWi hWi')
  · intro x
    exact det_isoGauge_pos Z Z' e i i' hWi hWi' x

end

end Work.Thom
