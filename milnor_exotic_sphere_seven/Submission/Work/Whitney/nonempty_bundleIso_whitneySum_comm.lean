import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Whitney sum commutes with the interchange of the summands

`Work.Whitney.whitneySum Z₁ Z₂` and `Work.Whitney.whitneySum Z₂ Z₁` are the same bundle — the
direct sum is symmetric — but they are *presented* differently: the first has fibre
`EuclideanSpace ℂ (Fin (m₁ + m₂))` over the cover `ι₁ × ι₂`, the second fibre
`EuclideanSpace ℂ (Fin (m₂ + m₁))` over the cover `ι₂ × ι₁`.  This module proves that they are
isomorphic (`Work.Whitney.nonempty_bundleIso_whitneySum_comm`).

The isomorphism is the constant gauge

`Work.Whitney.sumCommGauge m₁ m₂ : ℂ^{m₁+m₂} ≃L[ℂ] ℂ^{m₂+m₁}`,
`e ↦ sumFibreC m₂ m₁ (swap (sumFibreC m₁ m₂)⁻¹ e)`,

transporting the *swap* of the two summands; it is a `ContinuousLinearEquiv` between two *different*
model fibres, which is why the general tool
`Work.Whitney.nonempty_bundleIso_of_gauge_fibre` below is stated for two bundles with different
fibres `F`, `F'` and different covers `ι`, `ι'` related by an equivalence `σ : ι ≃ ι'`.

## What is here

* `Work.Whitney.nonempty_bundleIso_of_gauge_fibre` — a constant gauge `e : F ≃L[𝕜] F'` whose
  conjugation with the transition functions of `X` and `Y` (with `σ`-shifted indices) computes the
  transition functions of `Y` gives a `BundleIso X Y`.  This is the two-fibre generalisation of
  `Work.Thom.nonempty_bundleIso_of_gauge` (and of `Work.Thom.continuousOn_chartExpr_gauge`); it is
  proved by feeding the chart expressions to `Work.Thom.continuous_totalSpaceMap_clm_gen`.
* `Work.Whitney.sumCommGauge` / `sumCommGaugeCLM` — the swapping gauge and its underlying
  continuous linear map.
* `Work.Whitney.whitneySum_comm_gauge_conj` — the conjugation identity, the only place where the
  explicit form of `sumFibreC` and of the swap `ℂ^{m₁} × ℂ^{m₂} ≃L ℂ^{m₂} × ℂ^{m₁}` is used.
* `Work.Whitney.nonempty_bundleIso_whitneySum_comm` — the target.
-/

namespace Work.Whitney

open Work.TangentClasses

noncomputable section

/-! ## The general gauge lemma -/

/-- **A bundle isomorphism from a constant gauge between two different model fibres.**

`X` has cover `ι` and fibre `F`, `Y` has cover `ι'` and fibre `F'`; `σ : ι ≃ ι'` identifies the
covers and `e : F ≃L[𝕜] F'` the fibres, in such a way that `hconj` holds: in the canonical
trivialisations, the transition function of `Y` followed by `e` is `e` followed by the transition
function of `X`.  Then `hom b := e`, `inv b := e.symm` is a bundle isomorphism.

The hypotheses `hbase` and `hindex` say that `Y`'s charts are the `σ`-shifted charts of `X`. -/
theorem nonempty_bundleIso_of_gauge_fibre {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {ι ι' : Type*} (X : VectorBundleCore 𝕜 B F ι) (Y : VectorBundleCore 𝕜 B F' ι')
    (e : F ≃L[𝕜] F') (σ : ι ≃ ι')
    (hbase : ∀ i : ι, Y.baseSet (σ i) = X.baseSet i)
    (hindex : ∀ b : B, Y.indexAt b = σ (X.indexAt b))
    (hconj : ∀ (i : ι) (b : B),
      (Y.coordChange (Y.indexAt b) (σ i) b).comp ((e : F →L[𝕜] F'))
        = ((e : F →L[𝕜] F')).comp (X.coordChange (X.indexAt b) i b)) :
    Nonempty (Work.Thom.BundleIso X Y) := by
  -- `hindex` lets one read the transition functions of `Y` in the chart of `X`.
  have hconj' : ∀ (i : ι) (b : B),
      (Y.coordChange (σ (X.indexAt b)) (σ i) b).comp ((e : F →L[𝕜] F'))
        = ((e : F →L[𝕜] F')).comp (X.coordChange (X.indexAt b) i b) := by
    intro i b
    rw [← hindex b]
    exact hconj i b
  -- Continuity of the total-space map `X → Y`, chart by chart: on `X.baseSet i₁ ∩ Y.baseSet i₂`
  -- the conjugate of the gauge is, by `hconj` and `coordChange_comp`, `Y.coordChange (σ i₁) i₂ ∘ e`.
  have hT : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B =>
      (Y.coordChange (Y.indexAt b) i₂ b).comp (((e : F →L[𝕜] F').comp
        (X.coordChange i₁ (X.indexAt b) b)))) (X.baseSet i₁ ∩ Y.baseSet i₂) := by
    intro i₁ i₂
    refine ContinuousOn.congr (f := fun b : B =>
      (Y.coordChange (σ i₁) i₂ b).comp (e : F →L[𝕜] F')) ?_ ?_
    · refine ContinuousOn.clm_comp ?_ continuousOn_const
      exact (Y.continuousOn_coordChange (σ i₁) i₂).mono
        (fun b hb => ⟨by rw [hbase i₁]; exact hb.1, hb.2⟩)
    · intro b hb
      have hbX : b ∈ X.baseSet i₁ := hb.1
      have hbY2 : b ∈ Y.baseSet i₂ := hb.2
      have hbY1 : b ∈ Y.baseSet (σ i₁) := by rw [hbase i₁]; exact hbX
      have hcomp : (Y.coordChange (Y.indexAt b) i₂ b)
          = (Y.coordChange (σ i₁) i₂ b).comp (Y.coordChange (Y.indexAt b) (σ i₁) b) :=
        (Y.coordChange_linear_comp (Y.indexAt b) (σ i₁) i₂ b
          ⟨⟨Y.mem_baseSet_at b, hbY1⟩, hbY2⟩).symm
      have hXc : (X.coordChange (X.indexAt b) i₁ b).comp
          (X.coordChange i₁ (X.indexAt b) b) = ContinuousLinearMap.id 𝕜 F := by
        rw [X.coordChange_linear_comp i₁ (X.indexAt b) i₁ b
          ⟨⟨hbX, X.mem_baseSet_at b⟩, hbX⟩]
        ext v
        exact X.coordChange_self i₁ b hbX v
      calc (Y.coordChange (Y.indexAt b) i₂ b).comp ((e : F →L[𝕜] F').comp
              (X.coordChange i₁ (X.indexAt b) b))
          = ((Y.coordChange (σ i₁) i₂ b).comp (Y.coordChange (Y.indexAt b) (σ i₁) b)).comp
              ((e : F →L[𝕜] F').comp (X.coordChange i₁ (X.indexAt b) b)) := by rw [hcomp]
        _ = (Y.coordChange (σ i₁) i₂ b).comp ((Y.coordChange (Y.indexAt b) (σ i₁) b).comp
              ((e : F →L[𝕜] F').comp (X.coordChange i₁ (X.indexAt b) b))) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp (((Y.coordChange (Y.indexAt b) (σ i₁) b).comp
              (e : F →L[𝕜] F')).comp (X.coordChange i₁ (X.indexAt b) b)) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp (((e : F →L[𝕜] F').comp
              (X.coordChange (X.indexAt b) i₁ b)).comp
              (X.coordChange i₁ (X.indexAt b) b)) := by rw [hindex b, hconj' i₁ b]
        _ = (Y.coordChange (σ i₁) i₂ b).comp ((e : F →L[𝕜] F').comp
              ((X.coordChange (X.indexAt b) i₁ b).comp (X.coordChange i₁ (X.indexAt b) b))) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp ((e : F →L[𝕜] F').comp
              (ContinuousLinearMap.id 𝕜 F)) := by rw [hXc]
        _ = (Y.coordChange (σ i₁) i₂ b).comp (e : F →L[𝕜] F') := by
              rw [ContinuousLinearMap.comp_id]
  -- The same for `Y → X` with the inverse gauge; the conjugation identity for `e.symm` is
  -- obtained from `hconj` by composing with `e.symm` on both sides.
  have hTi : ∀ (i₂ : ι') (i₁ : ι), ContinuousOn (fun b : B =>
      (X.coordChange (X.indexAt b) i₁ b).comp (((e.symm : F' →L[𝕜] F).comp
        (Y.coordChange i₂ (Y.indexAt b) b)))) (Y.baseSet i₂ ∩ X.baseSet i₁) := by
    intro i₂ i₁
    refine ContinuousOn.congr (f := fun b : B =>
      ((e.symm : F' →L[𝕜] F)).comp (Y.coordChange i₂ (σ i₁) b)) ?_ ?_
    · refine ContinuousOn.clm_comp continuousOn_const ?_
      exact (Y.continuousOn_coordChange i₂ (σ i₁)).mono
        (fun b hb => ⟨hb.1, by rw [hbase i₁]; exact hb.2⟩)
    · intro b hb
      have hbY2 : b ∈ Y.baseSet i₂ := hb.1
      have hbX1 : b ∈ X.baseSet i₁ := hb.2
      have hbY1 : b ∈ Y.baseSet (σ i₁) := by rw [hbase i₁]; exact hbX1
      have hrev : (X.coordChange (X.indexAt b) i₁ b).comp ((e.symm : F' →L[𝕜] F))
          = ((e.symm : F' →L[𝕜] F)).comp (Y.coordChange (Y.indexAt b) (σ i₁) b) := by
        apply ContinuousLinearMap.ext
        intro w
        simp only [ContinuousLinearMap.comp_apply]
        have h2 : (Y.coordChange (Y.indexAt b) (σ i₁) b)
              ((e : F →L[𝕜] F') ((e.symm : F' →L[𝕜] F) w))
            = (e : F →L[𝕜] F')
              ((X.coordChange (X.indexAt b) i₁ b) ((e.symm : F' →L[𝕜] F) w)) := by
          have h3 := congrArg (fun (L : F →L[𝕜] F') => L ((e.symm : F' →L[𝕜] F) w))
            (hconj i₁ b)
          simpa only [ContinuousLinearMap.comp_apply] using h3
        calc (X.coordChange (X.indexAt b) i₁ b) ((e.symm : F' →L[𝕜] F) w)
            = (e.symm : F' →L[𝕜] F)
                ((e : F →L[𝕜] F')
                  ((X.coordChange (X.indexAt b) i₁ b) ((e.symm : F' →L[𝕜] F) w))) := by
                simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
          _ = (e.symm : F' →L[𝕜] F)
                ((Y.coordChange (Y.indexAt b) (σ i₁) b)
                  ((e : F →L[𝕜] F') ((e.symm : F' →L[𝕜] F) w))) := by rw [h2]
          _ = (e.symm : F' →L[𝕜] F) ((Y.coordChange (Y.indexAt b) (σ i₁) b) w) := by
                simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      have hcomp2 : (Y.coordChange (Y.indexAt b) (σ i₁) b).comp
            (Y.coordChange i₂ (Y.indexAt b) b) = Y.coordChange i₂ (σ i₁) b :=
        Y.coordChange_linear_comp i₂ (Y.indexAt b) (σ i₁) b
          ⟨⟨hbY2, Y.mem_baseSet_at b⟩, hbY1⟩
      calc (X.coordChange (X.indexAt b) i₁ b).comp (((e.symm : F' →L[𝕜] F)).comp
              (Y.coordChange i₂ (Y.indexAt b) b))
          = (((X.coordChange (X.indexAt b) i₁ b).comp (e.symm : F' →L[𝕜] F)).comp
              (Y.coordChange i₂ (Y.indexAt b) b)) := by
              rw [← ContinuousLinearMap.comp_assoc]
        _ = (((e.symm : F' →L[𝕜] F)).comp (Y.coordChange (Y.indexAt b) (σ i₁) b)).comp
              (Y.coordChange i₂ (Y.indexAt b) b) := by rw [hrev]
        _ = ((e.symm : F' →L[𝕜] F)).comp ((Y.coordChange (Y.indexAt b) (σ i₁) b).comp
              (Y.coordChange i₂ (Y.indexAt b) b)) := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = ((e.symm : F' →L[𝕜] F)).comp (Y.coordChange i₂ (σ i₁) b) := by rw [hcomp2]
  refine ⟨{ hom := fun _ => (e : F →L[𝕜] F').toLinearMap
            inv := fun _ => (e.symm : F' →L[𝕜] F).toLinearMap
            left_inv := fun b x => ?_
            right_inv := fun b y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · exact e.symm_apply_apply x
  · exact e.apply_symm_apply y
  · have hc : Continuous (fun p : X.TotalSpace =>
        (⟨p.1, (e : F →L[𝕜] F') p.2⟩ : Y.TotalSpace)) := by
      have hc0 := Work.Thom.continuous_totalSpaceMap_clm_gen X Y (ContinuousMap.id B)
        (fun _ => (e : F →L[𝕜] F')) (by
          intro i₁ i₂
          simpa only [ContinuousMap.coe_id, Set.preimage_id, ContinuousMap.id_apply] using hT i₁ i₂)
      simpa only [ContinuousMap.id_apply] using hc0
    refine Continuous.congr hc (fun p => ?_)
    exact congrArg (fun w : F' => (⟨p.1, w⟩ : Y.TotalSpace))
      (congrFun (ContinuousLinearMap.coe_coe (e : F →L[𝕜] F')).symm p.2)
  · have hc : Continuous (fun p : Y.TotalSpace =>
        (⟨p.1, (e.symm : F' →L[𝕜] F) p.2⟩ : X.TotalSpace)) := by
      have hc0 := Work.Thom.continuous_totalSpaceMap_clm_gen Y X (ContinuousMap.id B)
        (fun _ => (e.symm : F' →L[𝕜] F)) (by
          intro i₂ i₁
          simpa only [ContinuousMap.coe_id, Set.preimage_id, ContinuousMap.id_apply] using hTi i₂ i₁)
      simpa only [ContinuousMap.id_apply] using hc0
    refine Continuous.congr hc (fun p => ?_)
    exact congrArg (fun w : F => (⟨p.1, w⟩ : X.TotalSpace))
      (congrFun (ContinuousLinearMap.coe_coe (e.symm : F' →L[𝕜] F)).symm p.2)

/-! ## The gauge interchanging the two summands -/

/-- The continuous linear map underlying `Work.Whitney.sumCommGauge`: swap the two summands
(`ℂ^{m₁} × ℂ^{m₂} → ℂ^{m₂} × ℂ^{m₁}`) and re-concatenate with the other splitting. -/
noncomputable def sumCommGaugeCLM (m₁ m₂ : ℕ) :
    EuclideanSpace ℂ (Fin (m₁ + m₂)) →L[ℂ] EuclideanSpace ℂ (Fin (m₂ + m₁)) :=
  (sumFibreC m₂ m₁ : (EuclideanSpace ℂ (Fin m₂) × EuclideanSpace ℂ (Fin m₁)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m₂ + m₁))).comp
    ((((ContinuousLinearEquiv.prodComm ℂ (EuclideanSpace ℂ (Fin m₁))
        (EuclideanSpace ℂ (Fin m₂))) :
          (EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂)) →L[ℂ]
            (EuclideanSpace ℂ (Fin m₂) × EuclideanSpace ℂ (Fin m₁))).comp
      ((sumFibreC m₁ m₂).symm : EuclideanSpace ℂ (Fin (m₁ + m₂)) →L[ℂ]
        (EuclideanSpace ℂ (Fin m₁) × EuclideanSpace ℂ (Fin m₂)))))

/-- **The gauge interchanging the two summands**: `ℂ^{m₁+m₂} ≃L[ℂ] ℂ^{m₂+m₁}` obtained from the
splittings `sumFibreC` and the swap of the two factors.  Note that its source and target model
fibres are *different*, which is exactly why `nonempty_bundleIso_of_gauge_fibre` allows that. -/
noncomputable def sumCommGauge (m₁ m₂ : ℕ) :
    EuclideanSpace ℂ (Fin (m₁ + m₂)) ≃L[ℂ] EuclideanSpace ℂ (Fin (m₂ + m₁)) :=
  ((sumFibreC m₁ m₂).symm.trans
    ((ContinuousLinearEquiv.prodComm ℂ (EuclideanSpace ℂ (Fin m₁))
        (EuclideanSpace ℂ (Fin m₂))).trans (sumFibreC m₂ m₁)))

/-- The underlying continuous linear map of `Work.Whitney.sumCommGauge`. -/
theorem sumCommGauge_coe (m₁ m₂ : ℕ) :
    ((sumCommGauge m₁ m₂ : EuclideanSpace ℂ (Fin (m₁ + m₂)) →L[ℂ]
        EuclideanSpace ℂ (Fin (m₂ + m₁)))) = sumCommGaugeCLM m₁ m₂ := rfl

/-! ## The explicit swap of the two factors -/

/-- **The product of two linear maps commutes with the swap of the factors**: `(T₂ × T₁) ∘ swap` is
`swap ∘ (T₁ × T₂)`. -/
theorem prodMap_prodComm_swap {𝕜 : Type*} [Semiring 𝕜] {F₁ F₂ : Type*} [TopologicalSpace F₁]
    [AddCommMonoid F₁] [Module 𝕜 F₁] [TopologicalSpace F₂] [AddCommMonoid F₂] [Module 𝕜 F₂]
    (T₁ : F₁ →L[𝕜] F₁) (T₂ : F₂ →L[𝕜] F₂) :
    (T₂.prodMap T₁).comp
        ((ContinuousLinearEquiv.prodComm 𝕜 F₁ F₂ : (F₁ × F₂) ≃L[𝕜] (F₂ × F₁)) :
          (F₁ × F₂) →L[𝕜] (F₂ × F₁))
      = ((ContinuousLinearEquiv.prodComm 𝕜 F₁ F₂ : (F₁ × F₂) ≃L[𝕜] (F₂ × F₁)) :
          (F₁ × F₂) →L[𝕜] (F₂ × F₁)).comp (T₁.prodMap T₂) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨a, b⟩ := x
  simp [ContinuousLinearMap.coe_prodMap', ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk]

/-- The pointwise form of `Work.Whitney.prodMap_prodComm_swap`. -/
theorem prodMap_prodComm_swap_apply {𝕜 : Type*} [Semiring 𝕜] {F₁ F₂ : Type*} [TopologicalSpace F₁]
    [AddCommMonoid F₁] [Module 𝕜 F₁] [TopologicalSpace F₂] [AddCommMonoid F₂] [Module 𝕜 F₂]
    (T₁ : F₁ →L[𝕜] F₁) (T₂ : F₂ →L[𝕜] F₂) (w : F₁ × F₂) :
    (T₂.prodMap T₁) ((ContinuousLinearEquiv.prodComm 𝕜 F₁ F₂) w)
      = (ContinuousLinearEquiv.prodComm 𝕜 F₁ F₂) ((T₁.prodMap T₂) w) := by
  obtain ⟨a, b⟩ := w
  simp [ContinuousLinearMap.coe_prodMap', ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk]

/-! ## The conjugation identity -/

/-- **The conjugation identity for the swapping gauge.**  In the canonical trivialisations of
`whitneySum Z₁ Z₂` and `whitneySum Z₂ Z₁` (the latter indexed through the swap of the factors), the
transition functions of the two sums are conjugate by `Work.Whitney.sumCommGaugeCLM`; this is the
`hconj` hypothesis of `Work.Whitney.nonempty_bundleIso_of_gauge_fibre`. -/
theorem whitneySum_comm_gauge_conj {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    {B : Type} [TopologicalSpace B]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (b : B) (i : ι₁ × ι₂) :
    ((whitneySum Z₂ Z₁).coordChange ((whitneySum Z₂ Z₁).indexAt b)
        ((Equiv.prodComm ι₁ ι₂) i) b).comp (sumCommGaugeCLM m₁ m₂)
      = (sumCommGaugeCLM m₁ m₂).comp
        ((whitneySum Z₁ Z₂).coordChange ((whitneySum Z₁ Z₂).indexAt b) i b) := by
  obtain ⟨i₁, i₂⟩ := i
  ext v i'
  simp only [whitneySum_coordChange, whitneySum_indexAt, sumCommGaugeCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Equiv.prodComm_apply, ContinuousLinearEquiv.symm_apply_apply, Prod.swap_prod_mk]
  rw [prodMap_prodComm_swap_apply]

/-! ## The target -/

/-- **The Whitney sum commutes with the interchange of the summands.** -/
theorem nonempty_bundleIso_whitneySum_comm {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    {B : Type} [TopologicalSpace B]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.whitneySum Z₁ Z₂)
      (Work.Whitney.whitneySum Z₂ Z₁)) := by
  refine nonempty_bundleIso_of_gauge_fibre (whitneySum Z₁ Z₂) (whitneySum Z₂ Z₁)
    (sumCommGauge m₁ m₂) (Equiv.prodComm ι₁ ι₂) ?_ ?_ ?_
  · intro i
    simp only [whitneySum_baseSet, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    exact Set.inter_comm _ _
  · intro b
    rfl
  · intro i b
    simpa only [sumCommGauge_coe] using whitneySum_comm_gauge_conj Z₁ Z₂ b i

end

end Work.Whitney
