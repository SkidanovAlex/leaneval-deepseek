import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.Gen.ConjLine
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Gen.tautDual_iso_conjLine
import Submission.Work.Thom.CovDefs
import Submission.Work.Thom.BundleIsoGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Gen

open Work.TangentClasses Work.Thom Work.Projective

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {ι ι' : Type*}

def bundleIsoOfGauge (Z : VectorBundleCore 𝕜 B F ι)
    (Z' : VectorBundleCore 𝕜 B F' ι')
    (Φ : ι → ι' → B → (F →L[𝕜] F')) (Φinv : ι → ι' → B → (F' →L[𝕜] F))
    (hcont : ∀ i i', ContinuousOn (fun b => Φ i i' b) (Z.baseSet i ∩ Z'.baseSet i'))
    (hcontinv : ∀ i i', ContinuousOn (fun b => Φinv i i' b) (Z.baseSet i ∩ Z'.baseSet i'))
    (htgt : ∀ i t t' b, b ∈ Z.baseSet i → b ∈ Z'.baseSet t → b ∈ Z'.baseSet t' →
      (Z'.coordChange t t' b).comp (Φ i t b) = Φ i t' b)
    (hsrc : ∀ i t i' b, b ∈ Z.baseSet i → b ∈ Z.baseSet i' → b ∈ Z'.baseSet t →
      (Φ i t b).comp (Z.coordChange i' i b) = Φ i' t b)
    (htgtinv : ∀ i t t' b, b ∈ Z.baseSet i → b ∈ Z'.baseSet t → b ∈ Z'.baseSet t' →
      (Φinv i t b).comp (Z'.coordChange t' t b) = Φinv i t' b)
    (hsrcinv : ∀ i t i' b, b ∈ Z.baseSet i → b ∈ Z.baseSet i' → b ∈ Z'.baseSet t →
      (Z.coordChange i i' b).comp (Φinv i t b) = Φinv i' t b)
    (hleft : ∀ i i' b x, b ∈ Z.baseSet i ∩ Z'.baseSet i' → Φinv i i' b (Φ i i' b x) = x)
    (hright : ∀ i i' b y, b ∈ Z.baseSet i ∩ Z'.baseSet i' → Φ i i' b (Φinv i i' b y) = y) :
    BundleIso Z Z' := by
  have hT : ∀ i₁ i₂, ContinuousOn (fun b : B =>
      (Z'.coordChange (Z'.indexAt b) i₂ b).comp
        (((Φ (Z.indexAt b) (Z'.indexAt b) b).comp (Z.coordChange i₁ (Z.indexAt b) b))))
      (Z.baseSet i₁ ∩ Z'.baseSet i₂) := by
    intro i₁ i₂
    refine (hcont i₁ i₂).congr (fun b hb => ?_)
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply]
    have h1 := congrArg (fun (L : F →L[𝕜] F') => L (Z.coordChange i₁ (Z.indexAt b) b v))
        (htgt (Z.indexAt b) (Z'.indexAt b) i₂ b (Z.mem_baseSet_at b)
          (Z'.mem_baseSet_at b) hb.2)
    rw [ContinuousLinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun (L : F →L[𝕜] F') => L v)
      (hsrc (Z.indexAt b) i₂ i₁ b (Z.mem_baseSet_at b) hb.1 hb.2)
    rwa [ContinuousLinearMap.comp_apply] at h2
  have hTi : ∀ (i₂ : ι') (i₁ : ι), ContinuousOn (fun b : B =>
      (Z.coordChange (Z.indexAt b) i₁ b).comp
        (((Φinv (Z.indexAt b) (Z'.indexAt b) b).comp (Z'.coordChange i₂ (Z'.indexAt b) b))))
      (Z'.baseSet i₂ ∩ Z.baseSet i₁) := by
    intro i₂ i₁
    refine ((hcontinv i₁ i₂).mono (fun b hb => ⟨hb.2, hb.1⟩)).congr (fun b hb => ?_)
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply]
    have h1 := congrArg (fun (L : F' →L[𝕜] F) => L v)
        (htgtinv (Z.indexAt b) (Z'.indexAt b) i₂ b (Z.mem_baseSet_at b)
          (Z'.mem_baseSet_at b) hb.1)
    rw [ContinuousLinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun (L : F' →L[𝕜] F) => L v)
      (hsrcinv (Z.indexAt b) i₂ i₁ b (Z.mem_baseSet_at b) hb.2 hb.1)
    rwa [ContinuousLinearMap.comp_apply] at h2
  refine ⟨fun b => (Φ (Z.indexAt b) (Z'.indexAt b) b).toLinearMap,
    fun b => (Φinv (Z.indexAt b) (Z'.indexAt b) b).toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro b x
    exact hleft _ _ b x ⟨Z.mem_baseSet_at b, Z'.mem_baseSet_at b⟩
  · intro b y
    exact hright _ _ b y ⟨Z.mem_baseSet_at b, Z'.mem_baseSet_at b⟩
  · exact continuous_totalSpaceMap_clm_gen Z Z'
      (ContinuousMap.id B) (fun b => Φ (Z.indexAt b) (Z'.indexAt b) b) hT
  · exact continuous_totalSpaceMap_clm_gen Z' Z
      (ContinuousMap.id B) (fun b => Φinv (Z.indexAt b) (Z'.indexAt b) b) hTi



/-! ## Complex conjugation on the fibre `ℂ¹` -/

/-- **Complex conjugation** on `EuclideanSpace ℂ (Fin 1)`, as an `ℝ`-linear map. -/
def conjLM : EuclideanSpace ℂ (Fin 1) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1) where
  toFun v := WithLp.toLp 2 (fun _ : Fin 1 => star (v.ofLp 0))
  map_add' v w := by ext i; fin_cases i; simp
  map_smul' r v := by ext i; fin_cases i; simp

@[simp] theorem conjLM_apply (v : EuclideanSpace ℂ (Fin 1)) :
    conjLM v = WithLp.toLp 2 (fun _ : Fin 1 => star (v.ofLp 0)) := rfl

theorem conjLM_involutive (v : EuclideanSpace ℂ (Fin 1)) : conjLM (conjLM v) = v := by
  ext i; fin_cases i; simp [conjLM]

/-- The identification `ℂ¹ ≃ ℝ²` used to compute the determinant of `conjLM`. -/
def conjEe : EuclideanSpace ℂ (Fin 1) ≃ₗ[ℝ] ℂ :=
  ((EuclideanSpace.equiv (Fin 1) ℂ).toLinearEquiv.restrictScalars ℝ).trans
    ((LinearEquiv.funUnique (Fin 1) ℂ ℂ).restrictScalars ℝ)

theorem conjEe_apply (v : EuclideanSpace ℂ (Fin 1)) : conjEe v = v.ofLp 0 := by
  simp only [conjEe, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.funUnique_apply]
  rfl

theorem conjEe_symm_ofLp (w : ℂ) : (conjEe.symm w).ofLp 0 = w := by
  rw [← conjEe_apply (conjEe.symm w), LinearEquiv.apply_symm_apply]

/-- **The determinant of complex conjugation (on `ℂ¹`) is `-1`.** -/
theorem det_conjLM : LinearMap.det conjLM = -1 := by
  have hs : ((conjEe.symm : ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin 1)).symm).toLinearMap
      = conjEe.toLinearMap := by
    rw [LinearEquiv.symm_symm]
  have h : conjLM = (conjEe.symm : ℂ →ₗ[ℝ] EuclideanSpace ℂ (Fin 1)) ∘ₗ
      (Complex.conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ
      (conjEe : EuclideanSpace ℂ (Fin 1) →ₗ[ℝ] ℂ) := by
    apply LinearMap.ext
    intro v
    apply WithLp.ofLp_injective 2
    funext i
    fin_cases i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, conjEe_apply, conjEe_symm_ofLp,
      Complex.conjLIE_apply]
    rfl
  have hconj := LinearMap.det_conj (f := (Complex.conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ))
    (e := (conjEe.symm : ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin 1)))
  rw [hs] at hconj
  rw [h, hconj, Complex.det_conjLIE]

/-- Complex conjugation as a **continuous** `ℝ`-linear endomorphism of `ℂ¹`. -/
def conjCLM : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  LinearMap.toContinuousLinearMap conjLM

@[simp] theorem conjCLM_apply (v : EuclideanSpace ℂ (Fin 1)) : conjCLM v = conjLM v := rfl

/-! ## The gauge data of the conjugation isomorphism -/

variable {n : ℕ}

/-- The forward gauge `Φ i t b = h(i,t) · conj` comparing the chart `i` of
`realification (conjLine n)` with the chart `t` of `realification (tautLine n)`. -/
def conjPhi (i t : Fin (n + 1)) (b : CP n) :
    EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  (homCoord n i t b) • conjCLM

/-- The inverse gauge `Φ⁻¹ i t b = \overline{h(i,t)}^{-1} · conj`. -/
def conjPhiInv (i t : Fin (n + 1)) (b : CP n) :
    EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  (star (homCoord n i t b))⁻¹ • conjCLM

@[simp] theorem conjPhi_apply (i t : Fin (n + 1)) (b : CP n)
    (v : EuclideanSpace ℂ (Fin 1)) :
    conjPhi i t b v = homCoord n i t b • conjLM v := by
  simp [conjPhi, conjCLM]

@[simp] theorem conjPhiInv_apply (i t : Fin (n + 1)) (b : CP n)
    (v : EuclideanSpace ℂ (Fin 1)) :
    conjPhiInv i t b v = (star (homCoord n i t b))⁻¹ • conjLM v := by
  simp [conjPhiInv, conjCLM]

theorem continuous_clm_smul_conjCLM :
    Continuous (fun a : ℂ => a • conjCLM) :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun a : ℂ => a • conjCLM
       map_add' := by intro a b; ext v; simp [add_smul]
       map_smul' := by intro r a; ext v; simp [mul_assoc] } :
      ℂ →ₗ[ℝ] (EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℂ (Fin 1)))

theorem continuousOn_conjPhi (i t : Fin (n + 1)) :
    ContinuousOn (fun b : CP n => conjPhi i t b) (chartSet i ∩ chartSet t) := by
  have hfun : (fun b : CP n => conjPhi i t b)
      = (fun a : ℂ => a • conjCLM) ∘ (homCoord n i t) := rfl
  rw [hfun]
  exact (continuous_clm_smul_conjCLM.comp_continuousOn
    (continuousOn_homCoord (n := n) i t)).mono (Set.inter_subset_left)

theorem continuousOn_conjPhiInv (i t : Fin (n + 1)) :
    ContinuousOn (fun b : CP n => conjPhiInv i t b) (chartSet i ∩ chartSet t) := by
  have hne : ∀ b ∈ chartSet i ∩ chartSet t, star (homCoord n i t b) ≠ 0 :=
    fun b hb => star_ne_zero.mpr (homCoord_ne_zero_of_mem i t hb.1 hb.2)
  have h1 : ContinuousOn (fun b : CP n => (star (homCoord n i t b))⁻¹)
      (chartSet i ∩ chartSet t) :=
    ((continuousOn_homCoord (n := n) i t).star.mono (Set.inter_subset_left)).inv₀ hne
  have hfun : (fun b : CP n => conjPhiInv i t b)
      = (fun a : ℂ => a • conjCLM) ∘ (fun b : CP n => (star (homCoord n i t b))⁻¹) := rfl
  rw [hfun]
  exact continuous_clm_smul_conjCLM.comp_continuousOn h1


theorem conjLM_smul (a : ℂ) (v : EuclideanSpace ℂ (Fin 1)) :
    conjLM (a • v) = star a • conjLM v := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  simp [conjLM]

theorem realif_tautLine_coordChange_apply (t t' : Fin (n + 1)) (b : CP n)
    (v : EuclideanSpace ℂ (Fin 1)) :
    (realification (tautLine n)).coordChange t t' b v = homCoord n t t' b • v := by
  rw [realification_coordChange]
  simp

theorem realif_conjLine_coordChange_apply (i i' : Fin (n + 1)) (b : CP n)
    (v : EuclideanSpace ℂ (Fin 1)) :
    (realification (conjLine n)).coordChange i i' b v = star (homCoord n i i' b) • v := by
  rw [realification_coordChange]
  simp

/-- **The explicit real bundle isomorphism `realification (conjLine n) ≅ realification (tautLine n)`
given by fibrewise complex conjugation.** -/
def conjIso (n : ℕ) :
    BundleIso (realification (conjLine n)) (realification (tautLine n)) :=
  bundleIsoOfGauge (realification (conjLine n)) (realification (tautLine n))
    (fun i t b => conjPhi i t b) (fun i t b => conjPhiInv i t b)
    (fun i t => by
      simpa only [realification_baseSet, conjLine_baseSet, tautLine_baseSet]
        using continuousOn_conjPhi (n := n) i t)
    (fun i t => by
      simpa only [realification_baseSet, conjLine_baseSet, tautLine_baseSet]
        using continuousOn_conjPhiInv (n := n) i t)
    (fun i t t' b hb_i hb_t hb_t' => by
      simp only [realification_baseSet, conjLine_baseSet, tautLine_baseSet] at hb_i hb_t hb_t'
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, conjPhi_apply, realif_tautLine_coordChange_apply,
        conjPhi_apply, smul_smul, homCoord_mul i t t' hb_i hb_t hb_t'])
    (fun i t i' b hb_i hb_i' hb_t => by
      simp only [realification_baseSet, conjLine_baseSet, tautLine_baseSet] at hb_i hb_i' hb_t
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, realif_conjLine_coordChange_apply, conjPhi_apply,
        conjPhi_apply, conjLM_smul, smul_smul, star_star, homCoord_mul i' i t hb_i' hb_i hb_t])
    (fun i t t' b hb_i hb_t hb_t' => by
      simp only [realification_baseSet, conjLine_baseSet, tautLine_baseSet] at hb_i hb_t hb_t'
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, realif_tautLine_coordChange_apply, conjPhiInv_apply,
        conjPhiInv_apply, conjLM_smul, smul_smul]
      congr 1
      rw [homCoord_mul i t' t hb_i hb_t' hb_t, star_mul, mul_inv_rev, mul_assoc,
        mul_comm ((star (homCoord n i t' b))⁻¹) (star (homCoord n t' t b)), ← mul_assoc,
        inv_mul_cancel₀ (star_ne_zero.mpr (homCoord_ne_zero_of_mem t' t hb_t' hb_t)), one_mul])
    (fun i t i' b hb_i hb_i' hb_t => by
      simp only [realification_baseSet, conjLine_baseSet, tautLine_baseSet] at hb_i hb_i' hb_t
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, conjPhiInv_apply, realif_conjLine_coordChange_apply,
        conjPhiInv_apply, smul_smul]
      congr 1
      rw [homCoord_mul i i' t hb_i hb_i' hb_t, star_mul, mul_inv_rev, ← mul_assoc,
        mul_comm (star (homCoord n i i' b)) ((star (homCoord n i' t b))⁻¹), mul_assoc,
        mul_inv_cancel₀ (star_ne_zero.mpr (homCoord_ne_zero_of_mem i i' hb_i hb_i')), mul_one])
    (fun i i' b x hb => by
      have hb' : b ∈ chartSet i ∩ chartSet i' := by
        simpa only [realification_baseSet, conjLine_baseSet, tautLine_baseSet, Set.mem_inter_iff]
          using hb
      have hne : star (homCoord n i i' b) ≠ 0 :=
        star_ne_zero.mpr (homCoord_ne_zero_of_mem i i' hb'.1 hb'.2)
      show conjPhiInv i i' b (conjPhi i i' b x) = x
      rw [conjPhi_apply, conjPhiInv_apply, conjLM_smul, conjLM_involutive, smul_smul,
        inv_mul_cancel₀ hne, one_smul])
    (fun i i' b y hb => by
      have hb' : b ∈ chartSet i ∩ chartSet i' := by
        simpa only [realification_baseSet, conjLine_baseSet, tautLine_baseSet, Set.mem_inter_iff]
          using hb
      have hne : homCoord n i i' b ≠ 0 := homCoord_ne_zero_of_mem i i' hb'.1 hb'.2
      show conjPhi i i' b (conjPhiInv i i' b y) = y
      rw [conjPhiInv_apply, conjPhi_apply, conjLM_smul, conjLM_involutive, star_inv₀, star_star,
        smul_smul, mul_inv_cancel₀ hne, one_smul])

/-- The fibrewise map of `conjIso` is complex conjugation. -/
theorem conjIso_hom (n : ℕ) (b : CP n) (v : EuclideanSpace ℂ (Fin 1)) :
    (conjIso n).hom b v = conjLM v := by
  show conjPhi ((realification (conjLine n)).indexAt b)
      ((realification (tautLine n)).indexAt b) b v = conjLM v
  rw [conjPhi_apply]
  simp only [realification_indexAt, conjLine_indexAt, tautLine_indexAt]
  rw [homCoord_self, one_smul]

theorem conjIso_hom_fiber (n : ℕ) (b : CP n)
    (v : (realification (conjLine n)).Fiber b) :
    (conjIso n).hom b v = conjLM (RealBundle.fiber_eq (realification (conjLine n)) b ▸ v) :=
  conjIso_hom n b (RealBundle.fiber_eq (realification (conjLine n)) b ▸ v)

/-! ## Scalar multiplication on the fibre and its determinant -/

/-- Multiplication by a complex number `a` on `ℂ¹`, as an `ℝ`-linear map. -/
def mulLM (a : ℂ) : EuclideanSpace ℂ (Fin 1) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1) :=
  conjEe.symm.toLinearMap ∘ₗ
    (LinearMap.restrictScalars ℝ (a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))) ∘ₗ conjEe.toLinearMap

theorem mulLM_apply (a : ℂ) (v : EuclideanSpace ℂ (Fin 1)) : mulLM a v = a • v := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  simp only [mulLM, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
    LinearMap.id_apply, conjEe_apply, conjEe_symm_ofLp]
  rfl

/-- **The real determinant of the multiplication-by-`a` map is `‖a‖²`.** -/
theorem det_mulLM (a : ℂ) : LinearMap.det (mulLM a) = Complex.normSq a := by
  haveI : NeZero (Module.finrank ℂ ℂ) := ⟨by simp⟩
  have hdet : LinearMap.det (a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) = a := by
    rw [LinearMap.det_smul, Module.finrank_self]
    simp
  have hs : ((conjEe.symm : ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin 1)).symm).toLinearMap
      = conjEe.toLinearMap := by rw [LinearEquiv.symm_symm]
  have hconj := LinearMap.det_conj
    (f := LinearMap.restrictScalars ℝ (a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))
    (e := (conjEe.symm : ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin 1)))
  rw [hs] at hconj
  rw [mulLM]
  rw [hconj]
  rw [det_restrictScalars_eq_normSq, hdet]

/-! ## The gauge of the conjugation isomorphism and its determinant -/

/-- The gauge of `conjIso` over the charts `i` (source) and `i'` (target), in the chain form
`covE ∘ C'_{indexAt→i'} ∘ conj ∘ C_{i→indexAt} ∘ covE⁻¹`. -/
def conjGauge (n : ℕ) (i i' : Fin (n + 1)) (x : CP n) : Gauge (2 * 1) :=
  let A : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin (2 * 1)) := covE (m := 1)
  let B : EuclideanSpace ℝ (Fin (2 * 1)) →L[ℝ] EuclideanSpace ℂ (Fin 1) := (covE (m := 1)).symm
  A.comp (((homCoord n i i' x) • conjCLM).comp B)

theorem conjGauge_apply (i i' : Fin (n + 1)) (x : CP n)
    (v : EuclideanSpace ℝ (Fin (2 * 1))) :
    conjGauge (n := n) i i' x v
      = covE (m := 1) ((homCoord n i i' x) • conjLM ((covE (m := 1)).symm v)) := rfl

theorem continuousOn_conjGauge (i i' : Fin (n + 1)) :
    ContinuousOn (fun x : CP n => conjGauge (n := n) i i' x) (chartSet i ∩ chartSet i') := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_clm_of_continuous_apply
  show Continuous (fun p : ↥(chartSet i ∩ chartSet i') × EuclideanSpace ℝ (Fin (2 * 1)) =>
    covE (m := 1) ((homCoord n i i' (p.1 : CP n)) • conjLM ((covE (m := 1)).symm p.2)))
  have h1 : Continuous (fun p : ↥(chartSet i ∩ chartSet i') × EuclideanSpace ℝ (Fin (2 * 1)) =>
      homCoord n i i' (p.1 : CP n)) :=
    (continuousOn_homCoord (n := n) i i').comp_continuous
      (continuous_subtype_val.comp continuous_fst) (fun x => x.1.2.1)
  have h2 : Continuous (fun p : ↥(chartSet i ∩ chartSet i') × EuclideanSpace ℝ (Fin (2 * 1)) =>
      conjLM ((covE (m := 1)).symm p.2)) :=
    conjCLM.continuous.comp ((covE (m := 1)).symm.continuous.comp continuous_snd)
  exact (covE (m := 1)).continuous.comp (h1.smul h2)

theorem det_smul_conjLM (h : ℂ) :
    LinearMap.det (h • conjLM) = Complex.normSq h * (-1) := by
  have hcomp : (h • conjLM) = mulLM h ∘ₗ conjLM := by
    ext v
    rw [LinearMap.comp_apply, mulLM_apply, LinearMap.smul_apply]
  rw [hcomp, LinearMap.det_comp, det_mulLM, det_conjLM]

theorem det_conjGauge_neg (i i' : Fin (n + 1)) {x : CP n}
    (hx : x ∈ chartSet i ∩ chartSet i') :
    LinearMap.det (conjGauge (n := n) i i' x).toLinearMap < 0 := by
  have hne : homCoord n i i' x ≠ 0 := homCoord_ne_zero_of_mem i i' hx.1 hx.2
  have hpos : 0 < Complex.normSq (homCoord n i i' x) := Complex.normSq_pos.mpr hne
  have hL : (conjGauge (n := n) i i' x).toLinearMap
      = (↑((covE (m := 1)).toLinearEquiv) :
            EuclideanSpace ℂ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * 1))) ∘ₗ
        ((homCoord n i i' x) • conjLM) ∘ₗ
        (↑(((covE (m := 1)).toLinearEquiv).symm) :
            EuclideanSpace ℝ (Fin (2 * 1)) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1)) := by
    rw [conjGauge]
    ext v
    simp only [ContinuousLinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, conjCLM_apply, ContinuousLinearMap.coe_coe]
    rfl
  rw [hL]
  have hconj := LinearMap.det_conj (f := ((homCoord n i i' x) • conjLM))
    (e := ((covE (m := 1)).toLinearEquiv : EuclideanSpace ℂ (Fin 1) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (2 * 1))))
  rw [hconj, det_smul_conjLM]
  nlinarith

/-! ## The piece map of a real bundle isomorphism, and the gauge family over a chart -/

/-- **The map of the pieces induced by a bundle isomorphism** (real bundles, arbitrary fibres):
`p ↦ (p.1, e.hom p.1.1 p.1.2)`. -/
def pieceMapIsoR {B : Type} [TopologicalSpace B] {F F' : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type*}
    (Z : VectorBundleCore ℝ B F ι) (Z' : VectorBundleCore ℝ B F' ι')
    (e : BundleIso Z Z') (W : Set B) :
    C(↥(Z.proj ⁻¹' W), ↥(Z'.proj ⁻¹' W)) :=
  ⟨fun p => ⟨e.toTotalSpace p.1, p.2⟩,
    Continuous.subtype_mk (e.continuous_hom.comp continuous_subtype_val) (fun p => p.2)⟩

@[simp] theorem pieceMapIsoR_apply {B : Type} [TopologicalSpace B] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {ι ι' : Type*} (Z : VectorBundleCore ℝ B F ι) (Z' : VectorBundleCore ℝ B F' ι')
    (e : BundleIso Z Z') (W : Set B) (p : ↥(Z.proj ⁻¹' W)) :
    ((pieceMapIsoR Z Z' e W p : ↥(Z'.proj ⁻¹' W)) : Z'.TotalSpace)
      = (⟨p.1.1, e.hom p.1.1 p.1.2⟩ : Z'.TotalSpace) := rfl

theorem conjBaseSet_i (i : Fin (n + 1)) (W : Set (CP n))
    (hWi : W ⊆ (realification (conjLine n)).baseSet i) : W ⊆ chartSet i := fun x hx => by
  have h := hWi hx
  rwa [realification_baseSet, conjLine_baseSet] at h

theorem conjBaseSet_i' (i' : Fin (n + 1)) (W : Set (CP n))
    (hWi' : W ⊆ (realification (tautLine n)).baseSet i') : W ⊆ chartSet i' := fun x hx => by
  have h := hWi' hx
  rwa [realification_baseSet, tautLine_baseSet] at h

theorem continuous_conjGauge_W (i i' : Fin (n + 1)) (W : Set (CP n))
    (hWi : W ⊆ (realification (conjLine n)).baseSet i)
    (hWi' : W ⊆ (realification (tautLine n)).baseSet i') :
    Continuous (fun x : ↥W => conjGauge (n := n) i i' (x : CP n)) :=
  (continuousOn_conjGauge (n := n) i i').comp_continuous continuous_subtype_val
    (fun x => ⟨conjBaseSet_i i W hWi x.2, conjBaseSet_i' i' W hWi' x.2⟩)

theorem det_conjGauge_neg_W (i i' : Fin (n + 1)) (W : Set (CP n))
    (hWi : W ⊆ (realification (conjLine n)).baseSet i)
    (hWi' : W ⊆ (realification (tautLine n)).baseSet i') :
    ∀ x : ↥W, LinearMap.det (conjGauge (n := n) i i' (x : CP n)).toLinearMap < 0 :=
  fun x => det_conjGauge_neg i i' ⟨conjBaseSet_i i W hWi x.2, conjBaseSet_i' i' W hWi' x.2⟩


end

end Work.Gen
