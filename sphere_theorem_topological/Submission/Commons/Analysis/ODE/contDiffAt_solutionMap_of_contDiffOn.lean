import Mathlib
import Submission.Commons.Analysis.ODE.contDiffAt_solutionMap
import Submission.Commons.Analysis.ContinuousMap.exists_contDiffOn_nemitskii
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz
import Submission.Commons.Analysis.ODE.contDiffAt_solutionMap_of_eventually

namespace Commons.Analysis.ODE

noncomputable section

open scoped Topology ContDiff
open Set Filter Metric
open SmoothDep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The flattened field `(σ, (t, y)) ↦ t • F (e^{lam σ} • y)`. -/
noncomputable def Gflat (lam : ℝ) (F : E → E) : ℝ × (ℝ × E) → E :=
  fun p => p.2.1 • F (Real.exp (lam * p.1) • p.2.2)

/-- The open set on which `Gflat lam F` is smooth when `F` is smooth on `W`. -/
noncomputable def Vgood (lam : ℝ) (W : Set E) : Set (ℝ × (ℝ × E)) :=
  {p | Real.exp (lam * p.1) • p.2.2 ∈ W}

lemma Vgood_isOpen (lam : ℝ) {W : Set E} (hW : IsOpen W) : IsOpen (Vgood lam W) := by
  have h : Vgood lam W = (fun p : ℝ × (ℝ × E) => Real.exp (lam * p.1) • p.2.2) ⁻¹' W := rfl
  rw [h]
  exact hW.preimage (by fun_prop)

/-- Curves on `K` whose values lie in the pull-back of `W` under `y ↦ e^{lam σ} • y`. -/
noncomputable def Good (lam : ℝ) (W : Set E) : Set (C(K, ℝ × E)) :=
  {γ | ∀ σ : K, Real.exp (lam * (σ : ℝ)) • (γ σ).2 ∈ W}

lemma Gflat_contDiffOn (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) : ContDiffOn ℝ ∞ (Gflat lam F) (Vgood lam W) := by
  have hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × E) => Real.exp (lam * p.1) • p.2.2) (Vgood lam W) := by
    fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × (ℝ × E) => Real.exp (lam * p.1) • p.2.2)
      (Vgood lam W) W := fun p hp => hp
  have hcomp : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × E) => F (Real.exp (lam * p.1) • p.2.2))
      (Vgood lam W) := hF.comp hφ hmap
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × E) => p.2.1) (Vgood lam W) := by fun_prop
  exact (h1.smul hcomp).congr (fun p _ => rfl)

/-- The linear map `γ ↦ (σ ↦ (0, γ σ))`. -/
noncomputable def zeroEmb : C(K, ℝ × E) →L[ℝ] C(K, ℝ × (ℝ × E)) :=
  LinearMap.mkContinuous
    { toFun := fun γ => ⟨fun σ => ((0 : ℝ), γ σ), continuous_const.prodMk γ.continuous⟩
      map_add' := by
        intro γ₁ γ₂
        ext σ <;> simp [ContinuousMap.add_apply]
      map_smul' := by
        intro c γ
        ext σ <;> simp [ContinuousMap.smul_apply] }
    1 (by
      intro γ
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg γ)).mpr (fun σ => ?_)
      show ‖(((0 : ℝ), γ σ) : ℝ × (ℝ × E))‖ ≤ ‖γ‖
      rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
      exact ContinuousMap.norm_coe_le_norm γ σ)

@[simp] lemma zeroEmb_apply (γ : C(K, ℝ × E)) (σ : K) :
    zeroEmb γ σ = ((0 : ℝ), γ σ) := rfl

/-- The constant curve `σ ↦ (σ, 0)`. -/
noncomputable def baseCM : C(K, ℝ × (ℝ × E)) :=
  ⟨fun σ => (((σ : ℝ)), ((0 : ℝ), (0 : E))), continuous_subtype_val.prodMk continuous_const⟩

@[simp] lemma baseCM_apply (σ : K) : baseCM σ = (((σ : ℝ)), ((0 : ℝ), (0 : E))) := rfl

/-- The curve `σ ↦ (σ, γ σ)`. -/
noncomputable def locCurve (γ : C(K, ℝ × E)) : C(K, ℝ × (ℝ × E)) := baseCM + zeroEmb γ

@[simp] lemma locCurve_apply (γ : C(K, ℝ × E)) (σ : K) :
    locCurve γ σ = (((σ : ℝ)), γ σ) := by
  rw [locCurve, ContinuousMap.add_apply, baseCM_apply, zeroEmb_apply]
  ext <;> simp

/-- The localized Nemytskii operator playing the role of `nem (hfun lam F)`. -/
noncomputable def locNem (lam : ℝ) {W : Set E} (hW : IsOpen W) (F : E → E) :
    C(K, ℝ × E) → C(K, E) :=
  fun γ => Commons.Analysis.ContinuousMap.nem (Vgood lam W) (Gflat lam F) (locCurve γ)

lemma locNem_apply (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E} (hF : ContDiffOn ℝ ∞ F W)
    {γ : C(K, ℝ × E)} (hγ : ∀ σ : K, Real.exp (lam * (σ : ℝ)) • (γ σ).2 ∈ W) (σ : K) :
    locNem lam hW F γ σ = Gflat lam F (((σ : ℝ)), γ σ) := by
  unfold locNem
  have hg : ∀ s : K, locCurve γ s ∈ Vgood lam W := by
    intro s
    simpa [locCurve_apply, Vgood] using hγ s
  have hc : Continuous fun s : K => Gflat lam F (locCurve γ s) :=
    (Gflat_contDiffOn lam hW hF).continuousOn.comp_continuous (locCurve γ).continuous hg
  have h := Commons.Analysis.ContinuousMap.nem_apply (M := ℝ × (ℝ × E)) (E := E)
    (F := Gflat lam F) (g := locCurve γ) (Vgood lam W) hg hc σ
  rwa [locCurve_apply] at h

lemma locNem_contDiffOn (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) :
    ContDiffOn ℝ ∞ (locNem lam hW F)
      (Good lam W) := by
  have hnem : ContDiffOn ℝ ∞ (Commons.Analysis.ContinuousMap.nem (Vgood lam W) (Gflat lam F))
      {g : C(K, ℝ × (ℝ × E)) | ∀ s, g s ∈ Vgood lam W} :=
    Commons.Analysis.ContinuousMap.nem_contDiffOn_univ (Vgood_isOpen lam hW)
      (Gflat_contDiffOn lam hW hF)
  have h2u : ContDiffOn ℝ ∞ (fun γ : C(K, ℝ × E) => locCurve γ) Set.univ := by
    show ContDiffOn ℝ ∞ (fun γ : C(K, ℝ × E) => baseCM + zeroEmb γ) Set.univ
    fun_prop
  have h2 := h2u.mono (Set.subset_univ (Good lam W))
  have hmap : Set.MapsTo (fun γ : C(K, ℝ × E) => locCurve γ)
      (Good lam W) {g : C(K, ℝ × (ℝ × E)) | ∀ s, g s ∈ Vgood lam W} := by
    intro γ hγ s
    simpa [locCurve_apply, Vgood] using hγ s
  have hcomp := hnem.comp h2 hmap
  refine hcomp.congr ?_
  intro γ _
  rfl

lemma locNem_hasFDerivAt (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) {γ₀ : C(K, ℝ × E)}
    (hγ₀ : ∀ σ : K, Real.exp (lam * (σ : ℝ)) • (γ₀ σ).2 ∈ W) :
    HasFDerivAt (locNem lam hW F)
      (mulClm (E := ℝ × E) (G := E)
        ⟨fun σ => (fderiv ℝ (Gflat lam F) (((σ : ℝ)), γ₀ σ)).comp
            (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)),
          (((Gflat_contDiffOn lam hW hF).continuousOn_fderiv_of_isOpen
            (Vgood_isOpen lam hW) (by simp)).comp_continuous
              (continuous_subtype_val.prodMk γ₀.continuous) (by
                intro σ
                show Real.exp (lam * (σ : ℝ)) • (γ₀ σ).2 ∈ W
                exact hγ₀ σ)).clm_comp
            (continuous_const : Continuous fun _ : K => (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)))⟩)
      γ₀ := by
  have hd : DifferentiableOn ℝ (Gflat lam F) (Vgood lam W) :=
    (Gflat_contDiffOn lam hW hF).differentiableOn (by simp)
  have hc : ContinuousOn (fderiv ℝ (Gflat lam F)) (Vgood lam W) :=
    (Gflat_contDiffOn lam hW hF).continuousOn_fderiv_of_isOpen (Vgood_isOpen lam hW) (by simp)
  have hcF : ContinuousOn (Gflat lam F) (Vgood lam W) := (Gflat_contDiffOn lam hW hF).continuousOn
  have hg₀ : ∀ s : K, locCurve γ₀ s ∈ Vgood lam W := by
    intro s
    simpa [locCurve_apply, Vgood] using hγ₀ s
  have hT : HasFDerivAt (fun γ : C(K, ℝ × E) => locCurve γ)
      (zeroEmb : C(K, ℝ × E) →L[ℝ] C(K, ℝ × (ℝ × E))) γ₀ := by
    have h1 : HasFDerivAt (fun γ : C(K, ℝ × E) => zeroEmb γ)
        (zeroEmb : C(K, ℝ × E) →L[ℝ] C(K, ℝ × (ℝ × E))) γ₀ := by
      simpa using (zeroEmb : C(K, ℝ × E) →L[ℝ] C(K, ℝ × (ℝ × E))).hasFDerivAt
    have h2 : HasFDerivAt (fun _ : C(K, ℝ × E) => baseCM)
        (0 : C(K, ℝ × E) →L[ℝ] C(K, ℝ × (ℝ × E))) γ₀ :=
      hasFDerivAt_const (𝕜 := ℝ) (c := baseCM) (x := γ₀)
    have h3 : HasFDerivAt (fun γ : C(K, ℝ × E) => baseCM + zeroEmb γ) zeroEmb γ₀ := by
      have h4 := h2.add h1
      rw [zero_add] at h4
      convert h4 using 1
      all_goals rfl
    exact h3
  have hnem := Commons.Analysis.ContinuousMap.hasFDerivAt_nem (W := Vgood lam W)
    (Vgood_isOpen lam hW) hd hc hcF (locCurve γ₀) hg₀
  have hcomp := hnem.comp γ₀ hT
  have hAcont : Continuous fun σ : K =>
      (fderiv ℝ (Gflat lam F) (((σ : ℝ)), γ₀ σ)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)) :=
    (hc.comp_continuous (continuous_subtype_val.prodMk γ₀.continuous) (by
      intro σ
      show Real.exp (lam * (σ : ℝ)) • (γ₀ σ).2 ∈ W
      exact hγ₀ σ)).clm_comp
      (continuous_const : Continuous fun _ : K => (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)))
  convert hcomp using 2
  all_goals first
    | (ext δ σ
       simp only [ContinuousLinearMap.comp_apply, Commons.Analysis.ContinuousMap.clmComp_apply,
         zeroEmb_apply, locCurve_apply, mulClm_apply, mulLin_apply]
       rfl)
    | rfl

section Rescale

variable {F : E → E} {a b : ℝ} {t₀ : ℝ}

lemma hasDerivAt_rescale_pt {w : ℝ → E}
    (hw : ∀ t ∈ Set.Ioo a b, HasDerivAt w (F (w t)) t) {r : ℝ}
    (hr : t₀ * r ∈ Set.Ioo a b) :
    HasDerivAt (fun r : ℝ => w (t₀ * r)) (t₀ • F (w (t₀ * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => t₀ * r) t₀ r := hasDerivAt_const_mul t₀
  have h2 := (hw (t₀ * r) hr).scomp r h1
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using h2

lemma continuous_rescale_pt (ha : a < 0) (hb : 0 < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    {w : ℝ → E} (hw : ∀ t ∈ Set.Ioo a b, HasDerivAt w (F (w t)) t) :
    Continuous fun σ : K => w (t₀ * (σ : ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  exact ((hasDerivAt_rescale_pt hw (t_mul_mem_Ioo ha hb ht₀ σ.2)).continuousAt).comp
    continuous_subtype_val.continuousAt

lemma integral_rescale_pt (ha : a < 0) (hb : 0 < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    {W : Set E} {w : ℝ → E}
    (hw : ∀ t ∈ Set.Ioo a b, HasDerivAt w (F (w t)) t)
    (hWmem : ∀ t ∈ Set.Ioo a b, w t ∈ W) (hFc : ContinuousOn F W)
    {σ : ℝ} (hσ : σ ∈ K) :
    ∫ r in (0 : ℝ)..σ, t₀ • F (w (t₀ * r)) = w (t₀ * σ) - w 0 := by
  have hle : (0 : ℝ) ≤ σ := hσ.1
  have hderiv' : ∀ r ∈ Set.Icc (0 : ℝ) σ,
      HasDerivAt (fun r : ℝ => w (t₀ * r)) (t₀ • F (w (t₀ * r))) r := by
    intro r hr
    exact hasDerivAt_rescale_pt hw
      (t_mul_mem_Ioo ha hb ht₀ ⟨hr.1, le_trans hr.2 hσ.2⟩)
  have hcont : ContinuousOn (fun r : ℝ => w (t₀ * r)) (Set.Icc 0 σ) :=
    HasDerivAt.continuousOn hderiv'
  have hcontu : ContinuousOn (fun r : ℝ => w (t₀ * r)) (Set.uIcc 0 σ) := by
    rwa [Set.uIcc_of_le hle]
  have hint : IntervalIntegrable (fun r : ℝ => t₀ • F (w (t₀ * r))) MeasureTheory.volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    have hmem' : ∀ r ∈ Set.uIcc (0 : ℝ) σ, w (t₀ * r) ∈ W := by
      intro r hr
      rw [Set.uIcc_of_le hle] at hr
      exact hWmem _ (t_mul_mem_Ioo ha hb ht₀ ⟨hr.1, le_trans hr.2 hσ.2⟩)
    exact (hFc.comp hcontu hmem').const_smul t₀
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
    (fun r hr => hderiv' r ⟨le_of_lt hr.1, le_of_lt hr.2⟩) hint
  rw [h, mul_zero]

end Rescale

/-- The `exp(lam σ)`-scaled derivative of `Gflat` in the `(t,y)` direction. -/
lemma fderiv_Gflat_snd (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) {σ t : ℝ} {y : E} (hy : Real.exp (lam * σ) • y ∈ W) (v : E) :
    fderiv ℝ (fun q : ℝ × E => Gflat lam F (σ, q)) (t, y) (0, v)
      = t • fderiv ℝ F (Real.exp (lam * σ) • y) (Real.exp (lam * σ) • v) := by
  have hdF : DifferentiableAt ℝ F (Real.exp (lam * σ) • y) :=
    (hF.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)
  have hA : HasFDerivAt (fun q : ℝ × E => (((q.1 : ℝ)), Real.exp (lam * σ) • q.2))
      ((ContinuousLinearMap.fst ℝ ℝ E).prod
        (Real.exp (lam * σ) • ContinuousLinearMap.snd ℝ ℝ E)) (t, y) :=
    (hasFDerivAt_fst (p := (t, y))).prodMk
      ((hasFDerivAt_snd (p := (t, y))).const_smul (Real.exp (lam * σ)))
  have hP : HasFDerivAt (fun p : ℝ × E => p.1 • F p.2)
      (t • ((fderiv ℝ F (Real.exp (lam * σ) • y)).comp (ContinuousLinearMap.snd ℝ ℝ E))
        + (ContinuousLinearMap.fst ℝ ℝ E).smulRight (F (Real.exp (lam * σ) • y)))
      (t, Real.exp (lam * σ) • y) := by
    have hf : HasFDerivAt (fun p : ℝ × E => p.1) (ContinuousLinearMap.fst ℝ ℝ E)
        (t, Real.exp (lam * σ) • y) := hasFDerivAt_fst
    have hg : HasFDerivAt (fun p : ℝ × E => F p.2)
        ((fderiv ℝ F (Real.exp (lam * σ) • y)).comp (ContinuousLinearMap.snd ℝ ℝ E))
        (t, Real.exp (lam * σ) • y) :=
      hdF.hasFDerivAt.comp (t, Real.exp (lam * σ) • y)
        (hasFDerivAt_snd (p := (t, Real.exp (lam * σ) • y)))
    exact hf.smul hg
  have hcomp := hP.comp (t, y) hA
  have hfun : (fun q : ℝ × E => Gflat lam F (σ, q))
      = (fun p : ℝ × E => p.1 • F p.2) ∘ (fun q : ℝ × E => (((q.1 : ℝ)), Real.exp (lam * σ) • q.2)) := rfl
  rw [hfun, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.prod_apply]
  simp

/-- Chain rule identifying the second-variable derivative of `Gflat`. -/
lemma fderiv_snd_eq_loc (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) {σ t : ℝ} {y : E} (hy : Real.exp (lam * σ) • y ∈ W) :
    fderiv ℝ (fun q : ℝ × E => Gflat lam F (σ, q)) (t, y)
      = (fderiv ℝ (Gflat lam F) (σ, (t, y))).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)) := by
  have hmem : (σ, (t, y)) ∈ Vgood lam W := hy
  have hd : HasFDerivAt (Gflat lam F) (fderiv ℝ (Gflat lam F) (σ, (t, y))) (σ, (t, y)) :=
    ((Gflat_contDiffOn lam hW hF).contDiffAt ((Vgood_isOpen lam hW).mem_nhds hmem)).differentiableAt
      (by simp) |>.hasFDerivAt
  have hg : HasFDerivAt (fun q : ℝ × E => (σ, q)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)) (t, y) :=
    hasFDerivAt_prodMk_right σ (t, y)
  exact (hd.comp (t, y) hg).fderiv

/-- Evaluation of the `Xc` curve on a vertical increment. -/
lemma Xc_apply (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) {σ t : ℝ} {y : E} (hy : Real.exp (lam * σ) • y ∈ W) (v : E) :
    (fderiv ℝ (Gflat lam F) (σ, (t, y))).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)) ((0 : ℝ), v)
      = t • fderiv ℝ F (Real.exp (lam * σ) • y) (Real.exp (lam * σ) • v) := by
  rw [← fderiv_snd_eq_loc lam hW hF hy]
  exact fderiv_Gflat_snd lam hW hF hy v

/-- The set of `((x,t), γ)` for which the curve `σ ↦ (t, γ σ)` is good. -/
noncomputable def PGood (lam : ℝ) (W : Set E) : Set ((E × ℝ) × C(K, E)) :=
  {p | ∀ σ : K, Real.exp (lam * (σ : ℝ)) • (p.2 σ) ∈ W}

noncomputable def locPhieq (lam : ℝ) {W : Set E} (hW : IsOpen W) (F : E → E) :
    (E × ℝ) × C(K, E) → C(K, E) :=
  fun p => Mlam (E := E) lam (IntCLM (locNem lam hW F (comb lam (p.1.2, p.2))))

noncomputable def locFeq (lam : ℝ) {W : Set E} (hW : IsOpen W) (F : E → E) :
    (E × ℝ) × C(K, E) → C(K, E) :=
  fun p => p.2 - Mlam (E := E) lam (constCLM p.1.1) - locPhieq lam hW F p

lemma comb_mem_Good {lam : ℝ} {W : Set E} {p : (E × ℝ) × C(K, E)}
    (hp : p ∈ PGood lam W) : comb lam (p.1.2, p.2) ∈ Good lam W := by
  intro σ
  simpa [comb_apply, Good] using hp σ

lemma locPhieq_contDiffOn (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) : ContDiffOn ℝ ∞ (locPhieq lam hW F) (PGood lam W) := by
  have hcombu : ContDiffOn ℝ ∞ (fun p : (E × ℝ) × C(K, E) => comb lam (p.1.2, p.2))
      Set.univ := by fun_prop
  have hcomb := hcombu.mono (Set.subset_univ (PGood lam W))
  have h1 : ContDiffOn ℝ ∞
      (fun p : (E × ℝ) × C(K, E) => locNem lam hW F (comb lam (p.1.2, p.2))) (PGood lam W) :=
    (locNem_contDiffOn lam hW hF).comp hcomb (fun p hp => comb_mem_Good hp)
  have h2 : ContDiffOn ℝ ∞
      (fun p : (E × ℝ) × C(K, E) => IntCLM (locNem lam hW F (comb lam (p.1.2, p.2))))
      (PGood lam W) :=
    ((IntCLM (E := E)).contDiff.contDiffOn).comp h1 (fun x _ => Set.mem_univ _)
  have h3 : ContDiffOn ℝ ∞
      (fun p : (E × ℝ) × C(K, E) =>
        Mlam (E := E) lam (IntCLM (locNem lam hW F (comb lam (p.1.2, p.2)))))
      (PGood lam W) :=
    ((Mlam (E := E) lam).contDiff.contDiffOn).comp h2 (fun x _ => Set.mem_univ _)
  change ContDiffOn ℝ ∞
      (fun p : (E × ℝ) × C(K, E) =>
        Mlam (E := E) lam (IntCLM (locNem lam hW F (comb lam (p.1.2, p.2)))))
      (PGood lam W)
  exact h3

lemma locFeq_contDiffOn (lam : ℝ) {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F W) : ContDiffOn ℝ ∞ (locFeq lam hW F) (PGood lam W) := by
  have h1 := locPhieq_contDiffOn lam hW hF
  have h2 : ContDiffOn ℝ ∞ (fun p : (E × ℝ) × C(K, E) => Mlam (E := E) lam (constCLM p.1.1))
      (PGood lam W) := by
    refine ((Mlam (E := E) lam).contDiff.contDiffOn).comp ?_ (fun x _ => Set.mem_univ _)
    fun_prop
  have h3 : ContDiffOn ℝ ∞ (fun p : (E × ℝ) × C(K, E) => p.2) (PGood lam W) := by fun_prop
  change ContDiffOn ℝ ∞
      (fun p : (E × ℝ) × C(K, E) => p.2 - Mlam (E := E) lam (constCLM p.1.1)
        - locPhieq lam hW F p) (PGood lam W)
  exact (h3.sub h2).sub h1

/-- If `σ ↦ e^{lam σ} • γ σ` maps `K` into the open set `W`, then curves close enough to `γ` in the
sup norm satisfy `e^{lam σ} • g σ ∈ W` for every `σ ∈ K`. -/
lemma eventually_good (lam : ℝ) {W : Set E} (hW : IsOpen W) {γ : C(K, E)}
    (hγW : ∀ σ : K, Real.exp (lam * (σ : ℝ)) • γ σ ∈ W) (hlam : 0 < lam) :
    ∀ᶠ g : C(K, E) in nhds γ, ∀ σ : K, Real.exp (lam * (σ : ℝ)) • g σ ∈ W := by
  have hcont : Continuous fun σ : K => Real.exp (lam * (σ : ℝ)) • γ σ := by fun_prop
  obtain ⟨ε, hεpos, hεW⟩ := (isCompact_range hcont).exists_thickening_subset_open hW
    (fun z ⟨σ, hσ⟩ => hσ ▸ hγW σ)
  filter_upwards [Metric.ball_mem_nhds γ (by positivity : 0 < ε * Real.exp (-lam))] with g hg
  rw [Metric.mem_ball] at hg
  intro σ
  apply hεW
  rw [Metric.mem_thickening_iff]
  refine ⟨Real.exp (lam * (σ : ℝ)) • γ σ, ⟨σ, rfl⟩, ?_⟩
  have hexp_le : Real.exp (lam * (σ : ℝ)) ≤ Real.exp lam :=
    Real.exp_le_exp.mpr (by simpa using mul_le_of_le_one_right hlam.le σ.2.2)
  have hdist2 : ‖g σ - γ σ‖ < ε * Real.exp (-lam) := by
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist σ) hg
  have hprod : Real.exp (lam * (σ : ℝ)) * ‖g σ - γ σ‖ < ε := by
    calc Real.exp (lam * (σ : ℝ)) * ‖g σ - γ σ‖
        ≤ Real.exp lam * ‖g σ - γ σ‖ :=
          mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
      _ < Real.exp lam * (ε * Real.exp (-lam)) :=
          mul_lt_mul_of_pos_left hdist2 (Real.exp_pos lam)
      _ = ε := by
          rw [← mul_assoc, mul_comm (Real.exp lam) ε, mul_assoc, ← Real.exp_add, add_neg_cancel,
            Real.exp_zero, mul_one]
  calc dist (Real.exp (lam * (σ : ℝ)) • g σ) (Real.exp (lam * (σ : ℝ)) • γ σ)
      = Real.exp (lam * (σ : ℝ)) * ‖g σ - γ σ‖ := by
        rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ < ε := hprod

theorem contDiffAt_solutionMap_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {W : Set E} (hW : IsOpen W) {F : E → E}
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F W)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {u : E → ℝ → E} {x₀ : E}
    (h0 : ∀ᶠ x in nhds x₀, u x 0 = x)
    (hode : ∀ᶠ x in nhds x₀, ∀ t ∈ Set.Ioo a b, HasDerivAt (u x) (F (u x t)) t)
    (hmem : ∀ᶠ x in nhds x₀, ∀ t ∈ Set.Ioo a b, u x t ∈ W)
    (huniq : ∀ᶠ x in nhds x₀, ∀ y : ℝ → E, (∀ t ∈ Set.Ioo a b, HasDerivAt y (F (y t)) t) →
      y 0 = x → ∀ t ∈ Set.Ioo a b, y t = u x t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × ℝ => u p.1 p.2) (x₀, t₀) := by
  classical
  have hF' : ContDiffOn ℝ ∞ F W := by simpa using hF
  obtain ⟨S, hSmem, hS⟩ :=
    Filter.eventually_iff_exists_mem.mp (h0.and (hode.and (hmem.and huniq)))
  have hx₀S : x₀ ∈ S := mem_of_mem_nhds hSmem
  have hu0x₀ : u x₀ 0 = x₀ := (hS x₀ hx₀S).1
  have hodex₀ : ∀ t ∈ Set.Ioo a b, HasDerivAt (u x₀) (F (u x₀ t)) t := (hS x₀ hx₀S).2.1
  have hmemx₀ : ∀ t ∈ Set.Ioo a b, u x₀ t ∈ W := (hS x₀ hx₀S).2.2.1
  have hx₀W : x₀ ∈ W := by
    have h := hmemx₀ 0 ⟨ha, hb⟩
    rwa [hu0x₀] at h
  -- the model trajectory
  set γ₀ : C(K, E) :=
    ⟨fun σ => u x₀ (t₀ * (σ : ℝ)), continuous_rescale_pt ha hb ht₀ hodex₀⟩ with hγ₀def
  have hγ₀ : ∀ σ : K, γ₀ σ = u x₀ (t₀ * (σ : ℝ)) := fun σ => rfl
  have hγ₀W : ∀ σ : K, γ₀ σ ∈ W := by
    intro σ
    rw [hγ₀]
    exact hmemx₀ _ (t_mul_mem_Ioo ha hb ht₀ σ.2)
  have hDccont : Continuous fun σ : K => fderiv ℝ F (γ₀ σ) :=
    (hF'.continuousOn_fderiv_of_isOpen hW (by simp)).comp_continuous γ₀.continuous hγ₀W
  set Dc : C(K, E →L[ℝ] E) := ⟨fun σ => fderiv ℝ F (γ₀ σ), hDccont⟩ with hDcdef
  set C₀ : ℝ := ‖Dc‖ with hC₀def
  have hDcbound : ∀ σ : K, ‖fderiv ℝ F (γ₀ σ)‖ ≤ C₀ :=
    fun σ => ContinuousMap.norm_coe_le_norm Dc σ
  have hC₀nn : 0 ≤ C₀ := hC₀def.symm ▸ norm_nonneg Dc
  set lam : ℝ := 1 + |t₀| * C₀ with hlamdef
  have hlam_pos : 0 < lam := by rw [hlamdef]; positivity
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlam_gt : |t₀| * C₀ < lam := by rw [hlamdef]; linarith
  set η₀ : C(K, E) := Mlam (E := E) lam γ₀ with hη₀def
  have hη₀rel : ∀ σ : K, Real.exp (lam * (σ : ℝ)) • η₀ σ = γ₀ σ := by
    intro σ
    rw [hη₀def, Mlam_apply]
    rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  set u0 : E × ℝ := (x₀, t₀) with hu0def
  set p₀ : (E × ℝ) × C(K, E) := (u0, η₀) with hp₀def
  have hgoodC : ∀ τ : K, Real.exp (lam * (τ : ℝ)) • ((comb lam (t₀, η₀)) τ).2 ∈ W := by
    intro τ
    rw [comb_apply]
    rw [hη₀rel τ]
    exact hγ₀W τ
  have hbase : locFeq lam hW F p₀ = 0 := by
    ext σ
    have h1 : (locFeq lam hW F p₀) σ
        = η₀ σ - Real.exp (-(lam * (σ : ℝ))) • x₀
          - Real.exp (-(lam * (σ : ℝ))) • ∫ r in (0 : ℝ)..(σ : ℝ),
              (locNem lam hW F (comb lam (t₀, η₀))) (clampK r) := by
      simp only [locFeq, locPhieq, ContinuousMap.sub_apply, Mlam_apply, constCLM_apply,
        IntCLM_apply, hp₀def, hu0def]
    rw [h1]
    have hcongr : ∫ r in (0 : ℝ)..(σ : ℝ),
          (locNem lam hW F (comb lam (t₀, η₀))) (clampK r)
        = ∫ r in (0 : ℝ)..(σ : ℝ), t₀ • F (u x₀ (t₀ * r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le σ.2.1] at hr
      have hrK : r ∈ K := ⟨hr.1, le_trans hr.2 σ.2.2⟩
      show (locNem lam hW F (comb lam (t₀, η₀))) (clampK r) = t₀ • F (u x₀ (t₀ * r))
      rw [locNem_apply lam hW hF' hgoodC (clampK r), comb_apply, clampK_of_mem hrK]
      simp only [Gflat]
      rw [hη₀rel ⟨r, hrK⟩, hγ₀ ⟨r, hrK⟩]
    rw [hcongr, integral_rescale_pt ha hb ht₀ hodex₀ hmemx₀ hF'.continuousOn σ.2, hu0x₀]
    rw [hη₀def, Mlam_apply, hγ₀ σ]
    simp only [ContinuousMap.zero_apply]
    rw [smul_sub]
    abel
  have hη₀rel' : ∀ (r : ℝ) (hr : r ∈ K),
      Real.exp (lam * r) • η₀ ⟨r, hr⟩ = γ₀ ⟨r, hr⟩ := by
    intro r hr
    simpa using hη₀rel ⟨r, hr⟩
  have hXccont : Continuous fun σ : K =>
      (fderiv ℝ (Gflat lam F) (((σ : ℝ)), (comb lam (t₀, η₀)) σ)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)) :=
    (((Gflat_contDiffOn lam hW hF').continuousOn_fderiv_of_isOpen
        (Vgood_isOpen lam hW) (by simp)).comp_continuous
      (continuous_subtype_val.prodMk (comb lam (t₀, η₀)).continuous) (by
        intro σ
        show Real.exp (lam * (σ : ℝ)) • η₀ σ ∈ W
        rw [hη₀rel σ]
        exact hγ₀W σ)).clm_comp
      (continuous_const : Continuous fun _ : K => (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)))
  set Xc : C(K, (ℝ × E) →L[ℝ] E) :=
    ⟨fun σ => (fderiv ℝ (Gflat lam F) (((σ : ℝ)), (comb lam (t₀, η₀)) σ)).comp
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × E)), hXccont⟩ with hXcdef
  set A : C(K, E) →L[ℝ] C(K, E) :=
    (Mlam (E := E) lam).comp (IntCLM.comp ((mulClm (E := ℝ × E) (G := E) Xc).comp (emb lam)))
    with hAdef
  have hA_has : HasFDerivAt (fun η : C(K, E) => locPhieq lam hW F (u0, η)) A η₀ := by
    have hinr : HasFDerivAt (fun η : C(K, E) => (t₀, η))
        (ContinuousLinearMap.inr ℝ ℝ C(K, E)) η₀ :=
      (hasFDerivAt_const (𝕜 := ℝ) (x := η₀) (c := t₀)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (x := η₀))
    have hcomb2 : HasFDerivAt (fun η : C(K, E) => comb lam (t₀, η)) (emb lam) η₀ := by
      have hh1 := (comb (E := E) lam).hasFDerivAt.comp η₀ hinr
      simpa only [emb, Function.comp_def] using hh1
    have hnem : HasFDerivAt (locNem lam hW F)
        (mulClm (E := ℝ × E) (G := E) Xc) (comb lam (t₀, η₀)) :=
      locNem_hasFDerivAt lam hW hF' hgoodC
    have h4 := hnem.comp η₀ hcomb2
    have h5 := (IntCLM (E := E)).hasFDerivAt.comp η₀ h4
    have h6 := (Mlam (E := E) lam).hasFDerivAt.comp η₀ h5
    simpa only [A, locPhieq, Function.comp_def, hu0def, hAdef, hXcdef] using h6
  have hA_pt : ∀ δ : C(K, E), ‖A δ‖ ≤ (|t₀| * C₀ / lam) * ‖δ‖ := by
    intro δ
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro σ
    have hAap : (A δ) σ = Real.exp (-(lam * (σ : ℝ))) • ∫ r in (0 : ℝ)..(σ : ℝ),
        Xc (clampK r) ((emb lam δ) (clampK r)) := by
      simp only [A, hAdef, ContinuousLinearMap.comp_apply, Mlam_apply, IntCLM_apply,
        mulClm_apply, mulLin_apply]
    rw [hAap, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hint : IntervalIntegrable (fun r : ℝ => |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖)
        MeasureTheory.volume 0 (σ : ℝ) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hle : ‖∫ r in (0 : ℝ)..(σ : ℝ), Xc (clampK r) ((emb lam δ) (clampK r))‖
        ≤ ∫ r in (0 : ℝ)..(σ : ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le σ.2.1
      · filter_upwards with r hr
        have hrK : r ∈ K := ⟨le_of_lt hr.1, le_trans hr.2 σ.2.2⟩
        have hmemr : Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r) ∈ W := by
          rw [hη₀rel (clampK r)]
          exact hγ₀W (clampK r)
        have hXc : Xc (clampK r) ((emb lam δ) (clampK r))
            = t₀ • fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r))
                (Real.exp (lam * ((clampK r : K) : ℝ)) • δ (clampK r)) := by
          simp only [Xc, hXcdef, emb_apply, comb_apply]
          exact Xc_apply lam hW hF' hmemr (δ (clampK r))
        rw [hXc]
        have h1 : ‖fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r))‖ ≤ C₀ := by
          rw [hη₀rel (clampK r)]
          exact hDcbound (clampK r)
        have h2 : ‖δ (clampK r)‖ ≤ ‖δ‖ := ContinuousMap.norm_coe_le_norm δ (clampK r)
        have hnorm : ‖(fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r)))
            (Real.exp (lam * ((clampK r : K) : ℝ)) • δ (clampK r))‖
            ≤ Real.exp (lam * ((clampK r : K) : ℝ)) * (C₀ * ‖δ‖) := by
          calc ‖(fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r)))
                (Real.exp (lam * ((clampK r : K) : ℝ)) • δ (clampK r))‖
              ≤ ‖fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r))‖
                  * ‖Real.exp (lam * ((clampK r : K) : ℝ)) • δ (clampK r)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ = ‖fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r))‖
                  * (Real.exp (lam * ((clampK r : K) : ℝ)) * ‖δ (clampK r)‖) := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            _ ≤ C₀ * (Real.exp (lam * ((clampK r : K) : ℝ)) * ‖δ‖) :=
                mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos _)))
                  (by positivity) hC₀nn
            _ = Real.exp (lam * ((clampK r : K) : ℝ)) * (C₀ * ‖δ‖) := by ring
        calc ‖t₀ • (fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r)))
              (Real.exp (lam * ((clampK r : K) : ℝ)) • δ (clampK r))‖
            = |t₀| * ‖(fderiv ℝ F (Real.exp (lam * ((clampK r : K) : ℝ)) • η₀ (clampK r)))
              (Real.exp (lam * ((clampK r : K) : ℝ)) • δ (clampK r))‖ := by
                rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |t₀| * (Real.exp (lam * ((clampK r : K) : ℝ)) * (C₀ * ‖δ‖)) :=
                mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
          _ = |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ := by
                rw [clampK_of_mem hrK]
                simp only [Subtype.coe_mk]
                ring
      · exact hint
    have hInt : ∫ r in (0 : ℝ)..(σ : ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖
        = |t₀| * C₀ * (Real.exp (lam * (σ : ℝ)) - 1) / lam * ‖δ‖ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_exp_mul lam hlam_ne 0 (σ : ℝ)]
      rw [mul_zero, Real.exp_zero]
      ring
    have hexp : Real.exp (-(lam * (σ : ℝ)))
        * (|t₀| * C₀ * (Real.exp (lam * (σ : ℝ)) - 1) / lam * ‖δ‖)
        = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ : ℝ)))) / lam * ‖δ‖ := by
      have hh1 : Real.exp (-(lam * (σ : ℝ))) * Real.exp (lam * (σ : ℝ)) = 1 := by
        rw [← Real.exp_add]
        have hh2 : -(lam * (σ : ℝ)) + lam * (σ : ℝ) = 0 := by ring
        rw [hh2, Real.exp_zero]
      calc Real.exp (-(lam * (σ : ℝ)))
            * (|t₀| * C₀ * (Real.exp (lam * (σ : ℝ)) - 1) / lam * ‖δ‖)
          = (Real.exp (-(lam * (σ : ℝ))) * (Real.exp (lam * (σ : ℝ)) - 1))
              * (|t₀| * C₀ / lam * ‖δ‖) := by ring
        _ = (1 - Real.exp (-(lam * (σ : ℝ)))) * (|t₀| * C₀ / lam * ‖δ‖) := by
              rw [mul_sub, hh1, mul_one]
        _ = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ : ℝ)))) / lam * ‖δ‖ := by ring
    have h10 : |t₀| * C₀ * (1 - Real.exp (-(lam * (σ : ℝ)))) / lam * ‖δ‖
        ≤ |t₀| * C₀ / lam * ‖δ‖ := by
      have h12 : (1 - Real.exp (-(lam * (σ : ℝ)))) ≤ 1 := by
        have := Real.exp_pos (-(lam * (σ : ℝ))); linarith
      have h13 : 0 ≤ |t₀| * C₀ := mul_nonneg (abs_nonneg t₀) hC₀nn
      have h14 : 0 ≤ ‖δ‖ := norm_nonneg _
      have hh1 : |t₀| * C₀ * (1 - Real.exp (-(lam * (σ : ℝ)))) / lam ≤ |t₀| * C₀ / lam := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hlam_pos)
        exact mul_le_of_le_one_right h13 h12
      exact mul_le_mul_of_nonneg_right hh1 h14
    calc Real.exp (-(lam * (σ : ℝ)))
          * ‖∫ r in (0 : ℝ)..(σ : ℝ), Xc (clampK r) ((emb lam δ) (clampK r))‖
        ≤ Real.exp (-(lam * (σ : ℝ)))
          * ∫ r in (0 : ℝ)..(σ : ℝ), |t₀| * C₀ * Real.exp (lam * r) * ‖δ‖ :=
          mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(lam * (σ : ℝ)))
            * (|t₀| * C₀ * (Real.exp (lam * (σ : ℝ)) - 1) / lam * ‖δ‖) := by rw [hInt]
      _ = |t₀| * C₀ * (1 - Real.exp (-(lam * (σ : ℝ)))) / lam * ‖δ‖ := hexp
      _ ≤ |t₀| * C₀ / lam * ‖δ‖ := h10
  have hA_bound : ‖A‖ ≤ |t₀| * C₀ / lam :=
    ContinuousLinearMap.opNorm_le_bound A (by positivity) hA_pt
  have hA_lt : ‖A‖ < 1 := by
    have h1 : |t₀| * C₀ / lam < 1 := by
      rw [div_lt_one hlam_pos]; exact hlam_gt
    linarith
  have hsub : HasFDerivAt (fun η : C(K, E) => locFeq lam hW F (u0, η)) (1 - A) η₀ := by
    have h1 : HasFDerivAt (fun η : C(K, E) => η) (1 : C(K, E) →L[ℝ] C(K, E)) η₀ :=
      hasFDerivAt_id (𝕜 := ℝ) (x := η₀)
    have h2 : HasFDerivAt (fun _ : C(K, E) => Mlam (E := E) lam (constCLM (u0).1)) 0 η₀ :=
      hasFDerivAt_const (𝕜 := ℝ) (x := η₀) (c := Mlam (E := E) lam (constCLM (u0).1))
    have h3 := (h1.sub h2).sub hA_has
    have heq : (fun η : C(K, E) => locFeq lam hW F (u0, η))
        = ((fun η : C(K, E) => η) - (fun _ : C(K, E) => Mlam (E := E) lam (constCLM (u0).1))
           - (fun η : C(K, E) => locPhieq lam hW F (u0, η))) := by
      funext η
      simp only [locFeq, Pi.sub_apply]
    rw [heq]
    simpa only [sub_zero] using h3
  have hp₀mem : p₀ ∈ PGood lam W := by
    intro σ
    rw [hη₀rel σ]
    exact hγ₀W σ
  have hPGood_nhds : PGood lam W ∈ nhds p₀ := by
    have h1 : ∀ᶠ g : C(K, E) in nhds η₀, ∀ σ : K, Real.exp (lam * (σ : ℝ)) • g σ ∈ W :=
      eventually_good lam hW (γ := η₀) (fun σ : K => by rw [hη₀rel σ]; exact hγ₀W σ) hlam_pos
    have hp2 : Tendsto (fun p : (E × ℝ) × C(K, E) => p.2) (𝓝 p₀) (𝓝 η₀) :=
      continuous_snd.tendsto p₀
    exact hp2 h1
  have hFeq_at : HasFDerivAt (locFeq lam hW F) (fderiv ℝ (locFeq lam hW F) p₀) p₀ :=
    ((locFeq_contDiffOn lam hW hF').contDiffAt hPGood_nhds).differentiableAt (by simp) |>.hasFDerivAt
  have hinr2 : HasFDerivAt (fun η : C(K, E) => (u0, η))
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(K, E)) η₀ :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := η₀) (c := u0)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (x := η₀))
  have hcomp := hFeq_at.comp η₀ hinr2
  have hEq : ((fderiv ℝ (locFeq lam hW F) p₀) ∘L ContinuousLinearMap.inr ℝ (E × ℝ) C(K, E))
      = 1 - A := by
    rw [← hcomp.fderiv]
    exact hsub.fderiv
  have hif : ((fderiv ℝ (locFeq lam hW F) p₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) C(K, E)).IsInvertible := by
    rw [hEq]
    exact isInvertible_one_sub A hA_lt
  have hFeq_cd : ContDiffAt ℝ ∞ (locFeq lam hW F) p₀ :=
    (locFeq_contDiffOn lam hW hF').contDiffAt hPGood_nhds
  let ψ : E × ℝ → C(K, E) := hFeq_cd.implicitFunction (by simp) hif
  have hψ_cd : ContDiffAt ℝ ∞ ψ u0 := hFeq_cd.contDiffAt_implicitFunction (by simp) hif
  have hψ0 : ψ u0 = η₀ := hFeq_cd.implicitFunction_apply_self (by simp) hif
  have hev : ∀ᶠ y in 𝓝 u0, locFeq lam hW F (y, ψ y) = locFeq lam hW F p₀ :=
    hFeq_cd.eventually_apply_implicitFunction (by simp) hif
  have key : ∀ᶠ y in 𝓝 u0, u y.1 y.2 = Real.exp lam • (ψ y) ⟨1, by norm_num⟩ := by
    have hS_ev : ∀ᶠ y : E × ℝ in 𝓝 u0, y.1 ∈ S :=
      (continuous_fst.tendsto u0).eventually hSmem
    have hmem_ev : ∀ᶠ y : E × ℝ in 𝓝 u0, y.2 ∈ Set.Ioo a b :=
      (isOpen_Ioo.preimage continuous_snd).mem_nhds (by rw [hu0def]; exact ht₀)
    have hgood_ev : ∀ᶠ y : E × ℝ in 𝓝 u0, ∀ σ : K, Real.exp (lam * (σ : ℝ)) • (ψ y σ) ∈ W := by
      obtain ⟨ε, hεpos, hεW⟩ := (isCompact_range γ₀.continuous).exists_thickening_subset_open hW
        (fun z ⟨σ, hσ⟩ => hσ ▸ hγ₀W σ)
      have hgoodη : ∀ᶠ g : C(K, E) in nhds η₀,
          ∀ σ : K, Real.exp (lam * (σ : ℝ)) • g σ ∈ W :=
        eventually_good lam hW (γ := η₀) (fun σ : K => by rw [hη₀rel σ]; exact hγ₀W σ) hlam_pos
      have hcont : Tendsto ψ (𝓝 u0) (𝓝 η₀) := by
        rw [← hψ0]
        exact hψ_cd.continuousAt
      exact hcont hgoodη
    filter_upwards [hev, hS_ev, hmem_ev, hgood_ev] with y hy hyS hyab hgoody
    have h0y : u y.1 0 = y.1 := (hS y.1 hyS).1
    have hodey : ∀ t ∈ Set.Ioo a b, HasDerivAt (u y.1) (F (u y.1 t)) t := (hS y.1 hyS).2.1
    rw [hbase] at hy
    set Wc : C(K, E) := ψ y with hWcdef
    have hgoodc : ∀ σ : K, Real.exp (lam * (σ : ℝ)) • ((comb lam (y.2, Wc)) σ).2 ∈ W := by
      intro σ
      rw [comb_apply]
      exact hgoody σ
    have hint_eq : ∀ σ : K, Wc σ = Real.exp (-(lam * (σ : ℝ))) • (y.1 + ∫ r in (0 : ℝ)..(σ : ℝ),
        locNem lam hW F (comb lam (y.2, Wc)) (clampK r)) := by
      intro σ
      have h := congrArg (fun w : C(K, E) => w σ) hy
      simp only [locFeq, locPhieq, ContinuousMap.sub_apply, ContinuousMap.zero_apply, Mlam_apply,
        constCLM_apply, IntCLM_apply, hWcdef] at h
      rw [smul_add]
      have h1 : Wc σ - Real.exp (-(lam * (σ : ℝ))) • y.1
          = Real.exp (-(lam * (σ : ℝ))) • (∫ r in (0 : ℝ)..(σ : ℝ),
              locNem lam hW F (comb lam (y.2, Wc)) (clampK r)) := sub_eq_zero.mp h
      rw [sub_eq_iff_eq_add] at h1
      rw [h1, add_comm]
    set GR : ℝ → E := fun r => Real.exp (lam * r) • Wc (clampK r) with hGRdef
    have hGR_cont : Continuous GR := by
      rw [hGRdef]
      exact (by fun_prop : Continuous fun r : ℝ => Real.exp (lam * r)).smul
        (Wc.continuous.comp continuous_clampK)
    have hnem_apply : ∀ r : ℝ,
        locNem lam hW F (comb lam (y.2, Wc)) (clampK r) = y.2 • F (GR (clampK r)) := by
      intro r
      rw [locNem_apply lam hW hF' hgoodc (clampK r), comb_apply]
      simp only [Gflat]
      congr 1
      simp only [hGRdef, clampK_coe]
    have hGRint_eq0 : ∀ r ∈ K, y.1 + ∫ s in (0 : ℝ)..r,
        y.2 • F (GR (clampK s)) = GR r := by
      intro r hr
      have hint : ∫ s in (0 : ℝ)..r, locNem lam hW F (comb lam (y.2, Wc)) (clampK s)
          = ∫ s in (0 : ℝ)..r, y.2 • F (GR (clampK s)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact hnem_apply s
      have h2 : Real.exp (lam * r) • Wc ⟨r, hr⟩
          = y.1 + ∫ s in (0 : ℝ)..r, locNem lam hW F (comb lam (y.2, Wc)) (clampK s) := by
        have h := congrArg (fun z => Real.exp (lam * r) • z) (hint_eq ⟨r, hr⟩)
        rw [smul_smul] at h
        have h3 : Real.exp (lam * r) * Real.exp (-(lam * ((⟨r, hr⟩ : K) : ℝ))) = 1 := by
          rw [← Real.exp_add]
          have h4 : lam * r + -(lam * ((⟨r, hr⟩ : K) : ℝ)) = 0 := by push_cast; ring
          rw [h4, Real.exp_zero]
        rw [h3, one_smul] at h
        exact h
      have hGRr : GR r = Real.exp (lam * r) • Wc ⟨r, hr⟩ := by
        simp only [hGRdef, clampK_of_mem hr]
      rw [← hint, ← h2, hGRr]
    have hGRW : ∀ σ : K, GR (σ : ℝ) ∈ W := by
      intro σ
      simpa only [hGRdef, clampK_coe] using hgoody σ
    set GRint : ℝ → E := fun r => y.1 + ∫ s in (0 : ℝ)..r, y.2 • F (GR (clampK s))
      with hGRintdef
    have hGRint_eq : ∀ r ∈ K, GRint r = GR r := by
      intro r hr
      rw [hGRintdef]
      exact hGRint_eq0 r hr
    have hGRK : Continuous fun s : ℝ => GR (clampK s) :=
      hGR_cont.comp (continuous_subtype_val.comp continuous_clampK)
    have hGF : Continuous fun s : ℝ => y.2 • F (GR (clampK s)) :=
      continuous_const.smul (hF'.continuousOn.comp_continuous hGRK (fun s => hGRW (clampK s)))
    have hGRint_deriv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt GRint (y.2 • F (GRint r)) r := by
      intro r hr
      have hrK : r ∈ K := ⟨hr.1, hr.2⟩
      have h3 := intervalIntegral.integral_hasDerivAt_right (hGF.intervalIntegrable 0 r)
        (hGF.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 r)) hGF.continuousAt
      have h2 : HasDerivAt (fun r' => y.1 + ∫ s in (0 : ℝ)..r', y.2 • F (GR (clampK s)))
          (y.2 • F (GR (clampK r))) r := by
        simpa using h3.const_add y.1
      have hval : y.2 • F (GR (clampK r)) = y.2 • F (GRint r) := by
        rw [hGRint_eq r hrK, clampK_of_mem hrK]
      rw [hval] at h2
      rwa [hGRintdef]
    have hgr_deriv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun r : ℝ => u y.1 (y.2 * r)) (y.2 • F (u y.1 (y.2 * r))) r := by
      intro r hr
      have h1 : HasDerivAt (fun r : ℝ => y.2 * r) y.2 r := hasDerivAt_const_mul y.2
      have h2 : HasDerivAt (u y.1) (F (u y.1 (y.2 * r))) (y.2 * r) :=
        hodey (y.2 * r) (t_mul_mem_Ioo ha hb hyab ⟨hr.1, hr.2⟩)
      exact h2.scomp r h1
    have hloc : ∀ r ∈ Set.Icc (0 : ℝ) 1,
        ∃ K' : NNReal, ∃ U ∈ nhds (GRint r), LipschitzOnWith K' (fun z : E => y.2 • F z) U := by
      intro r hr
      have hrK : r ∈ K := ⟨hr.1, hr.2⟩
      have hmemWr : GRint r ∈ W := by
        rw [hGRint_eq r hrK]
        exact hGRW ⟨r, hrK⟩
      exact (((hF'.contDiffAt (hW.mem_nhds hmemWr)).of_le (by norm_num)).const_smul
        y.2).exists_lipschitzOnWith
    have h0eq : GRint 0 = (fun r : ℝ => u y.1 (y.2 * r)) 0 := by
      rw [hGRintdef]
      simp [h0y]
    have hEqOn : Set.EqOn GRint (fun r : ℝ => u y.1 (y.2 * r)) (Set.Icc (0 : ℝ) 1) :=
      eqOn_of_hasDerivAt_of_locallyLipschitz (by norm_num) hGRint_deriv hgr_deriv hloc h0eq
    have hfin : GRint 1 = u y.1 y.2 := by
      simpa using hEqOn (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    have h1mem : (1 : ℝ) ∈ K := by norm_num
    rw [← hfin, hGRint_eq 1 h1mem, hGRdef]
    simp only [clampK_of_mem h1mem, mul_one, hWcdef]
  have hcd : ContDiffAt ℝ ∞ (fun p : E × ℝ => Real.exp lam • (ψ p) ⟨1, by norm_num⟩) u0 := by
    have h1 : ContDiffAt ℝ ∞ (fun p : E × ℝ => ψ p) u0 := hψ_cd
    have h2 : ContDiffAt ℝ ∞ (fun p : E × ℝ => (ψ p) ⟨1, by norm_num⟩) u0 := by
      have heval : ContDiff ℝ ∞ (fun w : C(K, E) => w ⟨1, by norm_num⟩) := by
        have hlin : IsBoundedLinearMap ℝ (fun w : C(K, E) => w ⟨1, by norm_num⟩) :=
          ⟨⟨fun a b => rfl, fun c a => rfl⟩, ⟨1, one_pos, fun w => by
            rw [one_mul]; exact ContinuousMap.norm_coe_le_norm w ⟨1, by norm_num⟩⟩⟩
        exact hlin.contDiff
      exact heval.contDiffAt.comp u0 h1
    exact (contDiffAt_const (c := Real.exp lam)).smul h2
  have hgoal : ContDiffAt ℝ ∞ (fun p : E × ℝ => u p.1 p.2) u0 :=
    hcd.congr_of_eventuallyEq key
  simpa only [hu0def] using hgoal



end

end Commons.Analysis.ODE
