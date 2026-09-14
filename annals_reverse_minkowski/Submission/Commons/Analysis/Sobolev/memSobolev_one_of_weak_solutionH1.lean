import Mathlib
import Submission.Commons.Analysis.Sobolev.memSobolev_one_of_laplacian_memSobolev_neg_one
import Submission.Commons.Analysis.Sobolev.locallyIntegrable_of_hasCompactSupport_memLp
import Submission.Commons.Analysis.Sobolev.integral_heatKernel_conv_mul_self

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Sobolev

open MeasureTheory
open scoped ENNReal ContDiff SchwartzMap Laplacian

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The complexification `a ↦ (x ↦ (a x : ℂ))` as a continuous `ℝ`-linear map. -/
noncomputable def cplxMap : 𝓢(E, ℝ) →L[ℝ] 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM

@[simp] lemma cplxMap_apply (a : 𝓢(E, ℝ)) (x : E) : cplxMap a x = ((a x : ℝ) : ℂ) := rfl

lemma fderiv_cplxMap (a : 𝓢(E, ℝ)) (x : E) :
    fderiv ℝ (⇑(cplxMap a)) x = (Complex.ofRealCLM).comp (fderiv ℝ (⇑a) x) := by
  have h : HasFDerivAt (⇑(cplxMap a)) ((Complex.ofRealCLM).comp (fderiv ℝ (⇑a) x)) x :=
    (ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM).comp x
      ((a.differentiableAt).hasFDerivAt)
  exact h.fderiv

lemma lineDerivOp_cplxMap (a : 𝓢(E, ℝ)) (m x : E) :
    (LineDeriv.lineDerivOp m (cplxMap a)) x = (((LineDeriv.lineDerivOp m a) x : ℝ) : ℂ) := by
  rw [SchwartzMap.lineDerivOp_apply, SchwartzMap.lineDerivOp_apply,
    ((cplxMap a).differentiableAt).lineDeriv_eq_fderiv,
    (a.differentiableAt).lineDeriv_eq_fderiv, fderiv_cplxMap]
  rfl

lemma laplacian_cplxMap (a : 𝓢(E, ℝ)) (x : E) :
    (Laplacian.laplacian (cplxMap a)) x = (((Laplacian.laplacian a) x : ℝ) : ℂ) := by
  rw [SchwartzMap.laplacian_apply, SchwartzMap.laplacian_apply]
  rw [show ⇑(cplxMap a) = Complex.ofRealCLM ∘ ⇑a from rfl]
  rw [ContDiffAt.laplacian_CLM_comp_left (f := ⇑a) (x := x) (l := Complex.ofRealCLM)
    (a.contDiffAt 2)]
  rfl

/-- A density statement: a tempered distribution vanishing on all complexified compactly supported
smooth real functions vanishes. -/
lemma eq_zero_of_vanishes_on_cplxMap
    (hDensity : ∀ T : TemperedDistribution E ℂ,
      (∀ θ : SchwartzMap E ℂ, HasCompactSupport (⇑θ) → T θ = 0) → T = 0)
    (T : TemperedDistribution E ℂ)
    (h : ∀ a : SchwartzMap E ℝ, HasCompactSupport (⇑a) → T (cplxMap a) = 0) : T = 0 := by
  refine hDensity T (fun θ hθ => ?_)
  have hre : HasCompactSupport (⇑(θ.postcompCLM Complex.reCLM) : E → ℝ) := by
    refine hθ.mono (fun x hx => ?_)
    simp only [Function.mem_support, SchwartzMap.postcompCLM_apply] at hx ⊢
    intro h; exact hx (by rw [h]; simp)
  have him : HasCompactSupport (⇑(θ.postcompCLM Complex.imCLM) : E → ℝ) := by
    refine hθ.mono (fun x hx => ?_)
    simp only [Function.mem_support, SchwartzMap.postcompCLM_apply] at hx ⊢
    intro h; exact hx (by rw [h]; simp)
  have hdec : θ = cplxMap (θ.postcompCLM Complex.reCLM)
      + Complex.I • cplxMap (θ.postcompCLM Complex.imCLM) := by
    ext x
    simp only [cplxMap_apply, add_apply, smul_apply, SchwartzMap.postcompCLM_apply, smul_eq_mul,
      Complex.reCLM_apply, Complex.imCLM_apply]
    rw [show Complex.I * ((θ x).im : ℂ) = ((θ x).im : ℂ) * Complex.I from mul_comm _ _]
    exact (Complex.re_add_im (θ x)).symm
  rw [hdec, map_add, map_smul, h _ hre, h _ him, smul_zero, add_zero]

/-- Evaluation of the tempered distribution attached to an `L²` function. -/
lemma Lp_toTemperedDistribution_apply' {f : E → ℂ} (hf : MemLp f 2 (volume : Measure E))
    (θ : 𝓢(E, ℂ)) :
    (↑(hf.toLp f) : TemperedDistribution E ℂ) θ = ∫ x, θ x * f x := by
  rw [MeasureTheory.Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, smul_eq_mul]

/-- The distributional line derivative is the negative adjoint of the classical one. -/
lemma lineDerivOp_apply_tempered (T : TemperedDistribution E ℂ) (m : E) (θ : 𝓢(E, ℂ)) :
    (LineDeriv.lineDerivOp m T) θ = - T (LineDeriv.lineDerivOp m θ) := by
  rw [show LineDeriv.lineDerivOp m T = LineDeriv.lineDerivOpCLM ℂ 𝓢'(E, ℂ) m T from rfl,
    TemperedDistribution.lineDerivOpCLM_eq]
  change T (- (LineDeriv.lineDerivOpCLM ℂ 𝓢(E, ℂ) m) θ) = - T (LineDeriv.lineDerivOp m θ)
  rw [map_neg]
  rfl

/-- A locally integrable complex-valued function with compact support is integrable. -/
lemma integrable_of_locallyIntegrable_hasCompactSupport_cplx {f : E → ℂ}
    (hf : LocallyIntegrable f (volume : Measure E)) (hfc : HasCompactSupport f) :
    Integrable f (volume : Measure E) := by
  have hmeas : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have h_eq : f = (tsupport f).indicator f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact image_eq_zero_of_notMem_tsupport hx
  rw [h_eq, integrable_indicator_iff hmeas]
  exact hf.integrableOn_isCompact hfc.isCompact

end Helpers

open MeasureTheory
open scoped ENNReal ContDiff SchwartzMap Laplacian

/-- Weyl's lemma, one derivative: a weak solution `psi` of `Delta psi + div (psi grad f) = 0` with
`psi` and `psi * |grad f|` in `L^2` lies in `H^1`, tested against smooth compactly supported real
functions.  The hypothesis `hDensity` is the standard fact that a tempered distribution vanishing
on all compactly supported Schwartz functions vanishes. -/
theorem memSobolev_one_of_weak_solutionH1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hDensity : ∀ T : TemperedDistribution E ℂ,
      (∀ θ : SchwartzMap E ℂ, HasCompactSupport (⇑θ) → T θ = 0) → T = 0)
    (f ψ : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hψ : MemLp (fun x : E => ((ψ x : ℝ) : ℂ)) 2 (volume : Measure E))
    (hψf : MemLp (fun x : E => ((ψ x * ‖fderiv ℝ f x‖ : ℝ) : ℂ)) 2 (volume : Measure E))
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x : E, ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
        - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) : ℝ) : ℂ))) = 0) :
    TemperedDistribution.MemSobolev 1 2
      (↑(hψ.toLp (fun x : E => ((ψ x : ℝ) : ℂ))) : TemperedDistribution E ℂ) := by
  classical
  set u : TemperedDistribution E ℂ := ↑(hψ.toLp (fun x : E => ((ψ x : ℝ) : ℂ))) with hu
  have huapply : ∀ θ : 𝓢(E, ℂ), u θ = ∫ x, θ x * ((ψ x : ℝ) : ℂ) := by
    intro θ
    rw [hu]
    exact Lp_toTemperedDistribution_apply' hψ θ
  set b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E with hb
  set F : Fin (Module.finrank ℝ E) → E → ℂ :=
    fun i x => ((ψ x : ℝ) : ℂ) * (((fderiv ℝ f x) (b i) : ℝ) : ℂ) with hF
  have hFmem : ∀ i, MemLp (F i) 2 (volume : Measure E) := by
    intro i
    refine MeasureTheory.MemLp.mono hψf ?_ ?_
    · refine AEStronglyMeasurable.mul hψ.aestronglyMeasurable ?_
      have hcont : Continuous (fun x : E => (((fderiv ℝ f x) (b i) : ℝ) : ℂ)) := by
        have h1 : Continuous (fun x : E => (fderiv ℝ f x) (b i)) :=
          (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
        exact Complex.continuous_ofReal.comp h1
      exact hcont.aestronglyMeasurable
    · filter_upwards with x
      rw [hF]
      have hb1 : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
      calc ‖((ψ x : ℝ) : ℂ) * (((fderiv ℝ f x) (b i) : ℝ) : ℂ)‖
          = |ψ x| * ‖(fderiv ℝ f x) (b i)‖ := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ |ψ x| * (‖fderiv ℝ f x‖ * ‖b i‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
        _ = |ψ x| * ‖fderiv ℝ f x‖ := by rw [hb1, mul_one]
        _ = ‖((ψ x * ‖fderiv ℝ f x‖ : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (norm_nonneg _)]
  set w : Fin (Module.finrank ℝ E) → TemperedDistribution E ℂ :=
    fun i => ↑((hFmem i).toLp (F i)) with hwdef
  have hwapply : ∀ i (θ : 𝓢(E, ℂ)), w i θ = ∫ x, θ x * F i x := by
    intro i θ
    rw [hwdef]
    exact Lp_toTemperedDistribution_apply' (hFmem i) θ
  have hwi_mem : ∀ i, TemperedDistribution.MemSobolev 0 2 (w i) := by
    intro i
    exact TemperedDistribution.memSobolev_zero_iff.mpr ⟨(hFmem i).toLp (F i), by rw [hwdef]⟩
  -- the weak identity as tempered distributions
  have hid : Laplacian.laplacian u = - ∑ i, LineDeriv.lineDerivOp (b i) (w i) := by
    have hzero : Laplacian.laplacian u + ∑ i, LineDeriv.lineDerivOp (b i) (w i) = 0 := by
      refine eq_zero_of_vanishes_on_cplxMap hDensity _ (fun a ha => ?_)
      simp only [add_apply, sum_apply]
      have h1 : (Laplacian.laplacian u) (cplxMap a)
          = ∫ x, ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian a) x : ℝ) : ℂ) := by
        rw [TemperedDistribution.laplacian_apply_apply, huapply]
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [laplacian_cplxMap, mul_comm]
      have hAi : Integrable (fun x : E => ((ψ x : ℝ) : ℂ)
          * (((Laplacian.laplacian a) x : ℝ) : ℂ)) (volume : Measure E) := by
        have h2 := MemLp.integrable_mul hψ
          (SchwartzMap.memLp (cplxMap (Laplacian.laplacian a)) 2 volume)
        refine h2.congr ?_
        filter_upwards with x
        simp [cplxMap_apply]
      have hinner_eq : ∀ x : E,
          inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x))
            = ∑ i, (fderiv ℝ (⇑a) x) (b i) * (fderiv ℝ f x) (b i) := by
        intro x
        rw [← OrthonormalBasis.sum_inner_mul_inner b
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [InnerProductSpace.toDual_symm_apply, real_inner_comm,
          InnerProductSpace.toDual_symm_apply, mul_comm]
      have hBi : Integrable (fun x : E => ((ψ x : ℝ) : ℂ)
          * ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ))
          (volume : Measure E) := by
        obtain ⟨C, hCpos, hCbnd⟩ := a.decay 0 1
        have hC : ∀ x : E, ‖fderiv ℝ (⇑a) x‖ ≤ C := fun x => by simpa using hCbnd x
        have hBcont : Continuous (fun x : E =>
            ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ)) := by
          have h1 : Continuous (fun x : E =>
              (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) :=
            (InnerProductSpace.toDual ℝ E).symm.continuous.comp
              (hf.continuous_fderiv (by norm_num))
          have h2 : Continuous (fun x : E =>
              (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) :=
            (InnerProductSpace.toDual ℝ E).symm.continuous.comp
              ((a.smooth 2).continuous_fderiv (by norm_num))
          have hinner : Continuous (fun x : E =>
              inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x))) :=
            continuous_inner.comp (h1.prodMk h2)
          exact Complex.continuous_ofReal.comp hinner
        have hmemB : MemLp (fun x : E => ((ψ x : ℝ) : ℂ)
            * ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                 ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ))
            2 (volume : Measure E) := by
          refine MeasureTheory.MemLp.mono (hψf.const_mul (C : ℂ)) ?_ ?_
          · refine AEStronglyMeasurable.mul hψ.aestronglyMeasurable ?_
            exact hBcont.aestronglyMeasurable
          · filter_upwards with x
            have hg : ‖(C : ℂ) * ((ψ x * ‖fderiv ℝ f x‖ : ℝ) : ℂ)‖
                = C * (|ψ x| * ‖fderiv ℝ f x‖) := by
              rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs, abs_of_pos hCpos, abs_mul, abs_of_nonneg (norm_nonneg _)]
            rw [hg]
            calc ‖((ψ x : ℝ) : ℂ) * ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ)‖
                = |ψ x| * |inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                    ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x))| := by
                  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                    Real.norm_eq_abs]
              _ ≤ |ψ x| * (‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)‖
                    * ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)‖) := by
                  gcongr
                  exact abs_real_inner_le_norm _ _
              _ = |ψ x| * (‖fderiv ℝ f x‖ * ‖fderiv ℝ (⇑a) x‖) := by
                  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
              _ ≤ |ψ x| * (‖fderiv ℝ f x‖ * C) := by gcongr; exact hC x
              _ = C * (|ψ x| * ‖fderiv ℝ f x‖) := by ring
        have hBzero : ∀ x : E, (∀ i, (LineDeriv.lineDerivOp (b i) a) x = 0) →
            ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ) = 0 := by
          intro x hx
          have h0 : inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) = 0 := by
            rw [← OrthonormalBasis.sum_inner_mul_inner b
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x))]
            refine Finset.sum_eq_zero (fun i _ => ?_)
            have hpt : (fderiv ℝ (⇑a) x) (b i) = (LineDeriv.lineDerivOp (b i) a) x := by
              rw [SchwartzMap.lineDerivOp_apply, (a.differentiableAt).lineDeriv_eq_fderiv]
            rw [InnerProductSpace.toDual_symm_apply, real_inner_comm,
              InnerProductSpace.toDual_symm_apply, hpt, hx i, mul_zero]
          simp [h0]
        have hBcs : HasCompactSupport (fun x : E =>
            ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ)) := by
          refine ha.mono' (fun x hx => ?_)
          simp only [Function.mem_support] at hx
          by_contra hcon
          exact hx (hBzero x (fun i => image_eq_zero_of_notMem_tsupport
            (fun hmem => hcon (SchwartzMap.tsupport_lineDerivOp_subset (b i) a hmem))))
        have hcs : HasCompactSupport (fun x : E => ((ψ x : ℝ) : ℂ)
            * ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ)) := by
          refine hBcs.mono' (fun x hx => ?_)
          simp only [Function.mem_support] at hx
          by_contra hcon
          exact hx (by rw [image_eq_zero_of_notMem_tsupport hcon, mul_zero])
        exact integrable_of_locallyIntegrable_hasCompactSupport_cplx
          (Commons.Analysis.Sobolev.locallyIntegrable_of_hasCompactSupport_memLp
            (f := fun x : E => ((ψ x : ℝ) : ℂ)
              * ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                  ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ))
            (p := 2) (by norm_num) (by simpa using hmemB) hcs) hcs
      have h2 : (∑ i, (LineDeriv.lineDerivOp (b i) (w i)) (cplxMap a))
          = - ∫ x, ((ψ x : ℝ) : ℂ) * ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                  ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ) := by
        have hstep : ∀ i, (LineDeriv.lineDerivOp (b i) (w i)) (cplxMap a)
            = - ∫ x, (((fderiv ℝ (⇑a) x) (b i) : ℝ) : ℂ) * F i x := by
          intro i
          rw [lineDerivOp_apply_tempered]
          congr 1
          rw [hwapply i]
          refine integral_congr_ae ?_
          filter_upwards with x
          have hpt : (LineDeriv.lineDerivOp (b i) (cplxMap a)) x
              = (((fderiv ℝ (⇑a) x) (b i) : ℝ) : ℂ) := by
            rw [lineDerivOp_cplxMap, SchwartzMap.lineDerivOp_apply,
              (a.differentiableAt).lineDeriv_eq_fderiv]
          rw [hpt]
        have hgint : ∀ i, Integrable (fun x : E => (((fderiv ℝ (⇑a) x) (b i) : ℝ) : ℂ) * F i x)
            (volume : Measure E) := by
          intro i
          have hmi : MemLp (fun x : E => (((fderiv ℝ (⇑a) x) (b i) : ℝ) : ℂ)) 2
              (volume : Measure E) := by
            have heq : (fun x : E => (((fderiv ℝ (⇑a) x) (b i) : ℝ) : ℂ))
                = ⇑(cplxMap (LineDeriv.lineDerivOp (b i) a)) := by
              funext x
              rw [cplxMap_apply, SchwartzMap.lineDerivOp_apply,
                (a.differentiableAt).lineDeriv_eq_fderiv]
            rw [heq]
            exact SchwartzMap.memLp _ 2 volume
          exact MemLp.integrable_mul hmi (hFmem i)
        rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_neg_distrib]
        congr 1
        rw [← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hgint i)]
        refine integral_congr_ae ?_
        filter_upwards with x
        have hsum : (∑ i, (((fderiv ℝ (⇑a) x) (b i) : ℝ) : ℂ)
              * (((ψ x : ℝ) : ℂ) * (((fderiv ℝ f x) (b i) : ℝ) : ℂ)))
            = ((ψ x : ℝ) : ℂ) * ((∑ i, (fderiv ℝ (⇑a) x) (b i)
                * (fderiv ℝ f x) (b i) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Complex.ofReal_mul]; ring
        simp only [hF]
        rw [hsum, hinner_eq x]
      rw [h1, h2, ← sub_eq_add_neg, ← MeasureTheory.integral_sub hAi hBi]
      rw [show (fun x : E => ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian a) x : ℝ) : ℂ)
            - ((ψ x : ℝ) : ℂ) * ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ))
          = (fun x : E => ((ψ x : ℝ) : ℂ) * ((((Laplacian.laplacian (⇑a)) x : ℝ) : ℂ)
            - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (⇑a) x)) : ℝ) : ℂ)))
          from funext (fun x => by rw [SchwartzMap.laplacian_apply a x]; ring)]
      exact hw (⇑a) (a.smooth (⊤ : ℕ∞)) ha
    exact eq_neg_of_add_eq_zero_left hzero
  refine memSobolev_one_of_laplacian_memSobolev_neg_one u ?_ ?_
  · rw [hu]
    exact TemperedDistribution.memSobolev_zero_iff.mpr ⟨hψ.toLp _, rfl⟩
  · rw [hid]
    refine TemperedDistribution.MemSobolev.neg ?_
    have hsum : ∀ s : Finset (Fin (Module.finrank ℝ E)),
        TemperedDistribution.MemSobolev (-1) 2 (∑ i ∈ s, LineDeriv.lineDerivOp (b i) (w i)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp only [Finset.sum_empty]
        exact TemperedDistribution.memSobolev_fun_zero E ℂ (-1) 2
      · intro i s his ih
        rw [Finset.sum_insert his]
        have h1 : TemperedDistribution.MemSobolev (-1) 2 (LineDeriv.lineDerivOp (b i) (w i)) := by
          simpa using (hwi_mem i).lineDerivOp (m := b i)
        exact h1.add ih
    simpa using hsum Finset.univ

end Commons.Analysis.Sobolev
