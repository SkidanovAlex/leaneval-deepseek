import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.BSKinetic.plancherel_pconv
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal Convolution Pointwise

namespace Work.OneBodyKin

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- The indicator of the cube `acube ℓ`, as a real function. -/
def bsMeanBoxInd (ℓ : ℝ) : ℝ³ → ℝ := (acube ℓ).indicator (fun _ => (1 : ℝ))

lemma neg_mem_acube_iff (ℓ : ℝ) (z : ℝ³) : -z ∈ acube ℓ ↔ z ∈ acube ℓ := by
  have hneg : ∀ m : Fin 3, (-z) m = -(z m) := fun m => by simp
  simp only [mem_acube_iff]
  constructor
  · intro h m
    have h' := h m
    rw [hneg m] at h'
    simp only [Set.mem_Icc, neg_div] at h' ⊢
    exact ⟨by linarith [h'.2], by linarith [h'.1]⟩
  · intro h m
    have h' := h m
    simp only [Set.mem_Icc, neg_div] at h' ⊢
    rw [hneg m]
    exact ⟨by linarith [h'.2], by linarith [h'.1]⟩

lemma bsMeanBoxInd_of_mem {ℓ : ℝ} {z : ℝ³} (hz : z ∈ acube ℓ) : bsMeanBoxInd ℓ z = 1 := by
  rw [bsMeanBoxInd, Set.indicator_of_mem hz]

lemma bsMeanBoxInd_of_notMem {ℓ : ℝ} {z : ℝ³} (hz : z ∉ acube ℓ) : bsMeanBoxInd ℓ z = 0 := by
  rw [bsMeanBoxInd, Set.indicator_of_notMem hz]

lemma bsMeanBoxInd_even (ℓ : ℝ) (z : ℝ³) : bsMeanBoxInd ℓ (-z) = bsMeanBoxInd ℓ z := by
  by_cases hz : z ∈ acube ℓ
  · rw [bsMeanBoxInd_of_mem ((neg_mem_acube_iff ℓ z).2 hz), bsMeanBoxInd_of_mem hz]
  · rw [bsMeanBoxInd_of_notMem (fun h => hz ((neg_mem_acube_iff ℓ z).1 h)), bsMeanBoxInd_of_notMem hz]

lemma norm_bsMeanBoxInd_le_one (ℓ : ℝ) (z : ℝ³) : ‖bsMeanBoxInd ℓ z‖ ≤ 1 := by
  by_cases hz : z ∈ acube ℓ
  · rw [bsMeanBoxInd_of_mem hz]; simp
  · rw [bsMeanBoxInd_of_notMem hz]; simp

lemma integrable_bsMeanBoxInd (ℓ : ℝ) : Integrable (bsMeanBoxInd ℓ) volume := by
  rw [bsMeanBoxInd, integrable_indicator_iff (acube_measurable ℓ)]
  refine IntegrableOn.of_bound ((Work.UBBInputs9.B.acube_isCompact ℓ).measure_lt_top) ?_ 1 ?_
  · exact aestronglyMeasurable_const
  · filter_upwards with z; simp

/-- The box convolution `(1_{acube ℓ} ⋆ ψ)(x) = ∫_{acube ℓ} ψ (x - t) dt`. -/
def bsMeanBoxConv (ℓ : ℝ) (ψ : ℝ³ → ℝ) : ℝ³ → ℝ :=
  fun x => ∫ t : ℝ³, bsMeanBoxInd ℓ t * ψ (x - t)

lemma integral_acube_add_eq_bsMeanBoxConv (ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) :
    (∫ z in acube ℓ, ψ (x + z)) = bsMeanBoxConv ℓ ψ x := by
  rw [bsMeanBoxConv]
  have h1 : (∫ z in acube ℓ, ψ (x + z)) = ∫ z, bsMeanBoxInd ℓ z * ψ (x + z) := by
    rw [bsMeanBoxInd, ← MeasureTheory.integral_indicator (acube_measurable ℓ)]
    apply integral_congr_ae; filter_upwards with z
    by_cases hz : z ∈ acube ℓ
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  rw [h1]
  rw [← Submission.BoseGases.integral_comp_neg (fun z => bsMeanBoxInd ℓ z * ψ (x + z))]
  apply integral_congr_ae; filter_upwards with z
  rw [bsMeanBoxInd_even]
  congr 1

lemma bsMeanBoxConv_contDiff {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hcs : HasCompactSupport ψ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) : ContDiff ℝ (⊤ : ENat) (bsMeanBoxConv ℓ ψ) := by
  have hconv : bsMeanBoxConv ℓ ψ =
      MeasureTheory.convolution (bsMeanBoxInd ℓ) ψ (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    rw [bsMeanBoxConv, MeasureTheory.convolution_mul]
  rw [hconv]
  exact HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hcs
    (integrable_bsMeanBoxInd ℓ).locallyIntegrable hψ

lemma bsMeanBoxConv_hasCompactSupport {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hcs : HasCompactSupport ψ) :
    HasCompactSupport (bsMeanBoxConv ℓ ψ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := acube ℓ + tsupport ψ)
  · exact (Work.UBBInputs9.B.acube_isCompact ℓ).add hcs.isCompact
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hxK
    apply hx
    rw [bsMeanBoxConv]
    have hzero : ∀ t : ℝ³, bsMeanBoxInd ℓ t * ψ (x - t) = 0 := by
      intro t
      by_cases ht : t ∈ acube ℓ
      · have hxt : x - t ∉ tsupport ψ := by
          intro hmem
          apply hxK
          rw [Set.mem_add]
          exact ⟨t, ht, x - t, hmem, by abel⟩
        have hψ0 : ψ (x - t) = 0 := by
          by_contra h
          exact hxt (subset_tsupport ψ ((Function.mem_support).2 h))
        rw [hψ0, mul_zero]
      · rw [bsMeanBoxInd_of_notMem ht, zero_mul]
    simp [hzero]

lemma kinFT_bsMeanBoxInd (ℓ : ℝ) (q : ℝ³) :
    Submission.BoseGases.kinFT (fun z => (bsMeanBoxInd ℓ z : ℂ)) q = (boxHat ℓ q : ℂ) := by
  have hcont : Continuous (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ)))) := by
    apply Complex.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.mul continuous_const
    exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
  have hf : Integrable (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)) volume := by
    have hpt2 : (fun y : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ))
        = (acube ℓ).indicator (fun y => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ)))) := by
      funext y
      by_cases hy : y ∈ acube ℓ
      · rw [Set.indicator_of_mem hy, bsMeanBoxInd_of_mem hy]; simp
      · rw [Set.indicator_of_notMem hy, bsMeanBoxInd_of_notMem hy]; simp
    rw [hpt2, MeasureTheory.integrable_indicator_iff (acube_measurable ℓ)]
    exact ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.acube_isCompact ℓ) hcont.continuousOn
  have hexp : ∀ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q y : ℂ)))
      = ((Real.cos (inner ℝ q y) : ℝ) : ℂ) - ((Real.sin (inner ℝ q y) : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [show -(Complex.I * (inner ℝ q y : ℂ)) = ((-(inner ℝ q y) : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hpt : ∀ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)
      = ((bsMeanBoxInd ℓ y * Real.cos (inner ℝ q y) : ℝ) : ℂ)
        + ((-(bsMeanBoxInd ℓ y * Real.sin (inner ℝ q y)) : ℝ) : ℂ) * Complex.I := by
    intro y; rw [hexp y]; push_cast; ring
  have hre_pt : ∀ y : ℝ³,
      (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).re
        = bsMeanBoxInd ℓ y * Real.cos (inner ℝ q y) := by
    intro y; rw [hpt y]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have him_pt : ∀ y : ℝ³,
      (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).im
        = -(bsMeanBoxInd ℓ y * Real.sin (inner ℝ q y)) := by
    intro y; rw [hpt y]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  rw [Submission.BoseGases.kinFT]
  apply Complex.ext
  · have hre : (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).re
        = ∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).re := by
      have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
      simpa using this.symm
    rw [hre]
    rw [show (∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).re)
          = ∫ y : ℝ³, bsMeanBoxInd ℓ y * Real.cos (inner ℝ q y) from by
        apply integral_congr_ae; filter_upwards with y; exact hre_pt y]
    rw [show (∫ y : ℝ³, bsMeanBoxInd ℓ y * Real.cos (inner ℝ q y))
          = ∫ y in acube ℓ, Real.cos (inner ℝ q y) from by
        rw [show (fun y : ℝ³ => bsMeanBoxInd ℓ y * Real.cos (inner ℝ q y))
              = (acube ℓ).indicator (fun y => Real.cos (inner ℝ q y)) from by
          funext y
          by_cases hy : y ∈ acube ℓ
          · rw [bsMeanBoxInd_of_mem hy, Set.indicator_of_mem hy, one_mul]
          · rw [bsMeanBoxInd_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]]
        rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]]
    simp [boxHat]
  · have him : (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).im
        = ∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).im := by
      have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hf
      simpa using this.symm
    rw [him]
    rw [show (∫ y : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * (bsMeanBoxInd ℓ y : ℂ)).im)
          = ∫ y : ℝ³, -(bsMeanBoxInd ℓ y * Real.sin (inner ℝ q y)) from by
        apply integral_congr_ae; filter_upwards with y; exact him_pt y]
    rw [MeasureTheory.integral_neg]
    have hzero : (∫ y : ℝ³, bsMeanBoxInd ℓ y * Real.sin (inner ℝ q y)) = 0 := by
      have hinv := Submission.BoseGases.integral_comp_neg
        (fun y : ℝ³ => bsMeanBoxInd ℓ y * Real.sin (inner ℝ q y))
      have hshift : (∫ y : ℝ³, (fun y : ℝ³ => bsMeanBoxInd ℓ y * Real.sin (inner ℝ q y)) (-y))
          = -(∫ y : ℝ³, bsMeanBoxInd ℓ y * Real.sin (inner ℝ q y)) := by
        rw [← MeasureTheory.integral_neg]
        apply integral_congr_ae; filter_upwards with y
        rw [bsMeanBoxInd_even]
        simp only [inner_neg_right, Real.sin_neg]
        ring
      rw [hshift] at hinv
      linarith
    rw [hzero, neg_zero]
    simp

lemma kinFT_bsMeanBoxConv {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (q : ℝ³) :
    Submission.BoseGases.kinFT (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ)) q
      = (boxHat ℓ q : ℂ) * Submission.BoseGases.kinFT (fun z => (ψ z : ℂ)) q := by
  have hψℂ_smooth : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (ψ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  have hψℂ_cs : HasCompactSupport (fun z : ℝ³ => (ψ z : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      hcs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  have hψℂ_int : Integrable (fun z : ℝ³ => (ψ z : ℂ)) volume :=
    hψℂ_smooth.continuous.integrable_of_hasCompactSupport hψℂ_cs
  have hgℂ_int : Integrable (fun z : ℝ³ => (bsMeanBoxInd ℓ z : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp (integrable_bsMeanBoxInd ℓ)
  have hconv : (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ))
      = MeasureTheory.convolution (fun z => (bsMeanBoxInd ℓ z : ℂ)) (fun z => (ψ z : ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext z
    rw [MeasureTheory.convolution_mul]
    rw [bsMeanBoxConv, ← integral_complex_ofReal]
    apply integral_congr_ae; filter_upwards with t
    push_cast; ring
  calc Submission.BoseGases.kinFT (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ)) q
      = FourierTransform.fourier (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • q) :=
        Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ _
    _ = FourierTransform.fourier (MeasureTheory.convolution (fun z => (bsMeanBoxInd ℓ z : ℂ))
          (fun z => (ψ z : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume) ((2 * Real.pi)⁻¹ • q) := by
        rw [hconv]
    _ = FourierTransform.fourier (fun z => (bsMeanBoxInd ℓ z : ℂ)) ((2 * Real.pi)⁻¹ • q)
          * FourierTransform.fourier (fun z => (ψ z : ℂ)) ((2 * Real.pi)⁻¹ • q) :=
        Real.fourier_mul_convolution_eq hgℂ_int hψℂ_int _
    _ = (boxHat ℓ q : ℂ) * Submission.BoseGases.kinFT (fun z => (ψ z : ℂ)) q := by
        rw [← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
          ← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
        rw [kinFT_bsMeanBoxInd]

lemma norm_kinFT_bsMeanBoxConv_sq {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (q : ℝ³) :
    ‖Submission.BoseGases.kinFT (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ)) q‖ ^ 2
      = (boxHat ℓ q) ^ 2 * ‖Submission.BoseGases.kinFT (fun z => (ψ z : ℂ)) q‖ ^ 2 := by
  rw [kinFT_bsMeanBoxConv hψ hcs q, norm_mul, mul_pow]
  have h1 : ‖((boxHat ℓ q : ℝ) : ℂ)‖ ^ 2 = (boxHat ℓ q) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  rw [h1]

lemma integral_norm_kinFT_bsMeanBoxConv {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    (∫ q : ℝ³, ‖Submission.BoseGases.kinFT (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ)) q‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ x : ℝ³, (bsMeanBoxConv ℓ ψ x) ^ 2 := by
  have hc : ContDiff ℝ (⊤ : ENat) (bsMeanBoxConv ℓ ψ) := bsMeanBoxConv_contDiff hcs hψ
  have hk : HasCompactSupport (bsMeanBoxConv ℓ ψ) := bsMeanBoxConv_hasCompactSupport hcs
  have hp := Work.BSKinetic.plancherel_pconv (bsMeanBoxConv ℓ ψ) hc hk
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 (by positivity)
  calc (∫ q : ℝ³, ‖Submission.BoseGases.kinFT (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ)) q‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : ℝ³, ‖Submission.BoseGases.kinFT (fun z => ((bsMeanBoxConv ℓ ψ z : ℝ) : ℂ)) q‖ ^ 2) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = (2 * Real.pi) ^ 3 * ∫ x : ℝ³, (bsMeanBoxConv ℓ ψ x) ^ 2 := by rw [hp]

lemma integral_boxHat_sq {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    (∫ q : ℝ³, (boxHat ℓ q) ^ 2 * ‖Submission.BoseGases.kinFT (fun z => (ψ z : ℂ)) q‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ x : ℝ³, (bsMeanBoxConv ℓ ψ x) ^ 2 := by
  rw [← integral_norm_kinFT_bsMeanBoxConv hψ hcs]
  apply integral_congr_ae; filter_upwards with q
  exact (norm_kinFT_bsMeanBoxConv_sq hψ hcs q).symm

theorem integral_bsMean_sq_eq_symbol {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ u : EuclideanSpace ℝ (Fin 3), (Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 9)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.OneBodyKin.boxHat ℓ q) ^ 2 *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  have hbm : ∀ u : ℝ³, Work.BSKinetic.bsMean ℓ u ψ = (ℓ ^ 3)⁻¹ * bsMeanBoxConv ℓ ψ (ℓ • u) := by
    intro u
    rw [Work.BSKinetic.bsMean, integral_acube_add_eq_bsMeanBoxConv]
  have hJ : (∫ u : ℝ³, (bsMeanBoxConv ℓ ψ (ℓ • u)) ^ 2)
      = (ℓ ^ 3)⁻¹ * ∫ w : ℝ³, (bsMeanBoxConv ℓ ψ w) ^ 2 := by
    have h := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure ℝ³))
      (f := fun w : ℝ³ => (bsMeanBoxConv ℓ ψ w) ^ 2) ℓ (hR := hℓ.le)
    rw [show Module.finrank ℝ ℝ³ = 3 from by simp] at h
    simpa [smul_eq_mul] using h
  have hL : (∫ u : ℝ³, (Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
      = ((ℓ ^ 3)⁻¹) ^ 2 * ((ℓ ^ 3)⁻¹ * ∫ w : ℝ³, (bsMeanBoxConv ℓ ψ w) ^ 2) := by
    have h1 : (∫ u : ℝ³, (Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
        = ∫ u : ℝ³, (((ℓ ^ 3)⁻¹) ^ 2 * (bsMeanBoxConv ℓ ψ (ℓ • u)) ^ 2) := by
      apply integral_congr_ae; filter_upwards with u
      rw [hbm u]; ring
    rw [h1, integral_const_mul, hJ]
  have hInt : (∫ q : ℝ³, (boxHat ℓ q) ^ 2 * ‖Submission.BoseGases.kinFT (fun z => (ψ z : ℂ)) q‖ ^ 2)
      = (2 * Real.pi) ^ 3 * ∫ w : ℝ³, (bsMeanBoxConv ℓ ψ w) ^ 2 := integral_boxHat_sq hψ hcs
  rw [hL, hInt]
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

end Work.OneBodyKin
