import Mathlib
import Submission.Vinogradov.NormCoord
import Submission.Vinogradov.Extension
import Submission.Commons.Analysis.Integral.integral_norm_mul_sub_le
import Submission.Commons.Analysis.Fourier.half_integral_le_re_fourierInv

noncomputable section
open MeasureTheory Complex
open scoped Real BigOperators FourierTransform RealInnerProductSpace Interval

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Vinogradov

open Classical

/-!
# Band-limited Nikolskii for the extension operator (BDG §5 tools)

This module develops the `L^q`–`L^p` comparison for the moment-curve extension
operator that Bourgain–Demeter–Guth use in §5 of their proof (the "Corollary"
following their Lemma `nl9`):

    ‖E_{[0,1]} g‖_{L^q(w_B)} ≲ ‖E_{[0,1]} g‖_{L^p(w_B)}      (q ≥ p ≥ 1,  R ≥ 1),

with an implicit constant depending only on `k, p, q`.  The proof has three
ingredients:

1. **A reproducing Schwartz kernel.**  `reproKernel k` is the inverse Fourier
   transform of the truncation of a bump function that is `1` on the ball of
   radius `√k + 1`; consequently `𝓕 (reproKernel k) = 1` on that ball, and in
   particular `𝓕 (reproKernel k) (γ(t)) = 1` for `t ∈ [0,1]`, where
   `γ(t) = (t, t², …, tᵏ)` (`gammaVec`).
2. **The reproduction identity** `extOp_conv_reproKernel`: for every integrable
   `g` and every `x`, `E_{[0,1]} g x = ∫ y, E_{[0,1]} g (x - y) · ψ(y) dy`.
   This is the statement that the extension operator is *band limited*, in a
   form that is directly usable.
3. **Hölder / Young**, giving the pointwise bound
   `‖E g x‖ ≤ ‖ψ‖_{p'} (∫ ‖E g‖^p)^{1/p}`.

The remaining (project-specific) steps — the localization by a weight with
compactly supported Fourier transform, the cover lemma `nl9` and the final
comparison of weighted norms — are developed on top of these facts.

Everything in this file is proved (no sorries).
-/

/-- The moment-curve vector `γ(t) = (t, t², …, tᵏ) ∈ ℝᵏ`. -/
noncomputable def gammaVec (k : ℕ) (t : ℝ) : E k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => t ^ (j.val + 1))

lemma gammaVec_apply (k : ℕ) (t : ℝ) (j : Fin k) : gammaVec k t j = t ^ (j.val + 1) := by
  simp [gammaVec]

/-- `⟪y, γ(t)⟫ = y·γ(t)` is the phase of the moment-curve character. -/
lemma inner_gamma (k : ℕ) (y : E k) (t : ℝ) : ⟪y, gammaVec k t⟫ = momPhase k y t := by
  rw [inner_coord, momPhase]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [gammaVec_apply]

lemma sub_apply_E (k : ℕ) (x y : E k) (j : Fin k) : (x - y) j = x j - y j := rfl

lemma momPhase_sub (k : ℕ) (x y : E k) (t : ℝ) :
    momPhase k (x - y) t = momPhase k x t - momPhase k y t := by
  simp only [momPhase, sub_apply_E, sub_mul, Finset.sum_sub_distrib]

/-- Splitting the character: `e((x−y)·γ(t)) = e(x·γ(t))·𝐞(−⟪y, γ(t)⟫)`. -/
lemma momChar_sub (k : ℕ) (x y : E k) (t : ℝ) :
    momChar k (x - y) t
      = momChar k x t * ((Real.fourierChar (- ⟪y, gammaVec k t⟫) : Circle) : ℂ) := by
  rw [momChar_eq_exp, momChar_eq_exp, momPhase_sub, inner_gamma, Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The reference bump of radius `√k+1` at the origin (the frequency truncation). -/
noncomputable def bumpRho (k : ℕ) : ContDiffBump (0 : E k) :=
  ⟨Real.sqrt k + 1, Real.sqrt k + 2, by positivity, by linarith⟩

lemma contDiff_rho (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun w : E k => ((bumpRho k w : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (bumpRho k).contDiff

lemma hasCompactSupport_rho (k : ℕ) :
    HasCompactSupport (fun w : E k => ((bumpRho k w : ℝ) : ℂ)) :=
  (bumpRho k).hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

/-- The reference bump as a complex-valued Schwartz function. -/
noncomputable def rhoSch (k : ℕ) : SchwartzMap (E k) ℂ :=
  (hasCompactSupport_rho k).toSchwartzMap (contDiff_rho k)

lemma rhoSch_coe (k : ℕ) (w : E k) : (rhoSch k : E k → ℂ) w = ((bumpRho k w : ℝ) : ℂ) := by
  rw [rhoSch, HasCompactSupport.toSchwartzMap_toFun]

/-- The reproducing (band-limiting) kernel `ψ = 𝓕⁻(reference bump)`. -/
noncomputable def reproKernel (k : ℕ) : SchwartzMap (E k) ℂ :=
  (𝓕⁻ (rhoSch k) : SchwartzMap (E k) ℂ)

lemma fourier_reproKernel (k : ℕ) :
    𝓕 ((reproKernel k : E k → ℂ)) = (rhoSch k : E k → ℂ) := by
  have h : 𝓕 (reproKernel k) = rhoSch k :=
    FourierTransform.fourier_fourierInv_eq (E := SchwartzMap (E k) ℂ)
      (F := SchwartzMap (E k) ℂ) (rhoSch k)
  rw [← h, SchwartzMap.fourier_coe]

lemma gammaVec_norm_le (k : ℕ) (t : ℝ) (ht : |t| ≤ 1) : ‖gammaVec k t‖ ≤ Real.sqrt k + 1 := by
  have h2 : ‖gammaVec k t‖ ^ 2 ≤ (k : ℝ) := by
    rw [norm_sq_coord_sum]
    calc ∑ j : Fin k, (gammaVec k t j) ^ 2 ≤ ∑ _j : Fin k, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [gammaVec_apply]
          have h1 : |t ^ (j.val + 1)| ≤ 1 := by
            rw [abs_pow]
            exact pow_le_one₀ (abs_nonneg t) ht (n := j.val + 1)
          nlinarith [sq_abs (t ^ (j.val + 1)), abs_nonneg (t ^ (j.val + 1))]
      _ = (k : ℝ) := by simp
  have h3 : ‖gammaVec k t‖ ≤ Real.sqrt k := by
    calc ‖gammaVec k t‖ = Real.sqrt (‖gammaVec k t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt k := by norm_num
  linarith

/-- The reproducing property of `reproKernel` on the moment curve. -/
lemma fourier_reproKernel_gamma (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    𝓕 ((reproKernel k : E k → ℂ)) (gammaVec k t) = 1 := by
  rw [fourier_reproKernel, rhoSch_coe]
  have hmem : gammaVec k t ∈ Metric.closedBall (0 : E k) (bumpRho k).rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have : (bumpRho k).rIn = Real.sqrt k + 1 := rfl
    rw [this]
    exact gammaVec_norm_le k t (by rw [abs_of_nonneg ht.1]; exact ht.2)
  rw [(bumpRho k).one_of_mem_closedBall hmem]
  simp

lemma continuous_momChar_sub_prod (k : ℕ) (x : E k) :
    Continuous (fun z : ℝ × E k => momChar k (x - z.2) z.1) := by
  simp only [momChar]
  fun_prop

lemma integrable_momChar_mul_reproKernel (k : ℕ) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume) (x : E k) :
    Integrable (Function.uncurry (fun t : ℝ => fun y : E k =>
        (g t * momChar k (x - y) t) * (reproKernel k : E k → ℂ) y))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) := by
  have hg' : IntegrableOn g (Set.uIoc (0:ℝ) 1) volume := by
    refine hg.mono_set ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self
  have hψ : Integrable (fun y : E k => (reproKernel k : E k → ℂ) y) volume :=
    (reproKernel k).integrable
  have hbound : Integrable (fun z : ℝ × E k => ‖g z.1‖ * ‖(reproKernel k : E k → ℂ) z.2‖)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) :=
    hg'.norm.mul_prod hψ.norm
  refine Integrable.mono' hbound ?_ ?_
  · exact ((hg'.aestronglyMeasurable.comp_fst).mul
      (continuous_momChar_sub_prod k x).aestronglyMeasurable).mul
      ((reproKernel k).continuous.aestronglyMeasurable.comp_snd)
  · filter_upwards with z
    change ‖(g z.1 * momChar k (x - z.2) z.1) * (reproKernel k : E k → ℂ) z.2‖
        ≤ ‖g z.1‖ * ‖(reproKernel k : E k → ℂ) z.2‖
    rw [norm_mul, norm_mul, momChar_norm_one, mul_one]

/-- **The reproduction identity**: the extension operator `E_{[0,1]} g` equals its
convolution with the reproducing kernel `reproKernel k`.  This is the
"band-limitedness" of the extension operator in usable form. -/
lemma extOp_conv_reproKernel (k : ℕ) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    (x : E k) :
    extOp k g 0 1 x
      = ∫ y : E k, extOp k g 0 1 (x - y) * (reproKernel k : E k → ℂ) y := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hinner : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (∫ y : E k, (g t * momChar k (x - y) t) * (reproKernel k : E k → ℂ) y)
        = g t * momChar k x t := by
    intro t ht
    have h1 : ∀ y : E k, (g t * momChar k (x - y) t) * (reproKernel k : E k → ℂ) y
        = (g t * momChar k x t)
          * (((Real.fourierChar (- ⟪y, gammaVec k t⟫) : Circle) : ℂ)
              * (reproKernel k : E k → ℂ) y) := by
      intro y
      rw [momChar_sub]
      ring
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ y : E k, ((Real.fourierChar (- ⟪y, gammaVec k t⟫) : Circle) : ℂ)
          * (reproKernel k : E k → ℂ) y)
        = 𝓕 ((reproKernel k : E k → ℂ)) (gammaVec k t) := by
      rw [Real.fourier_eq]
      simp only [Circle.smul_def, smul_eq_mul]
    rw [h2, fourier_reproKernel_gamma k t ht, mul_one]
  rw [extOp, intervalIntegral.integral_of_le h01]
  have hstep : (∫ y : E k, extOp k g 0 1 (x - y) * (reproKernel k : E k → ℂ) y)
      = ∫ y : E k, ∫ t in (0:ℝ)..1,
          (g t * momChar k (x - y) t) * (reproKernel k : E k → ℂ) y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (intervalIntegral (fun t : ℝ => g t * momChar k (x - y) t) 0 1 volume)
        * (reproKernel k : E k → ℂ) y
      = ∫ t in (0:ℝ)..1, (g t * momChar k (x - y) t) * (reproKernel k : E k → ℂ) y
    exact (intervalIntegral.integral_mul_const _ _).symm
  rw [hstep, ← intervalIntegral_integral_swap (integrable_momChar_mul_reproKernel k g hg x)]
  conv_rhs => rw [intervalIntegral.integral_of_le h01]
  exact setIntegral_congr_fun measurableSet_Ioc
    (fun t ht => (hinner t (Set.Ioc_subset_Icc_self ht)).symm)

noncomputable section
open MeasureTheory Complex
open scoped Real BigOperators FourierTransform RealInnerProductSpace Interval

/-- The frequency-localizing bump of radius `1/16`, support `1/8`. -/
noncomputable def freqBump (k : ℕ) : ContDiffBump (0 : E k) :=
  ⟨1/16, 1/8, by norm_num, by norm_num⟩

lemma freqBump_rOut (k : ℕ) : (freqBump k).rOut = 1/8 := rfl
lemma freqBump_rIn (k : ℕ) : (freqBump k).rIn = 1/16 := rfl

lemma contDiff_freqBump (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun w : E k => ((freqBump k w : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (freqBump k).contDiff

lemma hasCompactSupport_freqBump (k : ℕ) :
    HasCompactSupport (fun w : E k => ((freqBump k w : ℝ) : ℂ)) :=
  (freqBump k).hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

noncomputable def freqBumpSch (k : ℕ) : SchwartzMap (E k) ℂ :=
  (hasCompactSupport_freqBump k).toSchwartzMap (contDiff_freqBump k)

lemma freqBumpSch_coe (k : ℕ) (w : E k) :
    (freqBumpSch k : E k → ℂ) w = ((freqBump k w : ℝ) : ℂ) := by
  rw [freqBumpSch, HasCompactSupport.toSchwartzMap_toFun]

/-- The localization weight `φ_B`. -/
noncomputable def phiB (k : ℕ) (c : E k) (R : ℝ) (x : E k) : ℂ :=
  ∫ w : E k, ((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
    * ((freqBump k w : ℝ) : ℂ)

lemma phiB_eq_fourierInv (k : ℕ) (c : E k) (R : ℝ) (x : E k) :
    phiB k c R x = 𝓕⁻ ((freqBumpSch k : E k → ℂ)) ((R⁻¹ : ℝ) • (x - c)) := by
  rw [phiB, Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [freqBumpSch_coe, Circle.smul_def, smul_eq_mul]


lemma phiB_sub (k : ℕ) (c : E k) (R : ℝ) (x y : E k) :
    phiB k c R (x - y)
      = ∫ w : E k, ((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((freqBump k w : ℝ) : ℂ) := by
  unfold phiB
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only []
  have harg : ⟪w, (R⁻¹ : ℝ) • ((x - y) - c)⟫
      = ⟪w, (R⁻¹ : ℝ) • (x - c)⟫ + (-⟪(R⁻¹ : ℝ) • w, y⟫) := by
    rw [real_inner_smul_right, inner_sub_right, inner_sub_right, real_inner_smul_right,
        inner_sub_right, real_inner_smul_left]
    ring
  rw [harg, Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


lemma fourier_reproKernel_one (k : ℕ) (w : E k) (hw : ‖w‖ ≤ Real.sqrt k + 1) :
    𝓕 ((reproKernel k : E k → ℂ)) w = 1 := by
  rw [fourier_reproKernel, rhoSch_coe]
  have hmem : w ∈ Metric.closedBall (0 : E k) (bumpRho k).rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h : (bumpRho k).rIn = Real.sqrt k + 1 := rfl
    rw [h]; exact hw
  rw [(bumpRho k).one_of_mem_closedBall hmem]
  simp

lemma char_R_mul (k : ℕ) (R : ℝ) (w y v : E k) :
    ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
      * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ)
    = ((Real.fourierChar (-⟪y, (R⁻¹ : ℝ) • w + v⟫) : Circle) : ℂ) := by
  have h1 : (-⟪(R⁻¹ : ℝ) • w, y⟫ : ℝ) = -⟪y, (R⁻¹ : ℝ) • w⟫ := by
    rw [real_inner_comm]
  have h2 : (-⟪y, (R⁻¹ : ℝ) • w + v⟫ : ℝ) = (-⟪y, (R⁻¹ : ℝ) • w⟫) + (-⟪y, v⟫) := by
    rw [inner_add_right]; ring
  rw [h1, h2, Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integrable_phiB_char_psi (k : ℕ) (c : E k) (R : ℝ) (x v : E k) :
    Integrable (Function.uncurry (fun w : E k => fun y : E k =>
        ((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((freqBump k w : ℝ) : ℂ)
          * (((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) y)))
      (volume.prod volume) := by
  have hψ : Integrable (fun y : E k => (reproKernel k : E k → ℂ) y) volume :=
    (reproKernel k).integrable
  have hbump : Integrable (fun w : E k => ((freqBump k w : ℝ))) volume :=
    (freqBump k).integrable
  have hbound : Integrable (fun z : E k × E k =>
      ((freqBump k z.1 : ℝ)) * ‖(reproKernel k : E k → ℂ) z.2‖) (volume.prod volume) :=
    hbump.mul_prod hψ.norm
  refine Integrable.mono' hbound ?_ ?_
  · apply Measurable.aestronglyMeasurable
    have hfb : Continuous (fun w : E k => ((freqBump k w : ℝ))) := (freqBump k).continuous
    have hψc : Continuous (fun y : E k => (reproKernel k : E k → ℂ) y) := (reproKernel k).continuous
    have hcont : Continuous (fun z : E k × E k =>
        ((Real.fourierChar (⟪z.1, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • z.1, z.2⟫) : Circle) : ℂ)
          * ((freqBump k z.1 : ℝ) : ℂ)
          * (((Real.fourierChar (-⟪z.2, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) z.2)) := by
      simp only [Real.fourierChar_apply]
      fun_prop
    exact hcont.measurable
  · filter_upwards with z
    change ‖((Real.fourierChar (⟪z.1, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • z.1, z.2⟫) : Circle) : ℂ)
          * ((freqBump k z.1 : ℝ) : ℂ)
          * (((Real.fourierChar (-⟪z.2, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) z.2)‖
        ≤ ((freqBump k z.1 : ℝ)) * ‖(reproKernel k : E k → ℂ) z.2‖
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have h1 : ‖((Real.fourierChar (⟪z.1, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    have h2 : ‖((Real.fourierChar (-⟪(R⁻¹ : ℝ) • z.1, z.2⟫) : Circle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    have h3 : ‖((Real.fourierChar (-⟪z.2, v⟫) : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    have h4 : ‖((freqBump k z.1 : ℝ) : ℂ)‖ = (freqBump k z.1 : ℝ) :=
      complex_norm_ofReal_nonneg (freqBump k z.1) ((freqBump k).nonneg' z.1)
    rw [h1, h2, h3, h4]
    linarith


lemma inner_integral_char (k : ℕ) (R : ℝ) (v w : E k) :
    (∫ y : E k, (((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ))
        * (reproKernel k : E k → ℂ) y)
      = 𝓕 ((reproKernel k : E k → ℂ)) ((R⁻¹ : ℝ) • w + v) := by
  have h : (fun y : E k => (((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ))
        * (reproKernel k : E k → ℂ) y)
      = fun y => ((Real.fourierChar (-⟪y, (R⁻¹ : ℝ) • w + v⟫) : Circle) : ℂ)
        * (reproKernel k : E k → ℂ) y := by
    funext y; rw [char_R_mul]
  rw [h, Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [Circle.smul_def, smul_eq_mul]

lemma phiB_char_conv (k : ℕ) (c : E k) (R : ℝ) (hR : 1 ≤ R) (x v : E k)
    (hv : ‖v‖ ≤ Real.sqrt k) :
    (∫ y : E k, phiB k c R (x - y)
        * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ)
        * ((reproKernel k : E k → ℂ) y))
      = phiB k c R x := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have h1 : ∀ y : E k,
      phiB k c R (x - y)
        * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ)
        * ((reproKernel k : E k → ℂ) y)
      = ∫ w : E k, (((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((freqBump k w : ℝ) : ℂ))
          * (((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) y) := by
    intro y
    rw [phiB_sub, mul_assoc]
    exact (MeasureTheory.integral_mul_const
      (((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) y)
      (fun w : E k => ((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((freqBump k w : ℝ) : ℂ))).symm
  rw [show (∫ y : E k, phiB k c R (x - y)
        * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ)
        * ((reproKernel k : E k → ℂ) y))
      = ∫ y : E k, ∫ w : E k, (((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((freqBump k w : ℝ) : ℂ))
          * (((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) y)
      from integral_congr_ae (Filter.Eventually.of_forall h1)]
  rw [← integral_integral_swap (integrable_phiB_char_psi k c R x v)]
  have h2 : ∀ w : E k, (∫ y : E k, (((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((freqBump k w : ℝ) : ℂ))
          * (((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) y))
      = ((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ) * ((freqBump k w : ℝ) : ℂ) := by
    intro w
    have hrw : (fun y : E k => (((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ)
          * ((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
          * ((freqBump k w : ℝ) : ℂ))
          * (((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ) * (reproKernel k : E k → ℂ) y))
        = fun y => (((Real.fourierChar (⟪w, (R⁻¹ : ℝ) • (x - c)⟫) : Circle) : ℂ) * ((freqBump k w : ℝ) : ℂ))
          * ((((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
              * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ)) * (reproKernel k : E k → ℂ) y) := by
      funext y; ring
    rw [hrw, MeasureTheory.integral_const_mul]
    by_cases hw : (freqBump k : E k → ℝ) w = 0
    · rw [hw]; simp
    · have hb : (∫ y : E k, (((Real.fourierChar (-⟪(R⁻¹ : ℝ) • w, y⟫) : Circle) : ℂ)
            * ((Real.fourierChar (-⟪y, v⟫) : Circle) : ℂ)) * (reproKernel k : E k → ℂ) y) = 1 := by
        rw [inner_integral_char]
        apply fourier_reproKernel_one
        have hsupp : w ∈ Function.support (freqBump k : E k → ℝ) := Function.mem_support.mpr hw
        have hmem : w ∈ Metric.ball (0 : E k) ((freqBump k).rOut) := by
          rwa [← (freqBump k).support_eq]
        have hwn : ‖w‖ < 1/8 := by
          rw [Metric.mem_ball, dist_zero_right] at hmem
          rwa [show (freqBump k).rOut = 1/8 from rfl] at hmem
        calc ‖(R⁻¹ : ℝ) • w + v‖ ≤ ‖(R⁻¹ : ℝ) • w‖ + ‖v‖ := norm_add_le _ _
          _ = R⁻¹ * ‖w‖ + ‖v‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
          _ ≤ 1 * (1/8) + Real.sqrt k := by
                apply add_le_add
                · exact mul_le_mul (inv_le_one_of_one_le₀ hR) (le_of_lt hwn)
                    (norm_nonneg w) zero_le_one
                · exact hv
          _ ≤ Real.sqrt k + 1 := by linarith
      rw [hb, mul_one]
  simp_rw [h2]
  rfl


lemma gammaVec_norm_le_sqrt (k : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    ‖gammaVec k t‖ ≤ Real.sqrt k := by
  have h2 : ‖gammaVec k t‖ ^ 2 ≤ (k : ℝ) := by
    rw [norm_sq_coord_sum]
    calc ∑ j : Fin k, (gammaVec k t j) ^ 2 ≤ ∑ _j : Fin k, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [gammaVec_apply]
          have h1 : |t ^ (j.val + 1)| ≤ 1 := by
            rw [abs_pow]
            exact pow_le_one₀ (abs_nonneg t) ht (n := j.val + 1)
          nlinarith [sq_abs (t ^ (j.val + 1)), abs_nonneg (t ^ (j.val + 1))]
      _ = (k : ℝ) := by simp
  calc ‖gammaVec k t‖ = Real.sqrt (‖gammaVec k t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt k := by norm_num


lemma phiB_norm_le (k : ℕ) (c : E k) (R : ℝ) (x : E k) :
    ‖phiB k c R x‖ ≤ ∫ w : E k, (freqBump k w : ℝ) := by
  unfold phiB
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [norm_mul, Circle.norm_coe, one_mul,
      complex_norm_ofReal_nonneg (freqBump k w) ((freqBump k).nonneg' w)]

lemma exists_upper_bound_phiB (k : ℕ) :
    ∃ C : ℝ, ∀ (c : E k) (R : ℝ) (x : E k), ‖phiB k c R x‖ ≤ C :=
  ⟨_, fun c R x => phiB_norm_le k c R x⟩


lemma extOp_sub_expand (k : ℕ) (g : ℝ → ℂ) (x y : E k) :
    extOp k g 0 1 (x - y)
      = ∫ t in (0:ℝ)..1, (g t * momChar k x t)
          * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ) := by
  rw [extOp]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only []
  rw [momChar_sub]
  ring



lemma continuous_fourierChar_coe :
    Continuous (fun θ : ℝ => ((Real.fourierChar θ : Circle) : ℂ)) := by
  simp only [Real.fourierChar_apply]
  fun_prop

set_option maxHeartbeats 4000000 in
lemma phiB_eq_schwartz (k : ℕ) (c : E k) (R : ℝ) (x : E k) :
    phiB k c R x = (𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) ((R⁻¹ : ℝ) • (x - c)) := by
  rw [phiB_eq_fourierInv]
  rw [← SchwartzMap.fourierInv_coe]

set_option maxHeartbeats 4000000 in
lemma continuous_phiB (k : ℕ) (c : E k) (R : ℝ) :
    Continuous (fun x : E k => phiB k c R x) := by
  have hg : Continuous (fun x : E k =>
      (𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) ((R⁻¹ : ℝ) • (x - c))) :=
    ((𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ)).continuous.comp (by fun_prop)
  exact hg.congr (fun x => (phiB_eq_schwartz k c R x).symm)

set_option maxHeartbeats 4000000 in
lemma integrable_phiB_expansion_prod (k : ℕ) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume) (c : E k) (R : ℝ) (x : E k) :
    Integrable (fun z : ℝ × E k =>
        (phiB k c R (x - z.2) * (reproKernel k : E k → ℂ) z.2)
          * ((g z.1 * momChar k x z.1)
            * ((Real.fourierChar (-⟪z.2, gammaVec k z.1⟫) : Circle) : ℂ)))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) := by
  have hgI : IntegrableOn g (Set.uIoc (0:ℝ) 1) volume := by
    refine hg.mono_set ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self
  have hψ : Integrable (fun y : E k => (reproKernel k : E k → ℂ) y) volume :=
    (reproKernel k).integrable
  have hbound : Integrable (fun z : ℝ × E k =>
      ((∫ w : E k, (freqBump k w : ℝ)) * ‖g z.1‖) * ‖(reproKernel k : E k → ℂ) z.2‖)
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) :=
    (hgI.norm.const_mul _).mul_prod hψ.norm
  refine Integrable.mono' hbound ?_ ?_
  · have hgasm : AEStronglyMeasurable (fun z : ℝ × E k => g z.1)
        ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) :=
      hgI.aestronglyMeasurable.comp_fst (ν := volume)
    have hmt : Continuous (fun z : ℝ × E k => momChar k x z.1) :=
      (momChar_continuous_t k x).comp continuous_fst
    have hmp : Continuous (fun z : ℝ × E k => -⟪z.2, gammaVec k z.1⟫) := by
      have h : (fun z : ℝ × E k => -⟪z.2, gammaVec k z.1⟫)
          = (fun z : ℝ × E k => -momPhase k z.2 z.1) := by
        funext z
        rw [inner_gamma]
      rw [h]
      simp only [momPhase]
      fun_prop
    have hch : Continuous (fun z : ℝ × E k =>
        ((Real.fourierChar (-⟪z.2, gammaVec k z.1⟫) : Circle) : ℂ)) :=
      continuous_fourierChar_coe.comp hmp
    have hψc : Continuous (fun z : ℝ × E k => (reproKernel k : E k → ℂ) z.2) :=
      (reproKernel k).continuous.comp continuous_snd
    have hphc : Continuous (fun z : ℝ × E k => phiB k c R (x - z.2)) :=
      (continuous_phiB k c R).comp ((continuous_const (y := x)).sub continuous_snd)
    exact (hphc.aestronglyMeasurable.mul hψc.aestronglyMeasurable).mul
      ((hgasm.mul hmt.aestronglyMeasurable).mul hch.aestronglyMeasurable)
  · filter_upwards with z
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have h1 : ‖phiB k c R (x - z.2)‖ ≤ ∫ w : E k, (freqBump k w : ℝ) :=
      phiB_norm_le k c R (x - z.2)
    have h2 : ‖((Real.fourierChar (-⟪z.2, gammaVec k z.1⟫) : Circle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    rw [momChar_norm_one, h2, mul_one, mul_one]
    have hC : 0 ≤ ∫ w : E k, (freqBump k w : ℝ) :=
      integral_nonneg (fun w => (freqBump k).nonneg' w)
    have hg0 : 0 ≤ ‖g z.1‖ := norm_nonneg _
    have hψ0 : 0 ≤ ‖(reproKernel k : E k → ℂ) z.2‖ := norm_nonneg _
    nlinarith [h1, hC, hg0, hψ0, mul_nonneg hC hg0, mul_nonneg (mul_nonneg hC hg0) hψ0,
      mul_le_mul_of_nonneg_right h1 (mul_nonneg hg0 hψ0)]

lemma integrable_phiB_expansion (k : ℕ) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume) (c : E k) (R : ℝ) (x : E k) :
    Integrable (Function.uncurry (fun t : ℝ => fun y : E k =>
        (phiB k c R (x - y) * (reproKernel k : E k → ℂ) y)
          * ((g t * momChar k x t) * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ))))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod volume) := by
  exact (integrable_phiB_expansion_prod k g hg c R x).congr
    (Filter.Eventually.of_forall (fun z => rfl))

set_option maxHeartbeats 4000000 in
lemma phiB_extOp_conv_reproKernel (k : ℕ) (g : ℝ → ℂ)
    (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    (c : E k) (R : ℝ) (hR : 1 ≤ R) (x : E k) :
    (∫ y : E k, (phiB k c R (x - y) * extOp k g 0 1 (x - y))
        * (reproKernel k : E k → ℂ) y)
      = phiB k c R x * extOp k g 0 1 x := by
  have h1 : ∀ y : E k, (phiB k c R (x - y) * extOp k g 0 1 (x - y))
        * (reproKernel k : E k → ℂ) y
      = ∫ t in (0:ℝ)..1, (phiB k c R (x - y) * (reproKernel k : E k → ℂ) y)
          * ((g t * momChar k x t)
            * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ)) := by
    intro y
    rw [extOp_sub_expand]
    rw [show (phiB k c R (x - y) * (∫ t in (0:ℝ)..1, (g t * momChar k x t)
              * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ)))
            * (reproKernel k : E k → ℂ) y
          = (∫ t in (0:ℝ)..1, (g t * momChar k x t)
              * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ))
            * (phiB k c R (x - y) * (reproKernel k : E k → ℂ) y) from by ring]
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    ring
  rw [show (∫ y : E k, (phiB k c R (x - y) * extOp k g 0 1 (x - y))
        * (reproKernel k : E k → ℂ) y)
      = ∫ y : E k, ∫ t in (0:ℝ)..1, (phiB k c R (x - y) * (reproKernel k : E k → ℂ) y)
          * ((g t * momChar k x t)
            * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ))
      from integral_congr_ae (Filter.Eventually.of_forall h1)]
  rw [← intervalIntegral_integral_swap (integrable_phiB_expansion k g hg c R x)]
  have h2 : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (∫ y : E k, (phiB k c R (x - y) * (reproKernel k : E k → ℂ) y)
          * ((g t * momChar k x t)
            * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ)))
      = (g t * momChar k x t) * phiB k c R x := by
    intro t ht
    rw [show (fun y : E k => (phiB k c R (x - y) * (reproKernel k : E k → ℂ) y)
              * ((g t * momChar k x t)
                * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ)))
          = fun y => (g t * momChar k x t) * ((phiB k c R (x - y)
              * ((Real.fourierChar (-⟪y, gammaVec k t⟫) : Circle) : ℂ))
              * (reproKernel k : E k → ℂ) y) from by funext y; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact phiB_char_conv k c R hR x (gammaVec k t)
      (gammaVec_norm_le_sqrt k t (by rw [abs_of_nonneg ht.1]; exact ht.2))
  rw [show phiB k c R x * extOp k g 0 1 x
      = ∫ t in (0:ℝ)..1, (g t * momChar k x t) * phiB k c R x from by
    rw [show extOp k g 0 1 x = ∫ t in (0:ℝ)..1, g t * momChar k x t from rfl]
    rw [intervalIntegral.integral_mul_const]
    ring]
  refine intervalIntegral.integral_congr (fun t ht => h2 t ?_)
  rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht

lemma finrank_E (k : ℕ) : Module.finrank ℝ (E k) = k := by
  simp [E, EuclideanSpace]

set_option maxHeartbeats 2000000 in
lemma memLp_phiB (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {p : ℝ} (hp : 0 ≤ p) :
    MemLp (fun y : E k => phiB k c R y) (ENNReal.ofReal p) volume := by
  have hΨ : MemLp ((𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) : E k → ℂ)
      (ENNReal.ofReal p) volume := SchwartzMap.memLp _ _ _
  have hmap : Measure.map (fun z : E k => (R⁻¹ : ℝ) • z) volume
      = ENNReal.ofReal (R ^ k) • volume := by
    rw [MeasureTheory.Measure.map_addHaar_smul volume (r := R⁻¹) (inv_ne_zero hR.ne')]
    rw [finrank_E]
    congr 1
    rw [inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hR.le k)]
  have h1 : MemLp ((𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) : E k → ℂ)
      (ENNReal.ofReal p) (ENNReal.ofReal (R ^ k) • volume) :=
    hΨ.smul_measure ENNReal.ofReal_ne_top
  have h2 : MemLp (fun z : E k => (𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) ((R⁻¹ : ℝ) • z))
      (ENNReal.ofReal p) volume :=
    h1.comp_measurePreserving ⟨(continuous_const_smul _).measurable, hmap⟩
  have htr : MeasurePreserving (fun y : E k => y - c) volume volume := by
    have h := measurePreserving_add_left volume (-c)
    have h2 : (fun x : E k => -c + x) = (fun y : E k => y - c) := by
      funext x; simp [sub_eq_add_neg, add_comm]
    rwa [h2] at h
  have h3 : MemLp (fun y : E k => (𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ)
      ((R⁻¹ : ℝ) • (y - c))) (ENNReal.ofReal p) volume := h2.comp_measurePreserving htr
  rw [show (fun y : E k => phiB k c R y)
      = (fun y : E k => (𝓕⁻ (freqBumpSch k) : SchwartzMap (E k) ℂ) ((R⁻¹ : ℝ) • (y - c)))
      from funext (fun y => phiB_eq_schwartz k c R y)]
  exact h3


open Submission.Vinogradov

set_option maxHeartbeats 2000000 in
lemma continuous_extOp (k : ℕ) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume) :
    Continuous (fun y : E k => extOp k g 0 1 y) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  have hInt := MeasureTheory.continuousAt_of_dominated
    (μ := (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) (x₀ := y₀)
    (F := fun y : E k => fun t : ℝ => g t * momChar k y t)
    (bound := fun t : ℝ => ‖g t‖)
  have hmeas : ∀ᶠ y : E k in nhds y₀,
      AEStronglyMeasurable (fun t : ℝ => g t * momChar k y t)
        ((volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) := by
    filter_upwards with y
    exact hg.aestronglyMeasurable.mul ((momChar_continuous_t k y).aestronglyMeasurable)
  have hbound : ∀ᶠ y : E k in nhds y₀,
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)),
        ‖g t * momChar k y t‖ ≤ ‖g t‖ := by
    filter_upwards with y
    filter_upwards with t
    rw [norm_mul, momChar_norm_one, mul_one]
  have hbint : Integrable (fun t : ℝ => ‖g t‖)
      ((volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) := hg.norm
  have hcont : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)),
      ContinuousAt (fun y : E k => g t * momChar k y t) y₀ := by
    filter_upwards with t
    exact continuousAt_const.mul (momChar_continuous_x k t).continuousAt
  have hc := hInt hmeas hbound hbint hcont
  refine hc.congr (Filter.Eventually.of_forall (fun y => ?_))
  show (∫ t, g t * momChar k y t ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
      = intervalIntegral (fun t : ℝ => g t * momChar k y t) 0 1 volume
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  simp_rw [MeasureTheory.integral_Icc_eq_integral_Ioc]


open Submission.Vinogradov

set_option maxHeartbeats 4000000 in
lemma memLp_locExtOp (k : ℕ) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    (c : E k) {R : ℝ} (hR : 0 < R) {p : ℝ} (hp : 1 ≤ p) :
    MemLp (fun y : E k => phiB k c R y * extOp k g 0 1 y) (ENNReal.ofReal p) volume := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hbase : MemLp (fun y : E k => ‖phiB k c R y‖) (ENNReal.ofReal p) volume :=
    (memLp_phiB k c hR (le_trans zero_le_one hp)).norm
  have hb : MemLp (fun y : E k => (∫ t in (0:ℝ)..1, ‖g t‖) * ‖phiB k c R y‖)
      (ENNReal.ofReal p) volume := by
    have h := hbase.const_smul (𝕜 := ℝ) (∫ t in (0:ℝ)..1, ‖g t‖)
    have hfun : ((∫ t in (0:ℝ)..1, ‖g t‖) • (fun y : E k => ‖phiB k c R y‖))
        = (fun y : E k => (∫ t in (0:ℝ)..1, ‖g t‖) * ‖phiB k c R y‖) := by
      funext y; rw [Pi.smul_apply, smul_eq_mul]
    rwa [hfun] at h
  refine hb.of_le ?_ ?_
  · exact (continuous_phiB k c R).aestronglyMeasurable.mul
      (continuous_extOp k g hg).aestronglyMeasurable
  · filter_upwards with y
    have hM0 : 0 ≤ ∫ t in (0:ℝ)..1, ‖g t‖ :=
      intervalIntegral.integral_nonneg h01 (fun t _ => norm_nonneg (g t))
    have hE : ‖extOp k g 0 1 y‖ ≤ ∫ t in (0:ℝ)..1, ‖g t‖ := extOp_norm_le k g h01 y
    have h1 : ‖phiB k c R y * extOp k g 0 1 y‖ = ‖phiB k c R y‖ * ‖extOp k g 0 1 y‖ :=
      norm_mul _ _
    have h2 : ‖(∫ t in (0:ℝ)..1, ‖g t‖) * ‖phiB k c R y‖‖
        = (∫ t in (0:ℝ)..1, ‖g t‖) * ‖phiB k c R y‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM0, abs_of_nonneg (norm_nonneg _)]
    rw [h1, h2]
    nlinarith [hE, hM0, norm_nonneg (phiB k c R y)]

set_option maxHeartbeats 4000000 in
lemma locExtOp_sup_le (k : ℕ) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    (c : E k) {R : ℝ} (hR : 1 ≤ R) (x : E k) {p q : ℝ} (hpq : Real.HolderConjugate p q)
    (hp : 1 ≤ p) :
    ‖phiB k c R x * extOp k g 0 1 x‖
      ≤ (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ p) ^ (1 / p)
        * (∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ q) ^ (1 / q) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  rw [← phiB_extOp_conv_reproKernel k g hg c R hR x]
  exact Commons.Analysis.Integral.integral_norm_mul_sub_le hpq
    (memLp_locExtOp k g hg c hRpos hp) ((reproKernel k).memLp (ENNReal.ofReal q) volume) x


open Submission.Vinogradov

set_option maxHeartbeats 4000000 in
lemma rpow_alg {P Q Pv C : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q) (hPQ : P ≤ Q)
    (hPv0 : 0 ≤ Pv) (hC0 : 0 ≤ C) :
    ((Pv * C) ^ (Q - P) * Pv ^ P) ^ (1 / Q) = C ^ (1 - P / Q) * Pv := by
  rcases eq_or_lt_of_le hPv0 with h | h
  · rw [← h]
    rw [mul_zero, Real.zero_rpow hP0.ne', mul_zero, Real.zero_rpow (one_div_ne_zero hQ0.ne')]
  · have e1 : Pv ^ (Q - P) * Pv ^ P = Pv ^ Q := by
      rw [← Real.rpow_add h, show (Q - P) + P = Q from by ring]
    rw [Real.mul_rpow hPv0 hC0, mul_assoc, mul_comm (C ^ (Q - P)) (Pv ^ P), ← mul_assoc, e1]
    rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt h) Q) (Real.rpow_nonneg hC0 (Q - P))]
    rw [← Real.rpow_mul (le_of_lt h), ← Real.rpow_mul hC0]
    rw [show Q * (1 / Q) = 1 from by field_simp]
    rw [show (Q - P) * (1 / Q) = 1 - P / Q from by field_simp]
    rw [Real.rpow_one]
    ring

set_option maxHeartbeats 4000000 in
lemma locExtOp_Lq_le_Lp (k : ℕ) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    (c : E k) {R : ℝ} (hR : 1 ≤ R) {P Q Pd : ℝ} (hPQ : P ≤ Q) (hP : 1 < P)
    (hPd : Real.HolderConjugate P Pd) :
    (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ Q) ^ (1/Q)
      ≤ ((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd)) ^ (1 - P/Q)
        * (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (1/P) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hP1 : 1 ≤ P := le_of_lt hP
  have hQ0 : 0 < Q := lt_of_lt_of_le hP0 hPQ
  set h : E k → ℂ := fun y => phiB k c R y * extOp k g 0 1 y with hh
  have hMp : MemLp h (ENNReal.ofReal P) volume := memLp_locExtOp k g hg c hRpos hP1
  have hIntp : Integrable (fun y : E k => ‖h y‖ ^ P) volume := by
    have h1 := hMp.integrable_norm_rpow (p := ENNReal.ofReal P)
      (ENNReal.ofReal_ne_zero_iff.mpr hP0)
    simpa [ENNReal.toReal_ofReal hP0.le] using h1
  set C : ℝ := (∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd) with hC
  set Pv : ℝ := (∫ y, ‖h y‖ ^ P) ^ (1/P) with hPv
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hPv0 : 0 ≤ Pv := by rw [hPv]; positivity
  have hsup : ∀ x, ‖h x‖ ≤ Pv * C := by
    intro x
    have := locExtOp_sup_le k g hg c hR x hPd hP1
    simpa only [hh, hC, hPv] using this
  have hM : 0 ≤ Pv * C := mul_nonneg hPv0 hC0
  have hpoint : ∀ y : E k, ‖h y‖ ^ Q ≤ (Pv * C) ^ (Q - P) * ‖h y‖ ^ P := by
    intro y
    set n : ℝ := ‖h y‖ with hn
    have hn0 : 0 ≤ n := norm_nonneg _
    have hsplit : n ^ Q = n ^ (Q - P) * n ^ P := by
      rcases eq_or_lt_of_le hn0 with h0 | h0
      · rw [← h0, Real.zero_rpow hQ0.ne', Real.zero_rpow hP0.ne', mul_zero]
      · rw [← Real.rpow_add h0]; ring_nf
    have hle : n ^ (Q - P) ≤ (Pv * C) ^ (Q - P) :=
      Real.rpow_le_rpow hn0 (hsup y) (by linarith)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hn0 P)
  have hIntq : Integrable (fun y : E k => ‖h y‖ ^ Q) volume := by
    have hcont : Continuous (fun y : E k => ‖h y‖ ^ Q) :=
      (((continuous_phiB k c R).mul (continuous_extOp k g hg)).norm).rpow_const
        (fun y => Or.inr hQ0.le)
    refine Integrable.mono' (hIntp.const_mul ((Pv * C) ^ (Q - P)))
      hcont.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) Q)]
    exact hpoint y
  have hkey : (∫ y : E k, ‖h y‖ ^ Q) ≤ (Pv * C) ^ (Q - P) * (∫ y : E k, ‖h y‖ ^ P) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono hIntq (hIntp.const_mul _) (fun y => hpoint y)
  have hPvP : Pv ^ P = ∫ y : E k, ‖h y‖ ^ P := by
    rw [hPv, one_div]
    exact Real.rpow_inv_rpow (x := ∫ y : E k, ‖h y‖ ^ P)
      (integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) P)) hP0.ne'
  have hfin : (∫ y : E k, ‖h y‖ ^ Q) ^ (1 / Q) ≤ C ^ (1 - P / Q) * Pv := by
    refine le_trans (Real.rpow_le_rpow ?_ hkey (by positivity)) ?_
    · exact integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) Q)
    · rw [← hPvP]; exact le_of_eq (rpow_alg hP0 hQ0 hPQ hPv0 hC0)
  exact hfin

lemma freqBump_integral_pos (k : ℕ) : 0 < ∫ w : E k, (freqBump k w : ℝ) := by
  have hsupp : Function.support (freqBump k : E k → ℝ) = Metric.ball (0 : E k) (1 / 8) :=
    (freqBump k).support_eq
  have hpos : 0 < volume (Function.support (freqBump k : E k → ℝ)) := by
    rw [hsupp]
    exact Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self (by norm_num)⟩
  have hnn : 0 ≤ᵐ[volume] (freqBump k : E k → ℝ) :=
    Filter.Eventually.of_forall (fun w => (freqBump k).nonneg' w)
  have := (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnn (freqBump k).integrable).mpr hpos
  simpa using this

lemma phiB_re_lower (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {x : E k}
    (hx : ‖x - c‖ ≤ R) :
    (1/2) * (∫ w : E k, (freqBump k w : ℝ)) ≤ (phiB k c R x).re := by
  have hu : ‖(R⁻¹ : ℝ) • (x - c)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    simpa [inv_mul_eq_div] using (div_le_one hR).mpr hx
  have hfun : (fun w : E k => ((freqBump k w : ℝ) : ℂ)) = (freqBumpSch k : E k → ℂ) := by
    funext w; exact (freqBumpSch_coe k w).symm
  have hsupp : ∀ w : E k, 1/8 < ‖w‖ → (freqBump k w : ℝ) = 0 := by
    intro w hw
    by_contra hne
    have hmem : w ∈ Function.support (freqBump k : E k → ℝ) := hne
    rw [(freqBump k).support_eq, Metric.mem_ball, dist_zero_right] at hmem
    rw [show (freqBump k).rOut = 1/8 from rfl] at hmem
    linarith
  have h := Commons.Analysis.Fourier.half_integral_le_re_fourierInv
    (ρ := fun w : E k => (freqBump k w : ℝ))
    (fun w => (freqBump k).nonneg' w) (freqBump k).integrable hsupp
    ((R⁻¹ : ℝ) • (x - c)) hu
  rwa [hfun, ← phiB_eq_fourierInv] at h


open Submission.Vinogradov

/-- The mass of the localizing bump. -/
noncomputable def phiBMass (k : ℕ) : ℝ := (1/2) * (∫ w : E k, (freqBump k w : ℝ))

lemma phiBMass_pos (k : ℕ) : 0 < phiBMass k := by
  unfold phiBMass; linarith [freqBump_integral_pos k]

lemma phiB_norm_ge (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {x : E k} (hx : ‖x - c‖ ≤ R) :
    phiBMass k ≤ ‖phiB k c R x‖ := by
  refine le_trans (phiB_re_lower k c hR hx) ?_
  exact Complex.re_le_norm _

set_option maxHeartbeats 8000000 in
lemma integrable_locExtOp_Lq (k : ℕ) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    (c : E k) {R : ℝ} (hR : 1 ≤ R) {P Q Pd : ℝ} (hPQ : P ≤ Q) (hP : 1 < P)
    (hPd : Real.HolderConjugate P Pd) :
    Integrable (fun y : E k => ‖phiB k c R y * extOp k g 0 1 y‖ ^ Q) volume := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hP1 : 1 ≤ P := le_of_lt hP
  have hQ0 : 0 < Q := lt_of_lt_of_le hP0 hPQ
  set h : E k → ℂ := fun y => phiB k c R y * extOp k g 0 1 y with hh
  have hMp : MemLp h (ENNReal.ofReal P) volume := memLp_locExtOp k g hg c hRpos hP1
  have hIntp : Integrable (fun y : E k => ‖h y‖ ^ P) volume := by
    have h1 := hMp.integrable_norm_rpow (p := ENNReal.ofReal P)
      (ENNReal.ofReal_ne_zero_iff.mpr hP0)
    simpa [ENNReal.toReal_ofReal hP0.le] using h1
  set C : ℝ := (∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd) with hC
  set Pv : ℝ := (∫ y, ‖h y‖ ^ P) ^ (1/P) with hPv
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hPv0 : 0 ≤ Pv := by rw [hPv]; positivity
  have hsup : ∀ x, ‖h x‖ ≤ Pv * C := by
    intro x
    have := locExtOp_sup_le k g hg c hR x hPd hP1
    simpa only [hh, hC, hPv] using this
  have hcont : Continuous (fun y : E k => ‖h y‖ ^ Q) :=
    (((continuous_phiB k c R).mul (continuous_extOp k g hg)).norm).rpow_const
      (fun y => Or.inr hQ0.le)
  have hpoint : ∀ y : E k, ‖h y‖ ^ Q ≤ (Pv * C) ^ (Q - P) * ‖h y‖ ^ P := by
    intro y
    set n : ℝ := ‖h y‖ with hn
    have hn0 : 0 ≤ n := norm_nonneg _
    have hsplit : n ^ Q = n ^ (Q - P) * n ^ P := by
      rcases eq_or_lt_of_le hn0 with h0 | h0
      · rw [← h0, Real.zero_rpow hQ0.ne', Real.zero_rpow hP0.ne', mul_zero]
      · rw [← Real.rpow_add h0]; ring_nf
    have hle : n ^ (Q - P) ≤ (Pv * C) ^ (Q - P) :=
      Real.rpow_le_rpow hn0 (hsup y) (by linarith)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hn0 P)
  refine Integrable.mono' (hIntp.const_mul ((Pv * C) ^ (Q - P))) hcont.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) Q)]
  exact hpoint y

set_option maxHeartbeats 8000000 in
lemma extOp_ball_Lq_le (k : ℕ) (g : ℝ → ℂ) (hg : IntegrableOn g (Set.Icc (0:ℝ) 1) volume)
    (c : E k) {R : ℝ} (hR : 1 ≤ R) {P Q Pd : ℝ} (hPQ : P ≤ Q) (hP : 1 < P)
    (hPd : Real.HolderConjugate P Pd) :
    ∫ x in Metric.ball c R, ‖extOp k g 0 1 x‖ ^ Q
      ≤ (phiBMass k) ^ (-Q)
        * ((((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd)) ^ (1 - P/Q)) ^ Q)
        * (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (Q/P) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hQ0 : 0 < Q := lt_of_lt_of_le hP0 hPQ
  have hmass : 0 < phiBMass k := phiBMass_pos k
  have hIntq : Integrable (fun x : E k => ‖phiB k c R x * extOp k g 0 1 x‖ ^ Q) volume :=
    integrable_locExtOp_Lq k g hg c hR hPQ hP hPd
  have hpoint : ∀ x ∈ Metric.ball c R,
      ‖extOp k g 0 1 x‖ ^ Q ≤ (phiBMass k) ^ (-Q) * ‖phiB k c R x * extOp k g 0 1 x‖ ^ Q := by
    intro x hx
    have hxc : ‖x - c‖ ≤ R := le_of_lt (Metric.mem_ball.mp hx)
    have h1 : phiBMass k * ‖extOp k g 0 1 x‖ ≤ ‖phiB k c R x * extOp k g 0 1 x‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (phiB_norm_ge k c hRpos hxc) (norm_nonneg _)
    have hpos : 0 < (phiBMass k) ^ Q := Real.rpow_pos_of_pos hmass Q
    rw [Real.rpow_neg (le_of_lt hmass), inv_mul_eq_div, le_div_iff₀ hpos, mul_comm,
        ← Real.mul_rpow (le_of_lt hmass) (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) h1 hQ0.le
  have step1 : ∫ x in Metric.ball c R, ‖extOp k g 0 1 x‖ ^ Q
      ≤ ∫ x in Metric.ball c R,
          (phiBMass k) ^ (-Q) * ‖phiB k c R x * extOp k g 0 1 x‖ ^ Q := by
    refine integral_mono_of_nonneg (μ := volume.restrict (Metric.ball c R))
      (f := fun x : E k => ‖extOp k g 0 1 x‖ ^ Q)
      (g := fun x : E k => (phiBMass k) ^ (-Q) * ‖phiB k c R x * extOp k g 0 1 x‖ ^ Q) ?_ ?_ ?_
    · filter_upwards with x; exact Real.rpow_nonneg (norm_nonneg _) Q
    · exact (hIntq.const_mul _).mono_measure Measure.restrict_le_self
    · filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
      exact hpoint x hx
  have step2 : ∫ x in Metric.ball c R,
        (phiBMass k) ^ (-Q) * ‖phiB k c R x * extOp k g 0 1 x‖ ^ Q
      ≤ (phiBMass k) ^ (-Q) * ∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ Q := by
    have h := MeasureTheory.setIntegral_le_integral (μ := volume) (s := Metric.ball c R)
      (f := fun x : E k => (phiBMass k) ^ (-Q) * ‖phiB k c R x * extOp k g 0 1 x‖ ^ Q)
      (hIntq.const_mul _)
      (Filter.Eventually.of_forall (fun x => mul_nonneg
        (Real.rpow_nonneg (le_of_lt hmass) (-Q)) (Real.rpow_nonneg (norm_nonneg _) Q)))
    have h2 : ∫ x : E k, (phiBMass k) ^ (-Q) * ‖phiB k c R x * extOp k g 0 1 x‖ ^ Q
        = (phiBMass k) ^ (-Q) * ∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ Q :=
      MeasureTheory.integral_const_mul _ _
    rwa [h2] at h
  have step3 : ∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ Q
      ≤ ((((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd)) ^ (1 - P/Q))
          * (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (1/P)) ^ Q := by
    have h0 : 0 ≤ ∫ y : E k, ‖phiB k c R y * extOp k g 0 1 y‖ ^ Q :=
      integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) Q)
    have h3 := locExtOp_Lq_le_Lp k g hg c hR hPQ hP hPd
    have h4 := Real.rpow_le_rpow (Real.rpow_nonneg h0 (1/Q)) h3 hQ0.le
    rwa [← Real.rpow_mul h0, show (1/Q)*Q = 1 from by field_simp, Real.rpow_one] at h4
  have hA0 : 0 ≤ ((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd)) ^ (1 - P/Q) :=
    Real.rpow_nonneg (Real.rpow_nonneg (integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) Pd)) _) _
  have hB0 : 0 ≤ (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (1/P) :=
    Real.rpow_nonneg (integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) P)) _
  calc ∫ x in Metric.ball c R, ‖extOp k g 0 1 x‖ ^ Q
      ≤ (phiBMass k) ^ (-Q) * ∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ Q :=
        le_trans step1 step2
    _ ≤ (phiBMass k) ^ (-Q)
          * ((((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd)) ^ (1 - P/Q))
              * (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (1/P)) ^ Q :=
        mul_le_mul_of_nonneg_left step3 (Real.rpow_nonneg (le_of_lt hmass) (-Q))
    _ = (phiBMass k) ^ (-Q)
          * ((((∫ y, ‖(reproKernel k : E k → ℂ) y‖ ^ Pd) ^ (1/Pd)) ^ (1 - P/Q)) ^ Q)
          * (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (Q/P) := by
        rw [Real.mul_rpow hA0 hB0]
        have hBQ : ((∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (1/P)) ^ Q
            = (∫ y, ‖phiB k c R y * extOp k g 0 1 y‖ ^ P) ^ (Q/P) := by
          rw [← Real.rpow_mul (integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) P))]
          congr 1
          ring
        rw [hBQ]
        ring

end
end Submission.Vinogradov
end
