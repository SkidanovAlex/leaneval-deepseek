import Mathlib
import Submission.Commons.Analysis.Integral.circle_avg_inv_sub_le_phiFun
import Submission.Commons.Analysis.Integral.phiFun_nonneg_of_le_eighth
import Submission.Commons.Analysis.Integral.abs_phiFun_le_six_mul
import Submission.Commons.Analysis.Integral.integral_phi_rpow_neg_three_halves_neg
import Submission.Commons.Analysis.Integral.integrableOn_inv_norm_parabolic_ramp
import Submission.Commons.Analysis.Integral.integrableOn_phiFun_stdVarRamp_integrand
import Submission.Commons.Analysis.Integral.integral_phiFun_stdVarRamp_realpow_le

namespace Commons.Analysis.Integral

open MeasureTheory Set Real
open scoped Interval InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖cos θ • e + sin θ • f‖ = 1` for an orthonormal pair `e, f`. -/
private lemma norm_circVec_eq_one (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (θ : ℝ) :
    ‖Real.cos θ • e + Real.sin θ • f‖ = 1 := by
  have h : ‖Real.cos θ • e + Real.sin θ • f‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hef, mul_zero,
        norm_smul, norm_smul, he, hf, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [mul_one, mul_one, sq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (Real.cos θ • e + Real.sin θ • f), h]

/-- The ramp `t ↦ min ρ (max 0 (T - t))` differs from the parabolic radius
`t ↦ c t ^ (2/3) z` almost everywhere on `(0, T]`. -/
private lemma ae_rampD_ne_parA {c T ρ z : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
      min ρ (max 0 (T - t)) ≠ c * t ^ ((2:ℝ)/3) * z := by
  have hdecr : ∀ s t : ℝ, 0 < s → s < t →
      min ρ (max 0 (T - t)) - c * t ^ ((2:ℝ)/3) * z
        < min ρ (max 0 (T - s)) - c * s ^ ((2:ℝ)/3) * z := by
    intro s t hs hst
    have ht0 : 0 < t := lt_trans hs hst
    have hdd : min ρ (max 0 (T - t)) ≤ min ρ (max 0 (T - s)) :=
      min_le_min_left ρ (max_le_max_left 0 (by linarith))
    have haa : c * s ^ ((2:ℝ)/3) * z < c * t ^ ((2:ℝ)/3) * z := by
      have h1 : s ^ ((2:ℝ)/3) < t ^ ((2:ℝ)/3) :=
        Real.rpow_lt_rpow hs.le hst (by norm_num)
      have hcz : (0:ℝ) < c * z := mul_pos hc hz
      calc c * s ^ ((2:ℝ)/3) * z = (c * z) * s ^ ((2:ℝ)/3) := by ring
        _ < (c * z) * t ^ ((2:ℝ)/3) := mul_lt_mul_of_pos_left h1 hcz
        _ = c * t ^ ((2:ℝ)/3) * z := by ring
    linarith
  have hsub : (Set.Ioc (0:ℝ) T ∩
      {t : ℝ | min ρ (max 0 (T - t)) = c * t ^ ((2:ℝ)/3) * z}).Subsingleton := by
    rintro s ⟨hsI, hsS⟩ t ⟨htI, htS⟩
    rcases lt_trichotomy s t with h | h | h
    · exfalso
      have := hdecr s t hsI.1 h
      rw [← hsS, ← htS] at this
      linarith
    · exact h
    · exfalso
      have := hdecr t s htI.1 h
      rw [← hsS, ← htS] at this
      linarith
  have hnull : volume (Set.Ioc (0:ℝ) T ∩
      {t : ℝ | min ρ (max 0 (T - t)) = c * t ^ ((2:ℝ)/3) * z}) = 0 := by
    obtain he | ⟨x, hx⟩ := hsub.eq_empty_or_singleton
    · rw [he]; simp
    · rw [hx]; simp
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
  have hset : {t : ℝ | ¬ (t ∈ Set.Ioc 0 T →
        min ρ (max 0 (T - t)) ≠ c * t ^ ((2:ℝ)/3) * z)}
      = Set.Ioc (0:ℝ) T ∩ {t : ℝ | min ρ (max 0 (T - t)) = c * t ^ ((2:ℝ)/3) * z} := by
    ext t; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioc]; tauto
  rw [hset]
  exact hnull

/-- Pointwise (in `t`) transfer inequality for the `θ`-average of `1/‖A + d e_θ‖`. -/
private lemma theta_sec_bound (e f xi : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) {c T ρ z : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z)
    (hxi : ‖xi‖ = z) {t : ℝ} (ht : 0 < t)
    (hne : min ρ (max 0 (T - t)) ≠ c * t ^ ((2:ℝ)/3) * z) :
    (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹)
      ≤ (1 / (c * t ^ ((2:ℝ)/3) * z)) *
          ((1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
            (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
              + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos θ)
              ^ (-(1:ℝ)/2)) - 1)) := by
  set Phi : ℝ := (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
            (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
              + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos θ)
              ^ (-(1:ℝ)/2)) - 1) with hPhi
  have ht0 : (0:ℝ) < c * t ^ ((2:ℝ)/3) * z :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos ht _)) hz
  have hA : ‖(c * t ^ ((2:ℝ)/3)) • xi‖ = c * t ^ ((2:ℝ)/3) * z := by
    rw [norm_smul, Real.norm_eq_abs, hxi, abs_of_nonneg (by positivity)]
  have hd0 : 0 ≤ min ρ (max 0 (T - t)) := le_min hρ.le (le_max_left _ _)
  have hApos : 0 < ‖(c * t ^ ((2:ℝ)/3)) • xi‖ := by rw [hA]; exact ht0
  have hne' : min ρ (max 0 (T - t)) ≠ ‖(c * t ^ ((2:ℝ)/3)) • xi‖ := by rw [hA]; exact hne
  have hmain := circle_avg_inv_sub_le_phiFun e f
      ((c * t ^ ((2:ℝ)/3)) • xi) he hf hef hd0 hApos hne'
  rw [hA] at hmain
  rw [← hPhi] at hmain
  have hneq : ∀ θ : ℝ, (c * t ^ ((2:ℝ)/3)) • xi
      + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f) ≠ 0 := by
    intro θ h0
    have h1 : ‖(c * t ^ ((2:ℝ)/3)) • xi‖
        = ‖(min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖ := by
      have h2 : (c * t ^ ((2:ℝ)/3)) • xi
          = -((min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)) :=
        eq_neg_of_add_eq_zero_left h0
      rw [h2, norm_neg]
    rw [hA, norm_smul, norm_circVec_eq_one e f he hf hef θ, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hd0] at h1
    exact hne h1.symm
  have hcont : ContinuousOn (fun θ : ℝ =>
      (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹)
      (Set.uIcc 0 (2 * Real.pi)) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro θ _
      exact norm_ne_zero_iff.mpr (hneq θ)
  have hint : IntervalIntegrable (fun θ : ℝ =>
      (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹)
      volume 0 (2 * Real.pi) := hcont.intervalIntegrable
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  have key : (1 / (2 * Real.pi)) *
        ((∫ θ in (0)..(2 * Real.pi),
            (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹)
          - (2 * Real.pi) * (c * t ^ ((2:ℝ)/3) * z)⁻¹)
      = (1 / (2 * Real.pi)) *
          (∫ θ in (0)..(2 * Real.pi),
            (‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹)
        - (c * t ^ ((2:ℝ)/3) * z)⁻¹ := by
    rw [mul_sub]
    congr 1
    field_simp
  rw [key]
  have hgoal : (1 / (c * t ^ ((2:ℝ)/3) * z)) * Phi
      = (1 + Phi) / (c * t ^ ((2:ℝ)/3) * z) - (c * t ^ ((2:ℝ)/3) * z)⁻¹ := by
    field_simp
    ring
  rw [hgoal]
  linarith [hmain]

/-- Integrability of `t ↦ (c t^{2/3} z)^{-1}` on `(0, T]`. -/
private lemma integrableOn_parA_inv_Ioc {c T z : ℝ} (hc : 0 < c) (hT : 0 < T) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => (c * t ^ ((2:ℝ)/3) * z)⁻¹) (Set.Ioc 0 T) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2:ℝ)/3)) (Set.Ioc (0:ℝ) T) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : IntegrableOn (fun t : ℝ => (c * z)⁻¹ * t ^ (-(2:ℝ)/3)) (Set.Ioc (0:ℝ) T) :=
    hbase.const_mul _
  refine h2.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have e1 : t ^ (-(2:ℝ)/3) = (t ^ ((2:ℝ)/3))⁻¹ := by
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by ring, Real.rpow_neg ht0.le]
  rw [e1, show c * t ^ ((2:ℝ)/3) * z = (c * z) * t ^ ((2:ℝ)/3) by ring]
  simp only [mul_inv]

/-- Integrability of the `- ‖A‖^{-1}` part of the transfer integrand on the rectangle. -/
private lemma integrableOn_parA_inv_prod {c T z : ℝ} (hc : 0 < c) (hT : 0 < T) (hz : 0 < z) :
    IntegrableOn (fun p : ℝ × ℝ => (c * p.2 ^ ((2:ℝ)/3) * z)⁻¹)
      (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 T) := by
  have hT' : Integrable (fun t : ℝ => (c * t ^ ((2:ℝ)/3) * z)⁻¹)
      (volume.restrict (Set.uIoc 0 T)) := by
    rw [Set.uIoc_of_le hT.le]; exact integrableOn_parA_inv_Ioc hc hT hz
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    rw [isFiniteMeasure_restrict, Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hmain := hT'.comp_snd (volume.restrict (Set.uIoc 0 (2 * Real.pi)))
  rw [MeasureTheory.Measure.prod_restrict] at hmain
  exact hmain

/-- The transfer integrand is integrable on the rectangle. -/
private lemma integrableOn_rampS (e f xi : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ)
    (hρT : ρ ≤ T) (hxi : ‖xi‖ = z) (hz : 0 < z) :
    IntegrableOn
      (Function.uncurry (fun θ t : ℝ => (‖(c * t ^ ((2:ℝ)/3)) • xi
          + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
            - (c * t ^ ((2:ℝ)/3) * z)⁻¹))
      (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 T) := by
  exact (Commons.Analysis.Integral.integrableOn_inv_norm_parabolic_ramp e f xi he hf hef
      hc hT hρ hρT hxi hz).sub (integrableOn_parA_inv_prod hc hT hz)

/-- The model transfer integrand is integrable on `(0, T]`. -/
private lemma integrableOn_phiModel {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ)
    (hρT : ρ ≤ T) (hz : 0 < z) :
    IntegrableOn
      (fun t : ℝ => (1 / (c * t ^ ((2:ℝ)/3) * z)) *
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
          (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
              + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos theta)
              ^ (-(1:ℝ)/2)) - 1)))
      (Set.Ioc 0 T) :=
  Commons.Analysis.Integral.integrableOn_phiFun_stdVarRamp_integrand hc hT hρ hρT hz

/-- The `t`-marginal of the transfer integrand is integrable on `(0, T]`. -/
private lemma integrableOn_thetaMarginal (e f xi : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ)
    (hρT : ρ ≤ T) (hxi : ‖xi‖ = z) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹)) (Set.Ioc 0 T) := by
  have hI := integrableOn_rampS e f xi he hf hef hc hT hρ hρT hxi hz
  have hI' : Integrable (fun p : ℝ × ℝ => (‖(c * p.2 ^ ((2:ℝ)/3)) • xi
      + (min ρ (max 0 (T - p.2))) • (Real.cos p.1 • e + Real.sin p.1 • f)‖)⁻¹
        - (c * p.2 ^ ((2:ℝ)/3) * z)⁻¹)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod (volume.restrict (Set.uIoc 0 T))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hI
  have hmarg := hI'.integral_prod_right
  rw [Set.uIoc_of_le hT.le] at hmarg
  refine (hmarg.const_mul (1 / (2 * Real.pi))).congr ?_
  apply Filter.Eventually.of_forall
  intro t
  simp only []
  have hfun : (∫ θ, (‖(c * t ^ ((2:ℝ)/3)) • xi
          + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
            - (c * t ^ ((2:ℝ)/3) * z)⁻¹ ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))))
      = ∫ θ in (0)..(2 * Real.pi), ((‖(c * t ^ ((2:ℝ)/3)) • xi
          + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
            - (c * t ^ ((2:ℝ)/3) * z)⁻¹) := by
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  rw [hfun]


theorem integral_theta_model_potential_realpow_le_strict {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e f xi : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ < T)
    (hxi : ‖xi‖ = z) (hz : 0 < z)
    (hsmall : ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) ≤ 1/8) :
    (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (∫ t in (0:ℝ)..T,
            (‖(c * t ^ ((2:ℝ)/3)) • xi
                + (min ρ (max 0 (T - t))) • (Real.cos theta • e + Real.sin theta • f)‖)⁻¹
              - (c * t ^ ((2:ℝ)/3) * z)⁻¹)
      ≤ (3/2) * ρ ^ ((1:ℝ)/2) * c ^ (-(3:ℝ)/2) * z ^ (-(3:ℝ)/2)
          * (∫ v in Set.Ioi (0:ℝ),
              ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
                (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1))
                * v ^ (-(3 : ℝ) / 2))
        + 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := by
  have hIntS := integrableOn_rampS e f xi he hf hef hc hT hρ hρT.le hxi hz
  have hJF := integrableOn_thetaMarginal e f xi he hf hef hc hT hρ hρT.le hxi hz
  have hJG := integrableOn_phiModel hc hT hρ hρT.le hz
  have hswap : (∫ θ in (0)..(2 * Real.pi), ∫ t in (0:ℝ)..T,
        ((‖(c * t ^ ((2:ℝ)/3)) • xi
            + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹))
      = ∫ t in (0:ℝ)..T, ∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ ((2:ℝ)/3)) • xi
            + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹) :=
    intervalIntegral_intervalIntegral_swap hIntS
  rw [hswap]
  have hbound : (fun t : ℝ => (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹))
      ≤ᵐ[volume.restrict (Set.Ioc 0 T)]
      (fun t : ℝ => (1 / (c * t ^ ((2:ℝ)/3) * z)) *
        ((1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
          (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
              + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos θ)
              ^ (-(1:ℝ)/2)) - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_rampD_ne_parA (T := T) hc hρ hz]
      with t ht hne
    exact theta_sec_bound e f xi he hf hef hc hρ hz hxi ht.1 hne
  have hcmp : (∫ t in (0:ℝ)..T, (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ ((2:ℝ)/3)) • xi + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹))
      ≤ ∫ t in (0:ℝ)..T, (1 / (c * t ^ ((2:ℝ)/3) * z)) *
        ((1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
          (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
              + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos θ)
              ^ (-(1:ℝ)/2)) - 1)) := by
    rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le]
    exact integral_mono_ae hJF hJG hbound
  calc (1 / (2 * Real.pi)) * ∫ t in (0:ℝ)..T, ∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ ((2:ℝ)/3)) • xi
            + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹)
      = ∫ t in (0:ℝ)..T, (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
        ((‖(c * t ^ ((2:ℝ)/3)) • xi
            + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * z)⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ t in (0:ℝ)..T, (1 / (c * t ^ ((2:ℝ)/3) * z)) *
        ((1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi),
          (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
              + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos θ)
              ^ (-(1:ℝ)/2)) - 1)) := hcmp
    _ ≤ (3/2) * ρ ^ ((1:ℝ)/2) * c ^ (-(3:ℝ)/2) * z ^ (-(3:ℝ)/2)
          * (∫ v in Set.Ioi (0:ℝ),
              ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
                (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1))
                * v ^ (-(3 : ℝ) / 2))
        + 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := by
        exact Commons.Analysis.Integral.integral_phiFun_stdVarRamp_realpow_le hc hT hρ hρT hz hsmall


end Commons.Analysis.Integral
