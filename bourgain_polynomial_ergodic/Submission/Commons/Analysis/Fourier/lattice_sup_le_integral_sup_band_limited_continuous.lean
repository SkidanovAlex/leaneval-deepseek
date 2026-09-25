import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.PSeries
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution

open MeasureTheory
open scoped FourierTransform

namespace Commons.Analysis.Fourier
noncomputable section

private def betaBump : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
private def betaC : ℝ → ℂ := fun x => ((betaBump x : ℝ) : ℂ)
private lemma betaC_contDiff : ContDiff ℝ (⊤ : ℕ∞) betaC :=
  Complex.ofRealCLM.contDiff.comp betaBump.contDiff
private lemma betaC_hcs : HasCompactSupport betaC :=
  (betaBump.hasCompactSupport (E := ℝ)).comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)
private def betaS : SchwartzMap ℝ ℂ := betaC_hcs.toSchwartzMap betaC_contDiff
private lemma betaS_coe : (betaS : ℝ → ℂ) = betaC :=
  funext (betaC_hcs.toSchwartzMap_toFun betaC_contDiff)
private lemma betaC_eq_one (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1/2) : ℝ) (1/2)) : betaC ξ = 1 := by
  have hr : betaBump.rIn = (1/2 : ℝ) := rfl
  have hmem : ξ ∈ Metric.closedBall (0 : ℝ) betaBump.rIn := by
    rw [Real.closedBall_eq_Icc, hr]; norm_num; exact hξ
  have h1 := betaBump.one_of_mem_closedBall hmem
  simp only [betaC]; rw [h1, Complex.ofReal_one]
private def KS : SchwartzMap ℝ ℂ := (𝓕⁻ betaS : SchwartzMap ℝ ℂ)
private def K : ℝ → ℂ := fun x => KS x
private lemma K_fourier_eq_one (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1/2) : ℝ) (1/2)) :
    𝓕 K ξ = 1 := by
  have hKS : KS = (𝓕⁻ betaS : SchwartzMap ℝ ℂ) := rfl
  have hfourier : (𝓕 KS : SchwartzMap ℝ ℂ) = betaS := by
    rw [hKS, FourierInvPair.fourier_fourierInv_eq]
  have h1 : 𝓕 K = ⇑betaS := by
    change 𝓕 (⇑KS) = ⇑betaS
    rw [← SchwartzMap.fourier_coe KS, hfourier]
  rw [h1, betaS_coe]; exact betaC_eq_one ξ hξ
private lemma K_decay : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2) := by
  set S0 : ℝ := (SchwartzMap.seminorm ℂ 0 0) KS with hS0
  set S2 : ℝ := (SchwartzMap.seminorm ℂ 2 0) KS with hS2
  refine ⟨max (S0 + S2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have h0 : ‖KS x‖ ≤ S0 := SchwartzMap.norm_le_seminorm ℂ KS x
  have h2 : ‖x‖ ^ 2 * ‖KS x‖ ≤ S2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ KS 2 x
  have hx2 : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hx2] at h2
  have hsum : (1 + x^2) * ‖KS x‖ ≤ S0 + S2 := by nlinarith [h0, h2]
  have hle : ‖KS x‖ ≤ max (S0 + S2) 1 / (1 + x^2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsum, le_max_left (S0+S2) 1, le_max_right (S0+S2) 1]
  simpa only [K, KS] using hle
private lemma fourierInv_betaC_eq_K : (𝓕⁻ betaC : ℝ → ℂ) = K := by
  have h1 : (𝓕⁻ betaC : ℝ → ℂ) = ⇑(𝓕⁻ betaS : SchwartzMap ℝ ℂ) := by
    rw [← betaS_coe, ← SchwartzMap.fourierInv_coe betaS]
  rw [h1]; rfl
private lemma betaC_integrable : Integrable betaC :=
  betaC_contDiff.continuous.integrable_of_hasCompactSupport betaC_hcs

private lemma fourier_integrable_of_band (g : ℝ → ℂ) (hg : Integrable g)
    (hbl : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) → 𝓕 g ξ = 0) :
    Integrable (𝓕 g) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  · refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(1/2) : ℝ) (1/2)) isCompact_Icc ?_
    intro ξ hξ; by_contra h; exact hξ (hbl ξ h)

private lemma reproducing (g : ℝ → ℂ) (hg : Integrable g)
    (hbl : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) → 𝓕 g ξ = 0) (x : ℝ)
    (hx : ContinuousAt g x) : g x = ∫ y : ℝ, g y * K (x - y) := by
  have hfg : Integrable (𝓕 g) := fourier_integrable_of_band g hg hbl
  have hconv := Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution betaC_integrable hg x
  have hcongr : (fun ξ => betaC ξ * 𝓕 g ξ) = 𝓕 g := by
    funext ξ
    by_cases h : ξ ∈ Set.Icc (-(1/2) : ℝ) (1/2)
    · rw [betaC_eq_one ξ h, one_mul]
    · rw [hbl ξ h, mul_zero]
  rw [hcongr, fourierInv_betaC_eq_K] at hconv
  rw [← hconv]
  exact (hg.fourierInv_fourier_eq hfg hx).symm


private lemma K_cont : Continuous K := KS.continuous

private lemma K_abs_le (C : ℝ) (hCb : ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2)) (hCpos : 0 < C)
    (z y : ℝ) : ‖K (z - y)‖ ≤ C := by
  have h := hCb (z - y)
  have h2 : C / (1 + (z - y)^2) ≤ C := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [hCpos, sq_nonneg (z - y)]
  linarith

private lemma integrable_gK (g : ℝ → ℂ) (hg : Integrable g) (C : ℝ)
    (hCb : ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2)) (hCpos : 0 < C) (z : ℝ) :
    Integrable (fun y : ℝ => ‖g y‖ * ‖K (z - y)‖) := by
  refine Integrable.mono' (g := fun y : ℝ => C * ‖g y‖) (hg.norm.const_mul C) ?_ ?_
  · exact hg.aestronglyMeasurable.norm.mul
      ((K_cont.comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable)
  · filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    have h := K_abs_le C hCb hCpos z y
    nlinarith [norm_nonneg (g y), norm_nonneg (K (z - y)), h, hCpos.le]

theorem local_reproducing_bound_band_limited :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℝ → ℂ), Integrable g → Continuous g →
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → 𝓕 g ξ = 0) →
      ∀ x : ℝ, ‖g x‖ ^ 2 ≤ A * ∫ t : ℝ, ‖g t‖ ^ 2 / (1 + (x - t) ^ 2) := by
  obtain ⟨C, hCpos, hCb⟩ := K_decay
  refine ⟨C^2 * Real.pi + 1, by positivity, ?_⟩
  intro g hg hcont hbl x
  have hrep : ∀ z : ℝ, g z = ∫ y : ℝ, g y * K (z - y) :=
    fun z => reproducing g hg hbl z hcont.continuousAt
  have hLnn : 0 ≤ ∫ y : ℝ, ‖g y‖ := integral_nonneg (fun y => norm_nonneg _)
  have hCnn : 0 ≤ C := hCpos.le
  have hgb : ∀ z : ℝ, ‖g z‖ ≤ C * ∫ y : ℝ, ‖g y‖ := by
    intro z
    have h1 : ‖g z‖ ≤ ∫ y : ℝ, ‖g y‖ * ‖K (z - y)‖ := by
      conv_lhs => rw [hrep z]
      rw [← norm_neg]
      calc ‖-(∫ y : ℝ, g y * K (z - y))‖ = ‖∫ y : ℝ, g y * K (z - y)‖ := norm_neg _
        _ ≤ ∫ y : ℝ, ‖g y * K (z - y)‖ := norm_integral_le_integral_norm _
        _ = ∫ y : ℝ, ‖g y‖ * ‖K (z - y)‖ := by
              apply integral_congr_ae; filter_upwards with y; rw [norm_mul]
    have h2 : ∫ y : ℝ, ‖g y‖ * ‖K (z - y)‖ ≤ C * ∫ y : ℝ, ‖g y‖ := by
      rw [show C * ∫ y : ℝ, ‖g y‖ = ∫ y : ℝ, C * ‖g y‖ by rw [integral_const_mul]]
      exact integral_mono (integrable_gK g hg C hCb hCpos z) (hg.norm.const_mul C) (fun y => by
        have h := K_abs_le C hCb hCpos z y
        nlinarith [norm_nonneg (g y), norm_nonneg (K (z - y)), h])
    linarith [h1, h2]
  have hgL2 : MemLp g 2 (volume : Measure ℝ) := by
    rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
    refine Integrable.mono' (g := fun z : ℝ => (C * ∫ y : ℝ, ‖g y‖) * ‖g z‖)
      (hg.norm.const_mul (C * ∫ y : ℝ, ‖g y‖)) (hg.aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg (by positivity)]
    have hz := hgb z
    nlinarith [hz, hLnn, hCnn, norm_nonneg (g z)]
  have hg2int : Integrable (fun y : ℝ => ‖g y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hgL2
  set w : ℝ → ℝ := fun y => (1 + (x - y) ^ 2)⁻¹ with hw
  have hw_nn : ∀ y, 0 ≤ w y := fun y => by rw [hw]; exact inv_nonneg.mpr (by nlinarith [sq_nonneg (x - y)])
  have hw_cont : Continuous w := by
    rw [hw]
    refine Continuous.inv₀ (continuous_const.add ((continuous_const.sub continuous_id).pow 2)) ?_
    intro y
    exact ne_of_gt (show (0:ℝ) < 1 + (x - y)^2 from by nlinarith [sq_nonneg (x - y)])
  have hw_int_able : Integrable w := by
    have h := integrable_inv_one_add_sq.comp_sub_left x
    simpa only [hw] using h
  have hw_le_one : ∀ y, w y ≤ 1 := by
    intro y
    rw [hw]; rw [inv_le_one₀ (by positivity)]; nlinarith [sq_nonneg (x - y)]
  have hKbound : ‖g x‖ ≤ C * ∫ y : ℝ, ‖g y‖ * w y := by
    have h1 : ‖g x‖ ≤ ∫ y : ℝ, ‖g y‖ * ‖K (x - y)‖ := by
      conv_lhs => rw [hrep x]
      rw [← norm_neg]
      calc ‖-(∫ y : ℝ, g y * K (x - y))‖ = ‖∫ y : ℝ, g y * K (x - y)‖ := norm_neg _
        _ ≤ ∫ y : ℝ, ‖g y * K (x - y)‖ := norm_integral_le_integral_norm _
        _ = ∫ y : ℝ, ‖g y‖ * ‖K (x - y)‖ := by
              apply integral_congr_ae; filter_upwards with y; rw [norm_mul]
    have h2 : ∫ y : ℝ, ‖g y‖ * ‖K (x - y)‖ ≤ C * ∫ y : ℝ, ‖g y‖ * w y := by
      rw [show C * ∫ y : ℝ, ‖g y‖ * w y = ∫ y : ℝ, C * (‖g y‖ * w y) by rw [integral_const_mul]]
      refine integral_mono (integrable_gK g hg C hCb hCpos x) ?_ ?_
      · refine Integrable.mono' (g := fun y : ℝ => C * ‖g y‖) (hg.norm.const_mul C) ?_ ?_
        · exact ((hg.aestronglyMeasurable.norm.mul hw_cont.aestronglyMeasurable).const_mul C)
        · filter_upwards with y
          rw [Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right (norm_nonneg (g y)) (hw_le_one y)) hCnn
      · intro y
        show ‖g y‖ * ‖K (x - y)‖ ≤ C * (‖g y‖ * w y)
        have hKy := hCb (x - y)
        have hCw : C * w y = C / (1 + (x - y)^2) := by rw [hw, div_eq_mul_inv]
        calc ‖g y‖ * ‖K (x - y)‖ ≤ ‖g y‖ * (C / (1 + (x - y)^2)) :=
              mul_le_mul_of_nonneg_left hKy (norm_nonneg (g y))
          _ = C * (‖g y‖ * w y) := by rw [← hCw]; ring
    linarith [h1, h2]
  set f1 : ℝ → ℝ := fun y => Real.sqrt (w y) with hf1
  set f2 : ℝ → ℝ := fun y => ‖g y‖ * Real.sqrt (w y) with hf2
  have hw_int : ∫ y : ℝ, w y = Real.pi := by
    have h := integral_sub_left_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) (volume : Measure ℝ) x
    simp only [hw]
    rw [h, integral_univ_inv_one_add_sq]
  have hf1c : Continuous f1 := Real.continuous_sqrt.comp hw_cont
  have hf1mem : MemLp f1 2 (volume : Measure ℝ) := by
    rw [hf1, memLp_two_iff_integrable_sq hf1c.aestronglyMeasurable]
    rw [show (fun y : ℝ => Real.sqrt (w y) ^ 2) = w from
      funext (fun y => by rw [Real.sq_sqrt (hw_nn y)])]
    exact hw_int_able
  have hf2c : Continuous (fun y : ℝ => Real.sqrt (w y)) := Real.continuous_sqrt.comp hw_cont
  have hf2mem : MemLp f2 2 (volume : Measure ℝ) := by
    have hmeas : AEStronglyMeasurable (fun y : ℝ => ‖g y‖ * Real.sqrt (w y)) volume :=
      hg.aestronglyMeasurable.norm.mul hf2c.aestronglyMeasurable
    rw [hf2, memLp_two_iff_integrable_sq hmeas]
    rw [show (fun y : ℝ => (‖g y‖ * Real.sqrt (w y)) ^ 2) = (fun y : ℝ => ‖g y‖^2 * w y) from
      funext (fun y => by rw [mul_pow, Real.sq_sqrt (hw_nn y)])]
    refine Integrable.mono' (g := fun y : ℝ => ‖g y‖^2) hg2int ?_ ?_
    · exact (hg.aestronglyMeasurable.norm.pow 2).mul hw_cont.aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [hw_nn y, hw_le_one y, sq_nonneg (‖g y‖)]
  have hCS := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure ℝ)) (p := 2) (q := 2) (f := f1) (g := f2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall (fun y => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
    (by simpa using hf1mem) (by simpa using hf2mem)
  have hA : (∫ y : ℝ, f1 y * f2 y) = ∫ y : ℝ, ‖g y‖ * w y := by
    apply integral_congr_ae; filter_upwards with y
    simp only [hf1, hf2]
    rw [show Real.sqrt (w y) * (‖g y‖ * Real.sqrt (w y)) = ‖g y‖ * (Real.sqrt (w y))^2 from by ring,
      Real.sq_sqrt (hw_nn y)]
  have hB : (∫ y : ℝ, f1 y ^ 2) = Real.pi := by
    rw [show (fun y : ℝ => f1 y ^ 2) = w from funext (fun y => by simp only [hf1, Real.sq_sqrt (hw_nn y)])]
    exact hw_int
  have hD : (∫ y : ℝ, f2 y ^ 2) = ∫ y : ℝ, ‖g y‖^2 * w y := by
    apply integral_congr_ae; filter_upwards with y
    simp only [hf2]; rw [mul_pow, Real.sq_sqrt (hw_nn y)]
  have hDnn : 0 ≤ ∫ y : ℝ, ‖g y‖^2 * w y := integral_nonneg (fun y => mul_nonneg (sq_nonneg _) (hw_nn y))
  have hsq : (∫ y : ℝ, ‖g y‖ * w y) ^ 2 ≤ Real.pi * ∫ y : ℝ, ‖g y‖^2 * w y := by
    have hCS_sqrt : ∫ y : ℝ, f1 y * f2 y ≤ Real.sqrt (∫ y : ℝ, f1 y ^ 2) * Real.sqrt (∫ y : ℝ, f2 y ^ 2) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      simpa only [Real.rpow_ofNat] using hCS
    have hCS2 : ∫ y : ℝ, ‖g y‖ * w y ≤ Real.sqrt Real.pi * Real.sqrt (∫ y : ℝ, ‖g y‖^2 * w y) := by
      rw [← hA, ← hB, ← hD]; exact hCS_sqrt
    calc (∫ y : ℝ, ‖g y‖ * w y) ^ 2
        ≤ (Real.sqrt Real.pi * Real.sqrt (∫ y : ℝ, ‖g y‖^2 * w y)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hCS2 2
      _ = Real.pi * ∫ y : ℝ, ‖g y‖^2 * w y := by
          rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hDnn]
  have hmain : ∫ t : ℝ, ‖g t‖^2 / (1 + (x - t)^2) = ∫ y : ℝ, ‖g y‖^2 * w y := by
    apply integral_congr_ae; filter_upwards with t
    simp only [hw]; rw [div_eq_mul_inv]
  have hA0nn : 0 ≤ ∫ y : ℝ, ‖g y‖ * w y := integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hw_nn y))
  have h1 : ‖g x‖^2 ≤ C^2 * (∫ y : ℝ, ‖g y‖ * w y)^2 := by
    have hk := hKbound
    have hsq := mul_self_le_mul_self (norm_nonneg (g x)) hk
    calc ‖g x‖^2 = ‖g x‖ * ‖g x‖ := by ring
      _ ≤ (C * ∫ y : ℝ, ‖g y‖ * w y) * (C * ∫ y : ℝ, ‖g y‖ * w y) := hsq
      _ = C^2 * (∫ y : ℝ, ‖g y‖ * w y)^2 := by ring
  have h2 : C^2 * (∫ y : ℝ, ‖g y‖ * w y)^2 ≤ C^2 * (Real.pi * ∫ y : ℝ, ‖g y‖^2 * w y) :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
  have hfin : ‖g x‖^2 ≤ (C^2 * Real.pi + 1) * ∫ y : ℝ, ‖g y‖^2 * w y := by
    have h2' : C^2 * (∫ y : ℝ, ‖g y‖ * w y)^2 ≤ C^2 * Real.pi * (∫ y : ℝ, ‖g y‖^2 * w y) := by
      rw [mul_assoc]; exact h2
    have hstep : C^2 * Real.pi * (∫ y : ℝ, ‖g y‖^2 * w y)
        ≤ (C^2 * Real.pi + 1) * (∫ y : ℝ, ‖g y‖^2 * w y) := by nlinarith [hDnn]
    linarith [h1, h2', hstep]
  rw [hmain]; exact hfin


open scoped ENNReal

private lemma inv_one_add_sq_le (n:ℕ) : (1+(n:ℝ)^2)⁻¹ ≤ 2 * (((n:ℝ)+1)^2)⁻¹ := by
  rw [inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < 1 + (n:ℝ)^2)]
  rw [show 2 * (((n:ℝ) + 1)^2)⁻¹ = 2 / ((n:ℝ) + 1)^2 by rw [div_eq_mul_inv]]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < ((n:ℝ)+1)^2)]
  nlinarith [sq_nonneg ((n:ℝ) - 1)]

private lemma summable_nat_inv_one_add_sq : Summable (fun n : ℕ => (1 + (n:ℝ)^2)⁻¹) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.mul_left 2)
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1), one_div, Real.rpow_ofNat]
  exact inv_one_add_sq_le n

private lemma summable_int_inv_one_add_sq : Summable (fun m : ℤ => (1 + (m:ℝ)^2)⁻¹) := by
  apply Summable.of_nat_of_neg
  · simpa using summable_nat_inv_one_add_sq
  · simpa using summable_nat_inv_one_add_sq

private noncomputable def phiW : ℤ → ℝ := fun m => (1 + (max (|(m:ℝ)| - 1) 0)^2)⁻¹

private lemma phiW_nn : ∀ m, 0 ≤ phiW m := fun m => by rw [phiW]; positivity

private lemma phiW_dom : ∀ m, phiW m ≤ 4 * (1 + (m:ℝ)^2)⁻¹ := by
  intro m
  rw [phiW]
  set A : ℝ := max (|(m:ℝ)| - 1) 0 with hA
  have hkey : 1 + (m:ℝ)^2 ≤ 4 * (1 + A^2) := by
    rcases lt_or_ge (1:ℝ) (|(m:ℝ)|) with h | h
    · rw [hA, max_eq_left (by linarith)]
      nlinarith [sq_nonneg (m:ℝ), sq_abs (m:ℝ), abs_nonneg (m:ℝ), h]
    · rw [hA, max_eq_right (by linarith)]
      nlinarith [sq_nonneg (|(m:ℝ)| - 1), abs_nonneg (m:ℝ), sq_abs (m:ℝ), h,
        sq_nonneg (|(m:ℝ)| - 4/3)]
  rw [show 4 * (1 + (m:ℝ)^2)⁻¹ = ((1 + (m:ℝ)^2) / 4)⁻¹ by rw [inv_div, div_eq_mul_inv]]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [hkey]

private lemma phiW_summable : Summable phiW :=
  Summable.of_nonneg_of_le phiW_nn phiW_dom (summable_int_inv_one_add_sq.mul_left 4)

private lemma phiW_pt (t : ℝ) : ∀ m : ℤ, (1 + ((m:ℝ) - t)^2)⁻¹ ≤ phiW (m - ⌊t⌋) := by
  intro m
  set s := t - ⌊t⌋ with hs
  have hs0 : 0 ≤ s := Int.fract_nonneg t
  have hs1 : s < 1 := Int.fract_lt_one t
  have hcast : (m:ℝ) - t = ((m - ⌊t⌋ : ℤ) : ℝ) - s := by rw [hs]; push_cast; ring
  set j : ℝ := ((m - ⌊t⌋ : ℤ) : ℝ) with hj
  have hA : max (|j| - 1) 0 ≤ |j - s| := by
    rcases lt_or_ge (1:ℝ) (|j|) with hgt | hle
    · rw [max_eq_left (by linarith)]
      rcases lt_or_ge j 0 with hjj | hjj
      · rw [abs_of_nonpos hjj.le, abs_of_nonpos (by linarith)]; rw [neg_sub]; linarith
      · rw [abs_of_nonneg hjj]
        have hj1 : 1 < j := by have := hgt; rwa [abs_of_nonneg hjj] at this
        rw [abs_of_nonneg (by linarith)]
        linarith
    · rw [max_eq_right (by linarith)]; positivity
  have hA2 : (max (|j| - 1) 0)^2 ≤ (j - s)^2 := by
    have h0 := le_max_right (|j| - 1) 0
    nlinarith [hA, abs_nonneg (j - s), sq_abs (j - s), h0]
  rw [phiW, hcast]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [hA2]

private lemma count_weight_le : ∃ B0 : ℝ, 0 < B0 ∧
    ∀ t : ℝ, ∑' m : ℤ, (1 + ((m : ℝ) - t) ^ 2)⁻¹ ≤ B0 := by
  refine ⟨∑' m : ℤ, phiW m, ?_, ?_⟩
  · have hφ0 : 0 < phiW 0 := by rw [phiW]; norm_num
    exact lt_of_lt_of_le hφ0 (phiW_summable.le_tsum 0 (fun j hj => phiW_nn j))
  · intro t
    have hg : Summable (fun m : ℤ => phiW (m - ⌊t⌋)) :=
      phiW_summable.comp_injective (fun a b h => by omega)
    have hf : Summable (fun m : ℤ => (1 + ((m:ℝ) - t)^2)⁻¹) :=
      Summable.of_nonneg_of_le (fun m => by positivity) (fun m => phiW_pt t m) hg
    calc ∑' m : ℤ, (1 + ((m:ℝ) - t)^2)⁻¹ ≤ ∑' m : ℤ, phiW (m - ⌊t⌋) :=
          Summable.tsum_le_tsum (fun m => phiW_pt t m) hf hg
      _ = ∑' j : ℤ, phiW j := Equiv.tsum_eq (Equiv.addRight (-⌊t⌋)) phiW

theorem lattice_sup_le_integral_sup_band_limited_continuous :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ → ℝ → ℂ),
      (∀ j : ℕ, MeasureTheory.Integrable (h j)) →
      (∀ j : ℕ, Continuous (h j)) →
      (∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
        FourierTransform.fourier (h j) ξ = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ENNReal.ofReal ‖h j (m : ℝ)‖) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
          ∫⁻ x : ℝ, (⨆ j : ℕ, ENNReal.ofReal ‖h j x‖) ^ (2 : ℝ)
            ∂MeasureTheory.volume := by
  obtain ⟨A, hApos, hL⟩ := local_reproducing_bound_band_limited
  obtain ⟨B0, hB0pos, hB0⟩ := count_weight_le
  refine ⟨A * B0, by positivity, ?_⟩
  intro h hint hcont hbl
  set F : ℝ → ℝ≥0∞ := fun x => (⨆ j : ℕ, ENNReal.ofReal ‖h j x‖) ^ (2 : ℕ) with hF
  have hFmeas : Measurable F := by
    rw [hF]
    exact (Measurable.iSup (fun j =>
      ENNReal.measurable_ofReal.comp ((hcont j).norm.measurable))).pow_const 2
  have hLHS : ∫⁻ m : ℤ, (⨆ j : ℕ, ENNReal.ofReal ‖h j (m:ℝ)‖) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count = ∫⁻ m : ℤ, F (m:ℝ) ∂MeasureTheory.Measure.count := by
    apply lintegral_congr; intro m
    show (⨆ j : ℕ, ENNReal.ofReal ‖h j (m:ℝ)‖) ^ (2:ℝ) = F (m:ℝ)
    rw [hF, ENNReal.rpow_ofNat]
  have hRHS : ∫⁻ x : ℝ, (⨆ j : ℕ, ENNReal.ofReal ‖h j x‖) ^ (2:ℝ)
        ∂MeasureTheory.volume = ∫⁻ x : ℝ, F x ∂MeasureTheory.volume := by
    apply lintegral_congr; intro x
    show (⨆ j : ℕ, ENNReal.ofReal ‖h j x‖) ^ (2:ℝ) = F x
    rw [hF, ENNReal.rpow_ofNat]
  rw [hLHS, hRHS]
  have hstep1 : ∀ m : ℤ, F (m:ℝ) ≤ ENNReal.ofReal A *
      ∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ) - t)^2)⁻¹) ∂MeasureTheory.volume := by
    intro m
    have hFm : F (m:ℝ) = ⨆ j : ℕ, ENNReal.ofReal (‖h j (m:ℝ)‖^2) := by
      show (⨆ j : ℕ, ENNReal.ofReal ‖h j (m:ℝ)‖)^2 = ⨆ j : ℕ, ENNReal.ofReal (‖h j (m:ℝ)‖^2)
      rw [ENNReal.iSup_pow]
      apply iSup_congr; intro j
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [hFm]
    apply iSup_le; intro j
    have hLm := hL (h j) (hint j) (hcont j) (hbl j) (m:ℝ)
    have hφnn : 0 ≤ᵐ[(volume:Measure ℝ)] (fun t : ℝ => ‖h j t‖^2 / (1 + ((m:ℝ)-t)^2)) :=
      Filter.Eventually.of_forall (fun t => by positivity)
    have hφmeas : AEStronglyMeasurable (fun t : ℝ => ‖h j t‖^2 / (1 + ((m:ℝ)-t)^2))
        (volume:Measure ℝ) := by
      have h2 : Measurable (fun t : ℝ => (1 + ((m:ℝ)-t)^2 : ℝ)) := by fun_prop
      exact (((hint j).aemeasurable.norm.pow_const 2).div h2.aemeasurable).aestronglyMeasurable
    calc ENNReal.ofReal (‖h j (m:ℝ)‖^2)
        ≤ ENNReal.ofReal (A * ∫ t : ℝ, ‖h j t‖^2 / (1 + ((m:ℝ)-t)^2)) :=
            ENNReal.ofReal_le_ofReal hLm
      _ = ENNReal.ofReal A * ENNReal.ofReal (∫ t : ℝ, ‖h j t‖^2 / (1 + ((m:ℝ)-t)^2)) := by
            rw [ENNReal.ofReal_mul hApos.le]
      _ ≤ ENNReal.ofReal A *
            ∫⁻ t : ℝ, ENNReal.ofReal (‖h j t‖^2 / (1 + ((m:ℝ)-t)^2)) ∂MeasureTheory.volume := by
            apply mul_le_mul_right
            rw [integral_eq_lintegral_of_nonneg_ae hφnn hφmeas]
            exact ENNReal.ofReal_toReal_le
      _ = ENNReal.ofReal A *
            ∫⁻ t : ℝ, ENNReal.ofReal (‖h j t‖^2) * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹)
              ∂MeasureTheory.volume := by
            congr 1; apply lintegral_congr; intro t
            rw [show ‖h j t‖^2 / (1 + ((m:ℝ)-t)^2) = ‖h j t‖^2 * (1 + ((m:ℝ)-t)^2)⁻¹
                  by rw [div_eq_mul_inv],
              ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal A *
            ∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.volume := by
            apply mul_le_mul_right
            apply lintegral_mono; intro t
            have hle : ENNReal.ofReal (‖h j t‖^2) ≤ F t := by
              show ENNReal.ofReal (‖h j t‖^2) ≤ (⨆ j : ℕ, ENNReal.ofReal ‖h j t‖)^2
              rw [ENNReal.iSup_pow,
                show ENNReal.ofReal (‖h j t‖^2) = (ENNReal.ofReal ‖h j t‖)^2 by
                  rw [ENNReal.ofReal_pow (norm_nonneg _)]]
              exact le_iSup (fun j => (ENNReal.ofReal ‖h j t‖)^2) j
            exact mul_le_mul_left hle _
  have hwmeas : Measurable (fun p : ℤ × ℝ => F p.2 * ENNReal.ofReal ((1 + ((p.1:ℝ) - p.2)^2)⁻¹)) := by
    refine (hFmeas.comp measurable_snd).mul ?_
    refine ENNReal.measurable_ofReal.comp ?_
    have h2 : Measurable (fun p : ℤ × ℝ => (1 + ((p.1:ℝ) - p.2)^2 : ℝ)) := by fun_prop
    exact measurable_inv.comp h2
  calc ∫⁻ m : ℤ, F (m:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m : ℤ, ENNReal.ofReal A *
          (∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.volume)
            ∂MeasureTheory.Measure.count := lintegral_mono (fun m => hstep1 m)
    _ = ENNReal.ofReal A *
          ∫⁻ m : ℤ, (∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹)
            ∂MeasureTheory.volume) ∂MeasureTheory.Measure.count := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal A *
          ∫⁻ t : ℝ, (∫⁻ m : ℤ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹)
            ∂MeasureTheory.Measure.count) ∂MeasureTheory.volume := by
          congr 1
          rw [lintegral_lintegral_swap]
          exact hwmeas.aemeasurable
    _ = ENNReal.ofReal A *
          ∫⁻ t : ℝ, F t * (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹)
            ∂MeasureTheory.Measure.count) ∂MeasureTheory.volume := by
          congr 1; apply lintegral_congr; intro t
          have hRmeas : Measurable (fun m : ℤ => ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹)) := by
            refine ENNReal.measurable_ofReal.comp ?_
            have h2 : Measurable (fun m : ℤ => (1 + ((m:ℝ)-t)^2 : ℝ)) := by fun_prop
            exact measurable_inv.comp h2
          rw [lintegral_const_mul (F t) hRmeas]
    _ ≤ ENNReal.ofReal A *
          ∫⁻ t : ℝ, F t * ENNReal.ofReal B0 ∂MeasureTheory.volume := by
          apply mul_le_mul_right
          apply lintegral_mono; intro t
          simp only []
          apply mul_le_mul_right
          have hsum : Summable (fun m : ℤ => (1 + ((m:ℝ)-t)^2)⁻¹) :=
            Summable.of_nonneg_of_le (fun m => by positivity) (fun m => phiW_pt t m)
              (phiW_summable.comp_injective (fun a b hh => by omega))
          rw [lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
          exact ENNReal.ofReal_le_ofReal (hB0 t)
    _ = ENNReal.ofReal A * ((∫⁻ t : ℝ, F t ∂MeasureTheory.volume) * ENNReal.ofReal B0) := by
          rw [lintegral_mul_const' (ENNReal.ofReal B0) F ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (A * B0) * ∫⁻ t : ℝ, F t ∂MeasureTheory.volume := by
          rw [mul_comm (∫⁻ t : ℝ, F t ∂MeasureTheory.volume) (ENNReal.ofReal B0),
            ← mul_assoc, ← ENNReal.ofReal_mul hApos.le]

end
end Commons.Analysis.Fourier