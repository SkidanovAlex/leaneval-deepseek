import Mathlib
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
import Submission.Commons.Analysis.Fourier.plancherel_trig_polynomial
import Submission.Commons.Analysis.Fourier.bandOp_l2_multiplier_bound
set_option maxHeartbeats 4000000

open MeasureTheory Finset
open scoped FourierTransform ENNReal BigOperators
open VectorFourier

namespace Commons.Analysis.Fourier

noncomputable section

private def zBump : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
private def zBumpC : ℝ → ℂ := fun x => ((zBump x : ℝ) : ℂ)
private lemma zBumpC_contDiff : ContDiff ℝ (⊤ : ℕ∞) zBumpC :=
  Complex.ofRealCLM.contDiff.comp zBump.contDiff
private lemma zBumpC_hcs : HasCompactSupport zBumpC :=
  (zBump.hasCompactSupport (E := ℝ)).comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)
private def zBumpS : SchwartzMap ℝ ℂ := zBumpC_hcs.toSchwartzMap zBumpC_contDiff
private lemma zBumpS_coe : (zBumpS : ℝ → ℂ) = zBumpC :=
  funext (zBumpC_hcs.toSchwartzMap_toFun zBumpC_contDiff)
private lemma zBumpC_eq_one (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1/2) : ℝ) (1/2)) : zBumpC ξ = 1 := by
  have hr : zBump.rIn = (1/2 : ℝ) := rfl
  have hmem : ξ ∈ Metric.closedBall (0 : ℝ) zBump.rIn := by
    rw [Real.closedBall_eq_Icc, hr]; norm_num; exact hξ
  have h1 := zBump.one_of_mem_closedBall hmem
  simp only [zBumpC]; rw [h1, Complex.ofReal_one]
private def zKS : SchwartzMap ℝ ℂ := (𝓕⁻ zBumpS : SchwartzMap ℝ ℂ)
private def zK : ℝ → ℂ := fun x => zKS x
private lemma zK_fourier_eq_one (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1/2) : ℝ) (1/2)) : 𝓕 zK ξ = 1 := by
  have hfourier : (𝓕 zKS : SchwartzMap ℝ ℂ) = zBumpS := FourierInvPair.fourier_fourierInv_eq zBumpS
  have h1 : 𝓕 zK = ⇑zBumpS := by
    change 𝓕 (⇑zKS) = ⇑zBumpS
    rw [← SchwartzMap.fourier_coe zKS, hfourier]
  rw [h1, zBumpS_coe]; exact zBumpC_eq_one ξ hξ
private lemma zK_cont : Continuous zK := zKS.continuous
private lemma zK_integrable : Integrable zK := zKS.integrable
private lemma zK_decay : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖zK x‖ ≤ C / (1 + x ^ 2) := by
  set S0 : ℝ := (SchwartzMap.seminorm ℂ 0 0) zKS with hS0
  set S2 : ℝ := (SchwartzMap.seminorm ℂ 2 0) zKS with hS2
  refine ⟨max (S0 + S2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have h0 : ‖zKS x‖ ≤ S0 := SchwartzMap.norm_le_seminorm ℂ zKS x
  have h2 : ‖x‖ ^ 2 * ‖zKS x‖ ≤ S2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ zKS 2 x
  have hx2 : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hx2] at h2
  have hsum : (1 + x^2) * ‖zKS x‖ ≤ S0 + S2 := by nlinarith [h0, h2]
  have hle : ‖zKS x‖ ≤ max (S0 + S2) 1 / (1 + x^2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsum, le_max_left (S0+S2) 1, le_max_right (S0+S2) 1]
  simpa only [zK, zKS] using hle

private noncomputable def multInt (H : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ : ℝ, H ξ * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))

private lemma hMult_eq_fourierInv (H : ℝ → ℂ) (x : ℝ) :
    multInt H x = 𝓕⁻ H x := by
  rw [multInt]
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  have hph : (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I : ℂ)
      = 2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ) := by
    rw [Real.inner_apply]; push_cast; ring
  rw [hph, smul_eq_mul, mul_comm]

private lemma hMult_continuous (H : ℝ → ℂ) (hH : Integrable H) :
    Continuous (multInt H) := by
  refine continuous_of_dominated (bound := fun ξ : ℝ => ‖H ξ‖) ?_ ?_ hH.norm ?_
  · intro x
    refine AEStronglyMeasurable.mul hH.aestronglyMeasurable ?_
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · intro x
    filter_upwards with ξ
    rw [norm_mul]
    have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))‖ = 1 := by
      rw [show 2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)
        = (↑(2 * Real.pi * ξ * x) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [h1, mul_one]
  · filter_upwards with ξ
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))

private lemma zK_shift_integrable (z : ℝ) : Integrable (fun y : ℝ => zK (z - y)) :=
  zK_integrable.comp_sub_left z

private lemma hMult_reproducing (H : ℝ → ℂ) (hH : Integrable H)
    (hHsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → H ξ = 0) (z : ℝ) :
    multInt H z = ∫ y : ℝ, zK y * multInt H (z - y) := by
  have hconv := Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution hH zK_integrable z
  have hfun : (fun ξ : ℝ => H ξ * 𝓕 zK ξ) = H := by
    funext ξ
    by_cases h : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2)
    · rw [zK_fourier_eq_one ξ h, mul_one]
    · rw [hHsupp ξ h, zero_mul]
  rw [hfun] at hconv
  rw [hMult_eq_fourierInv H z, hconv]
  apply integral_congr_ae
  filter_upwards with y
  rw [hMult_eq_fourierInv H (z-y)]

private lemma zK_shift_memLp (z : ℝ) : MemLp (fun y : ℝ => zK (z - y)) 2 (volume : Measure ℝ) := by
  refine memLp_two_of_lintegral_enorm_lt_top (zK_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
  have h1 : ∫⁻ y : ℝ, ‖zK (z - y)‖ₑ ^ (2:ℝ) = ∫⁻ y : ℝ, ‖zK y‖ₑ ^ (2:ℝ) :=
    lintegral_sub_left_eq_self (fun t : ℝ => ‖zK t‖ₑ ^ (2:ℝ)) z
  rw [h1]
  exact lintegral_enorm_sq_lt_top_of_memLp (zKS.memLp 2 (volume : Measure ℝ))

private lemma integrable_hh_zK (hh : ℝ → ℂ) (hhL2 : MemLp hh 2 (volume : Measure ℝ)) (z : ℝ) :
    Integrable (fun y : ℝ => ‖hh y‖ * ‖zK (z - y)‖) := by
  have h : Integrable (fun y : ℝ => hh y * zK (z - y)) := hhL2.integrable_mul (zK_shift_memLp z)
  refine h.norm.congr (Filter.Eventually.of_forall (fun y => ?_))
  simp only [norm_mul]

private lemma integrable_hh_w (hh : ℝ → ℂ) (hhL2 : MemLp hh 2 (volume : Measure ℝ)) (z : ℝ) :
    Integrable (fun y : ℝ => ‖hh y‖ * (1 + (z - y) ^ 2)⁻¹) := by
  have hwint : Integrable (fun y : ℝ => (1 + (z - y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_sub_left z
  have hsq : Integrable (fun y : ℝ => ‖hh y‖ ^ 2 * (1 + (z - y) ^ 2)⁻¹) := by
    refine Integrable.mono' (g := fun y => ‖hh y‖ ^ 2)
      ((memLp_two_iff_integrable_sq_norm hhL2.aestronglyMeasurable).mp hhL2) ?_ ?_
    · exact (hhL2.aestronglyMeasurable.norm.pow 2).mul hwint.aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : (1 + (z - y) ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]; nlinarith [sq_nonneg (z - y)]
      nlinarith [h1, sq_nonneg ‖hh y‖]
  refine Integrable.mono' (g := fun y => (‖hh y‖^2 * (1 + (z-y)^2)⁻¹ + (1 + (z-y)^2)⁻¹)/2)
    ((hsq.add hwint).div_const 2) ?_ ?_
  · exact (hhL2.aestronglyMeasurable.norm.mul hwint.aestronglyMeasurable)
  · filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    have hw0 : (0:ℝ) ≤ (1 + (z - y)^2)⁻¹ := by positivity
    nlinarith [sq_nonneg (‖hh y‖ - 1), hw0]

private theorem multiplier_pointwise_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (H : ℝ → ℂ), Integrable H →
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) → H ξ = 0) →
      MemLp H 2 (volume : Measure ℝ) →
      ∀ x : ℝ, ‖multInt H x‖ ^ 2
        ≤ A * ∫ t : ℝ, ‖multInt H t‖ ^ 2 / (1 + (x - t) ^ 2) := by
  obtain ⟨C, hCpos, hCb⟩ := zK_decay
  refine ⟨C ^ 2 * Real.pi + 1, by positivity, ?_⟩
  intro H hH hHsupp hHL2 x
  set hh : ℝ → ℂ := multInt H with hhdef
  have hhcont : Continuous hh := by rw [hhdef]; exact hMult_continuous H hH
  have hhL2 : MemLp hh 2 (volume : Measure ℝ) := by
    have h1 : MemLp H 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hH
    have hcong : ∫⁻ z : ℝ, ‖hh z‖ₑ ^ (2:ℝ) = ∫⁻ z : ℝ, ‖𝓕⁻ H z‖ₑ ^ (2:ℝ) := by
      apply lintegral_congr; intro z
      have hzt : hh z = 𝓕⁻ H z := by rw [hhdef]; exact hMult_eq_fourierInv H z
      rw [hzt]
    have hfin : ∫⁻ z : ℝ, ‖hh z‖ₑ ^ (2:ℝ) < ⊤ := by
      rw [hcong, Commons.Analysis.Fourier.BoundaryLayer.lintegral_pwInv h1 hHL2]
      exact lintegral_enorm_sq_lt_top_of_memLp hHL2
    exact memLp_two_of_lintegral_enorm_lt_top hhcont.aestronglyMeasurable hfin
  have hrep : ∀ z : ℝ, hh z = ∫ y : ℝ, hh y * zK (z - y) := by
    intro z
    have h0 : hh z = ∫ y : ℝ, zK y * hh (z - y) := by
      rw [hhdef]; exact hMult_reproducing H hH hHsupp z
    rw [h0, ← integral_sub_left_eq_self (fun t : ℝ => hh t * zK (z - t)) (volume : Measure ℝ) z]
    apply integral_congr_ae
    filter_upwards with y
    simp only [sub_sub_cancel, mul_comm]
  have hKbound : ‖hh x‖ ≤ C * ∫ y : ℝ, ‖hh y‖ * (1 + (x - y) ^ 2)⁻¹ := by
    have h1 : ‖hh x‖ ≤ ∫ y : ℝ, ‖hh y‖ * ‖zK (x - y)‖ := by
      conv_lhs => rw [hrep x]
      calc ‖∫ y : ℝ, hh y * zK (x - y)‖ ≤ ∫ y : ℝ, ‖hh y * zK (x - y)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ y : ℝ, ‖hh y‖ * ‖zK (x - y)‖ := by
            apply integral_congr_ae; filter_upwards with y; rw [norm_mul]
    have h2 : ∫ y : ℝ, ‖hh y‖ * ‖zK (x - y)‖
        ≤ C * ∫ y : ℝ, ‖hh y‖ * (1 + (x - y) ^ 2)⁻¹ := by
      rw [show C * ∫ y : ℝ, ‖hh y‖ * (1 + (x - y) ^ 2)⁻¹
            = ∫ y : ℝ, C * (‖hh y‖ * (1 + (x - y) ^ 2)⁻¹) by rw [integral_const_mul]]
      refine integral_mono (integrable_hh_zK hh hhL2 x) ?_ (fun y => ?_)
      · exact (integrable_hh_w hh hhL2 x).const_mul C
      · have hy := hCb (x - y)
        have hpos : (0:ℝ) < 1 + (x - y)^2 := by positivity
        calc ‖hh y‖ * ‖zK (x - y)‖ ≤ ‖hh y‖ * (C / (1 + (x - y)^2)) :=
              mul_le_mul_of_nonneg_left hy (norm_nonneg _)
          _ = C * (‖hh y‖ * (1 + (x - y)^2)⁻¹) := by rw [div_eq_mul_inv]; ring
    linarith [h1, h2]
  have hg2int : Integrable (fun y : ℝ => ‖hh y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hhL2.aestronglyMeasurable).mp hhL2
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
  have hKb := hKbound
  set f1 : ℝ → ℝ := fun y => Real.sqrt (w y) with hf1
  set f2 : ℝ → ℝ := fun y => ‖hh y‖ * Real.sqrt (w y) with hf2
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
    have hmeas : AEStronglyMeasurable (fun y : ℝ => ‖hh y‖ * Real.sqrt (w y)) volume :=
      hhcont.aestronglyMeasurable.norm.mul hf2c.aestronglyMeasurable
    rw [hf2, memLp_two_iff_integrable_sq hmeas]
    rw [show (fun y : ℝ => (‖hh y‖ * Real.sqrt (w y)) ^ 2) = (fun y : ℝ => ‖hh y‖^2 * w y) from
      funext (fun y => by rw [mul_pow, Real.sq_sqrt (hw_nn y)])]
    refine Integrable.mono' (g := fun y : ℝ => ‖hh y‖^2) hg2int ?_ ?_
    · exact (hhcont.aestronglyMeasurable.norm.pow 2).mul hw_cont.aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [hw_nn y, hw_le_one y, sq_nonneg (‖hh y‖)]
  have hCS := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure ℝ)) (p := 2) (q := 2) (f := f1) (g := f2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall (fun y => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
    (by simpa using hf1mem) (by simpa using hf2mem)
  have hA : (∫ y : ℝ, f1 y * f2 y) = ∫ y : ℝ, ‖hh y‖ * w y := by
    apply integral_congr_ae; filter_upwards with y
    simp only [hf1, hf2]
    rw [show Real.sqrt (w y) * (‖hh y‖ * Real.sqrt (w y)) = ‖hh y‖ * (Real.sqrt (w y))^2 from by ring,
      Real.sq_sqrt (hw_nn y)]
  have hB : (∫ y : ℝ, f1 y ^ 2) = Real.pi := by
    rw [show (fun y : ℝ => f1 y ^ 2) = w from funext (fun y => by simp only [hf1, Real.sq_sqrt (hw_nn y)])]
    exact hw_int
  have hD : (∫ y : ℝ, f2 y ^ 2) = ∫ y : ℝ, ‖hh y‖^2 * w y := by
    apply integral_congr_ae; filter_upwards with y
    simp only [hf2]; rw [mul_pow, Real.sq_sqrt (hw_nn y)]
  have hDnn : 0 ≤ ∫ y : ℝ, ‖hh y‖^2 * w y := integral_nonneg (fun y => mul_nonneg (sq_nonneg _) (hw_nn y))
  have hsq : (∫ y : ℝ, ‖hh y‖ * w y) ^ 2 ≤ Real.pi * ∫ y : ℝ, ‖hh y‖^2 * w y := by
    have hCS_sqrt : ∫ y : ℝ, f1 y * f2 y ≤ Real.sqrt (∫ y : ℝ, f1 y ^ 2) * Real.sqrt (∫ y : ℝ, f2 y ^ 2) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      simpa only [Real.rpow_ofNat] using hCS
    have hCS2 : ∫ y : ℝ, ‖hh y‖ * w y ≤ Real.sqrt Real.pi * Real.sqrt (∫ y : ℝ, ‖hh y‖^2 * w y) := by
      rw [← hA, ← hB, ← hD]; exact hCS_sqrt
    calc (∫ y : ℝ, ‖hh y‖ * w y) ^ 2
        ≤ (Real.sqrt Real.pi * Real.sqrt (∫ y : ℝ, ‖hh y‖^2 * w y)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hCS2 2
      _ = Real.pi * ∫ y : ℝ, ‖hh y‖^2 * w y := by
          rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hDnn]
  have hmain : ∫ t : ℝ, ‖hh t‖^2 / (1 + (x - t)^2) = ∫ y : ℝ, ‖hh y‖^2 * w y := by
    apply integral_congr_ae; filter_upwards with t
    simp only [hw]; rw [div_eq_mul_inv]
  have hA0nn : 0 ≤ ∫ y : ℝ, ‖hh y‖ * w y := integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hw_nn y))
  have h1 : ‖hh x‖^2 ≤ C^2 * (∫ y : ℝ, ‖hh y‖ * w y)^2 := by
    have hkk := hKb
    have hsq2 := mul_self_le_mul_self (norm_nonneg (hh x)) hkk
    calc ‖hh x‖^2 = ‖hh x‖ * ‖hh x‖ := by ring
      _ ≤ (C * ∫ y : ℝ, ‖hh y‖ * w y) * (C * ∫ y : ℝ, ‖hh y‖ * w y) := hsq2
      _ = C^2 * (∫ y : ℝ, ‖hh y‖ * w y)^2 := by ring
  have h2 : C^2 * (∫ y : ℝ, ‖hh y‖ * w y)^2 ≤ C^2 * (Real.pi * ∫ y : ℝ, ‖hh y‖^2 * w y) :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
  have hfin : ‖hh x‖^2 ≤ (C^2 * Real.pi + 1) * ∫ y : ℝ, ‖hh y‖^2 * w y := by
    have h2' : C^2 * (∫ y : ℝ, ‖hh y‖ * w y)^2 ≤ C^2 * Real.pi * (∫ y : ℝ, ‖hh y‖^2 * w y) := by
      rw [mul_assoc]; exact h2
    have hstep : C^2 * Real.pi * (∫ y : ℝ, ‖hh y‖^2 * w y)
        ≤ (C^2 * Real.pi + 1) * (∫ y : ℝ, ‖hh y‖^2 * w y) := by nlinarith [hDnn]
    linarith [h1, h2', hstep]
  rw [hmain]; exact hfin

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

private theorem lattice_sup_le_integral_sup_multiplier_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℕ → ℝ → ℂ),
      (∀ j : ℕ, MemLp (H j) 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      (∀ j : ℕ, MemLp (H j) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      (∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → H j ξ = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) (m:ℝ)‖) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) x‖) ^ (2:ℝ) ∂MeasureTheory.volume := by
  obtain ⟨A, hApos, hL⟩ := multiplier_pointwise_bound
  obtain ⟨B0, hB0pos, hB0⟩ := count_weight_le
  refine ⟨A * B0, by positivity, ?_⟩
  intro H hH1 hH2 hHsupp
  have hcontH : ∀ j, Continuous (multInt (H j)) := fun j => hMult_continuous (H j) (memLp_one_iff_integrable.mp (hH1 j))
  set F : ℝ → ℝ≥0∞ := fun x => (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) x‖) ^ (2 : ℕ) with hF
  have hFmeas : Measurable F := by
    rw [hF]
    exact (Measurable.iSup (fun j => ENNReal.measurable_ofReal.comp ((hcontH j).norm.measurable))).pow_const 2
  have hLHS : ∫⁻ m : ℤ, (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) (m:ℝ)‖) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      = ∫⁻ m : ℤ, F (m:ℝ) ∂MeasureTheory.Measure.count := by
    apply lintegral_congr; intro m
    show (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) (m:ℝ)‖) ^ (2:ℝ) = F (m:ℝ)
    rw [hF, ENNReal.rpow_ofNat]
  have hRHS : ∫⁻ x : ℝ, (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) x‖) ^ (2:ℝ) ∂MeasureTheory.volume
      = ∫⁻ x : ℝ, F x ∂MeasureTheory.volume := by
    apply lintegral_congr; intro x
    show (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) x‖) ^ (2:ℝ) = F x
    rw [hF, ENNReal.rpow_ofNat]
  rw [hLHS, hRHS]
  have hstep1 : ∀ m : ℤ, F (m:ℝ) ≤ ENNReal.ofReal A *
      ∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ) - t)^2)⁻¹) ∂MeasureTheory.volume := by
    intro m
    have hFm : F (m:ℝ) = ⨆ j : ℕ, ENNReal.ofReal (‖multInt (H j) (m:ℝ)‖^2) := by
      show (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) (m:ℝ)‖)^2 = ⨆ j : ℕ, ENNReal.ofReal (‖multInt (H j) (m:ℝ)‖^2)
      rw [ENNReal.iSup_pow]
      apply iSup_congr; intro j
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [hFm]
    apply iSup_le; intro j
    have hLm := hL (H j) (memLp_one_iff_integrable.mp (hH1 j)) (hHsupp j) (hH2 j) (m:ℝ)
    have hφnn : 0 ≤ᵐ[(MeasureTheory.volume:MeasureTheory.Measure ℝ)] (fun t : ℝ => ‖multInt (H j) t‖^2 / (1 + ((m:ℝ)-t)^2)) :=
      Filter.Eventually.of_forall (fun t => by positivity)
    have hφmeas : AEStronglyMeasurable (fun t : ℝ => ‖multInt (H j) t‖^2 / (1 + ((m:ℝ)-t)^2)) (MeasureTheory.volume:MeasureTheory.Measure ℝ) := by
      have h2 : Measurable (fun t : ℝ => (1 + ((m:ℝ)-t)^2 : ℝ)) := by fun_prop
      exact (((hcontH j).measurable.norm.pow_const 2).div h2).aestronglyMeasurable
    calc ENNReal.ofReal (‖multInt (H j) (m:ℝ)‖^2)
        ≤ ENNReal.ofReal (A * ∫ t : ℝ, ‖multInt (H j) t‖^2 / (1 + ((m:ℝ)-t)^2)) := ENNReal.ofReal_le_ofReal hLm
      _ = ENNReal.ofReal A * ENNReal.ofReal (∫ t : ℝ, ‖multInt (H j) t‖^2 / (1 + ((m:ℝ)-t)^2)) := by rw [ENNReal.ofReal_mul hApos.le]
      _ ≤ ENNReal.ofReal A * ∫⁻ t : ℝ, ENNReal.ofReal (‖multInt (H j) t‖^2 / (1 + ((m:ℝ)-t)^2)) ∂MeasureTheory.volume := by
            apply mul_le_mul_right
            rw [integral_eq_lintegral_of_nonneg_ae hφnn hφmeas]
            exact ENNReal.ofReal_toReal_le
      _ = ENNReal.ofReal A * ∫⁻ t : ℝ, ENNReal.ofReal (‖multInt (H j) t‖^2) * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.volume := by
            congr 1; apply lintegral_congr; intro t
            rw [show ‖multInt (H j) t‖^2 / (1 + ((m:ℝ)-t)^2) = ‖multInt (H j) t‖^2 * (1 + ((m:ℝ)-t)^2)⁻¹ by rw [div_eq_mul_inv], ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal A * ∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.volume := by
            apply mul_le_mul_right
            apply lintegral_mono; intro t
            have hle : ENNReal.ofReal (‖multInt (H j) t‖^2) ≤ F t := by
              show ENNReal.ofReal (‖multInt (H j) t‖^2) ≤ (⨆ j : ℕ, ENNReal.ofReal ‖multInt (H j) t‖)^2
              rw [ENNReal.iSup_pow, show ENNReal.ofReal (‖multInt (H j) t‖^2) = (ENNReal.ofReal ‖multInt (H j) t‖)^2 by rw [ENNReal.ofReal_pow (norm_nonneg _)]]
              exact le_iSup (fun j => (ENNReal.ofReal ‖multInt (H j) t‖)^2) j
            exact mul_le_mul_left hle _
  have hwmeas : Measurable (fun p : ℤ × ℝ => F p.2 * ENNReal.ofReal ((1 + ((p.1:ℝ) - p.2)^2)⁻¹)) := by
    refine (hFmeas.comp measurable_snd).mul ?_
    refine ENNReal.measurable_ofReal.comp ?_
    have h2 : Measurable (fun p : ℤ × ℝ => (1 + ((p.1:ℝ) - p.2)^2 : ℝ)) := by fun_prop
    exact measurable_inv.comp h2
  calc ∫⁻ m : ℤ, F (m:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m : ℤ, ENNReal.ofReal A * (∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.volume) ∂MeasureTheory.Measure.count := lintegral_mono (fun m => hstep1 m)
    _ = ENNReal.ofReal A * ∫⁻ m : ℤ, (∫⁻ t : ℝ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.volume) ∂MeasureTheory.Measure.count := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal A * ∫⁻ t : ℝ, (∫⁻ m : ℤ, F t * ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.Measure.count) ∂MeasureTheory.volume := by
          congr 1
          rw [lintegral_lintegral_swap]
          exact hwmeas.aemeasurable
    _ = ENNReal.ofReal A * ∫⁻ t : ℝ, F t * (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹) ∂MeasureTheory.Measure.count) ∂MeasureTheory.volume := by
          congr 1; apply lintegral_congr; intro t
          have hRmeas : Measurable (fun m : ℤ => ENNReal.ofReal ((1 + ((m:ℝ)-t)^2)⁻¹)) := by
            refine ENNReal.measurable_ofReal.comp ?_
            have h2 : Measurable (fun m : ℤ => (1 + ((m:ℝ)-t)^2 : ℝ)) := by fun_prop
            exact measurable_inv.comp h2
          rw [lintegral_const_mul (F t) hRmeas]
    _ ≤ ENNReal.ofReal A * ∫⁻ t : ℝ, F t * ENNReal.ofReal B0 ∂MeasureTheory.volume := by
          apply mul_le_mul_right
          apply lintegral_mono; intro t
          simp only []
          apply mul_le_mul_right
          have hsum : Summable (fun m : ℤ => (1 + ((m:ℝ)-t)^2)⁻¹) :=
            Summable.of_nonneg_of_le (fun m => by positivity) (fun m => phiW_pt t m) (phiW_summable.comp_injective (fun a b hh => by omega))
          rw [lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
          exact ENNReal.ofReal_le_ofReal (hB0 t)
    _ = ENNReal.ofReal A * ((∫⁻ t : ℝ, F t ∂MeasureTheory.volume) * ENNReal.ofReal B0) := by
          rw [lintegral_mul_const' (ENNReal.ofReal B0) F ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (A * B0) * ∫⁻ t : ℝ, F t ∂MeasureTheory.volume := by
          rw [mul_comm (∫⁻ t : ℝ, F t ∂MeasureTheory.volume) (ENNReal.ofReal B0), ← mul_assoc, ← ENNReal.ofReal_mul hApos.le]

private def Lfreq (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) : Set ℝ :=
  {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
private def Mfreq (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) : Set ℝ :=
  {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
private def GLam (f : ℤ → ℂ) (s : Finset ℤ) : ℝ → ℂ :=
  fun ξ => ∑ n ∈ s, f n * Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℂ)) * (ξ : ℂ)))
private def FLam (f : ℤ → ℂ) (s : Finset ℤ) : ℝ → ℂ :=
  fun θ => ∑ n ∈ s, f n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ)) * (θ : ℂ))

private lemma measurableSet_Lfreq (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) : MeasurableSet (Lfreq N lam j) := by
  have hset : Lfreq N lam j = ⋃ k : Fin N, ⋃ l : ℤ,
      {θ : ℝ | |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)} := by
    ext θ; simp only [Lfreq, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  refine MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun l => ?_))
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

private lemma measurableSet_Mfreq (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) : MeasurableSet (Mfreq N lam j) := by
  have hset : Mfreq N lam j = ⋃ k : Fin N, ⋃ l : ℤ,
      {ξ : ℝ | |ξ + (l:ℝ) + lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)} := by
    ext ξ; simp only [Mfreq, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  refine MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun l => ?_))
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

private lemma Mfreq_neg (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (ξ : ℝ) :
    (-ξ) ∈ Mfreq N lam j ↔ ξ ∈ Lfreq N lam j := by
  constructor
  · rintro ⟨k, l, hl⟩
    refine ⟨k, -l, ?_⟩
    have h : -ξ + (l:ℝ) + lam k = -(ξ + ((-l:ℤ):ℝ) - lam k) := by push_cast; ring
    rw [h, abs_neg] at hl; exact hl
  · rintro ⟨k, l, hl⟩
    refine ⟨k, -l, ?_⟩
    have h : -ξ + ((-l:ℤ):ℝ) + lam k = -(ξ + (l:ℝ) - lam k) := by push_cast; ring
    rw [h, abs_neg]; exact hl

private lemma GLam_neg (f : ℤ → ℂ) (s : Finset ℤ) (ξ : ℝ) :
    GLam f s (-ξ) = FLam f s ξ := by
  simp only [GLam, FLam]
  apply Finset.sum_congr rfl; intro n hn
  congr 1
  push_cast
  ring

private lemma GLam_cont (f : ℤ → ℂ) (s : Finset ℤ) : Continuous (GLam f s) := by
  apply continuous_finsetSum; intro n hn
  exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))

private lemma FLam_cont (f : ℤ → ℂ) (s : Finset ℤ) : Continuous (FLam f s) := by
  apply continuous_finsetSum; intro n hn
  exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))

private lemma GLam_bound (f : ℤ → ℂ) (s : Finset ℤ) (ξ : ℝ) :
    ‖GLam f s ξ‖ ≤ ∑ n ∈ s, ‖f n‖ := by
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro n hn
  rw [norm_mul]
  have h1 : ‖Complex.exp (-(2 * Real.pi * Complex.I * (n:ℂ) * (ξ:ℂ)))‖ = 1 := by
    have hph : -(2 * Real.pi * Complex.I * (n:ℂ) * (ξ:ℂ)) = (↑(-(2 * Real.pi * (n:ℝ) * ξ)) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hph, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

private def Hm (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) : ℝ → ℂ :=
  fun ξ => Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ => (1:ℂ)) ξ
    * (Set.indicator (Mfreq N lam j) (fun _ => (1:ℂ)) ξ * GLam f s ξ)

private lemma Hm_memLp (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (p : ℝ≥0∞) :
    MemLp (Hm N lam f s j) p (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  classical
  refine HasCompactSupport.memLp_of_bound ?_ ?_ (∑ n ∈ s, ‖f n‖) (Filter.Eventually.of_forall (fun ξ => ?_))
  · refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(1/2)) (b := (1/2))) (fun ξ hξ => ?_)
    simp only [Function.mem_support, ne_eq] at hξ
    by_contra hcon
    exact hξ (by rw [Hm, Set.indicator_of_notMem hcon, zero_mul])
  · exact (((measurable_const.indicator measurableSet_Icc).mul
      ((measurable_const.indicator (measurableSet_Mfreq N lam j)).mul (GLam_cont f s).measurable))).aestronglyMeasurable
  · rw [Hm, norm_mul, norm_mul]
    have h1 : ‖Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ => (1:ℂ)) ξ‖ ≤ 1 := by
      by_cases h : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2)
      · rw [Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h]; simp
    have h2 : ‖Set.indicator (Mfreq N lam j) (fun _ => (1:ℂ)) ξ‖ ≤ 1 := by
      by_cases h : ξ ∈ Mfreq N lam j
      · rw [Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h]; simp
    calc ‖Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ => (1:ℂ)) ξ‖
          * (‖Set.indicator (Mfreq N lam j) (fun _ => (1:ℂ)) ξ‖ * ‖GLam f s ξ‖)
        ≤ 1 * (1 * (∑ n ∈ s, ‖f n‖)) := by
          refine mul_le_mul h1 (mul_le_mul h2 (GLam_bound f s ξ) (norm_nonneg _) (by norm_num))
            (by positivity) (by norm_num)
      _ = ∑ n ∈ s, ‖f n‖ := by ring

private lemma exp_int_cexp (n : ℤ) : Complex.exp ((n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I n
  rwa [show (n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) = (n:ℂ) * (2 * ↑Real.pi * Complex.I) by ring] at h

private lemma Lfreq_periodic (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (x : ℝ) :
    (x + 1) ∈ Lfreq N lam j ↔ x ∈ Lfreq N lam j := by
  constructor
  · rintro ⟨k, l, hl⟩
    refine ⟨k, l + 1, ?_⟩
    have he : x + ((l + 1 : ℤ) : ℝ) - lam k = x + 1 + (l:ℝ) - lam k := by push_cast; ring
    rw [he]; exact hl
  · rintro ⟨k, l, hl⟩
    refine ⟨k, l - 1, ?_⟩
    have he : x + 1 + ((l - 1 : ℤ) : ℝ) - lam k = x + (l:ℝ) - lam k := by push_cast; ring
    rw [he]; exact hl

private def Tfun (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) : ℝ → ℂ :=
  fun θ => Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ * FLam f s θ
    * Complex.exp (-(2*Real.pi*Complex.I*((m:ℂ))*(θ:ℂ)))
private def MIfun (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) : ℝ → ℂ :=
  fun ξ => Set.indicator (Mfreq N lam j) (fun _ => (1:ℂ)) ξ * GLam f s ξ
    * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*((m:ℂ)))

private lemma exp_neg_int_cexp (n : ℤ) : Complex.exp (-(n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)) = 1 := by
  rw [show -(n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) = ((-n : ℤ):ℂ) * (2 * (Real.pi:ℂ) * Complex.I) by push_cast; ring]
  exact exp_int_cexp (-n)

private lemma FLam_neg (f : ℤ → ℂ) (s : Finset ℤ) (ξ : ℝ) :
    FLam f s (-ξ) = GLam f s ξ := by
  rw [← GLam_neg f s (-ξ), neg_neg]

private lemma FLam_periodic (f : ℤ → ℂ) (s : Finset ℤ) (x : ℝ) :
    FLam f s (x + 1) = FLam f s x := by
  simp only [FLam]
  apply Finset.sum_congr rfl; intro n hn
  congr 1
  rw [show (2 * Real.pi * Complex.I * (n:ℂ) * ((x+1 : ℝ):ℂ))
      = (2 * Real.pi * Complex.I * (n:ℂ) * (x:ℂ)) + ((n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)) by push_cast; ring]
  rw [Complex.exp_add, exp_int_cexp, mul_one]

private lemma Tfun_periodic (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) :
    Function.Periodic (Tfun N lam f s j m) 1 := by
  intro x
  show Tfun N lam f s j m (x + 1) = Tfun N lam f s j m x
  simp only [Tfun]
  rw [show (x + 1 : ℝ) = x + 1 from rfl]
  by_cases hx : x ∈ Lfreq N lam j
  · have hx1 : x + 1 ∈ Lfreq N lam j := (Lfreq_periodic N lam j x).mpr hx
    rw [Set.indicator_of_mem hx1, Set.indicator_of_mem hx, FLam_periodic]
    congr 1
    rw [show -(2 * Real.pi * Complex.I * (m:ℂ) * ((x+1 : ℝ):ℂ))
        = (-(2 * Real.pi * Complex.I * (m:ℂ) * (x:ℂ))) + ((-(m:ℂ)) * (2 * (Real.pi:ℂ) * Complex.I)) by push_cast; ring]
    rw [Complex.exp_add, exp_neg_int_cexp m, mul_one]
  · have hx1 : x + 1 ∉ Lfreq N lam j := fun h => hx ((Lfreq_periodic N lam j x).mp h)
    rw [Set.indicator_of_notMem hx1, Set.indicator_of_notMem hx]
    simp

private lemma MIfun_neg (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) (ξ : ℝ) :
    MIfun N lam f s j m ξ = Tfun N lam f s j m (-ξ) := by
  simp only [MIfun, Tfun]
  have hL : ((-ξ) ∈ Lfreq N lam j) ↔ (ξ ∈ Mfreq N lam j) := by
    have := Mfreq_neg N lam j (-ξ); simpa using this.symm
  by_cases h : ξ ∈ Mfreq N lam j
  · have h' : (-ξ) ∈ Lfreq N lam j := hL.mpr h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h', FLam_neg]
    congr 1
    rw [show -(2 * Real.pi * Complex.I * (m:ℂ) * ((-ξ : ℝ):ℂ)) = 2 * Real.pi * Complex.I * (ξ:ℂ) * (m:ℂ) by push_cast; ring]
  · have h' : (-ξ) ∉ Lfreq N lam j := fun hh => h (hL.mp hh)
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    simp

private lemma TVint_eq (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) (θ : ℝ) :
    (∑ n ∈ s, f n * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
        * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))))
      = Tfun N lam f s j m θ := by
  rw [Tfun]
  have h1 : ∀ n ∈ s, f n * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
        * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))))
      = Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
        * (f n * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) := fun n hn => by ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have h2 : (∑ n ∈ s, f n * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))))
      = Complex.exp (-(2*Real.pi*Complex.I*((m:ℂ))*(θ:ℂ))) * FLam f s θ := by
    rw [FLam, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n hn
    rw [show -(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))
        = (-(2*Real.pi*Complex.I*((m:ℂ))*(θ:ℂ))) + (2*Real.pi*Complex.I*((n:ℂ))*(θ:ℂ)) by push_cast; ring]
    rw [Complex.exp_add]; ring
  rw [h2]; ring

private lemma Hm_mul_exp (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) (ξ : ℝ) :
    Hm N lam f s j ξ * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*((m:ℂ)))
      = Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (MIfun N lam f s j m) ξ := by
  unfold Hm MIfun
  classical
  by_cases h : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring


private lemma intervalIntegrable_ind_bound (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (a b : ℝ) (r : ℤ) (c : ℂ) :
    IntervalIntegrable (fun θ : ℝ => c * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))))) volume a b := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => c * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))))) volume :=
    (measurable_const.mul ((measurable_const.indicator (measurableSet_Lfreq N lam j)).mul
      (Complex.continuous_exp.comp (by fun_prop)).measurable)).aestronglyMeasurable
  have hb : ∀ θ, ‖c * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))))‖ ≤ ‖c‖ := by
    intro θ
    rw [norm_mul]
    have h1 : ‖Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
        * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ)))‖ ≤ 1 := by
      rw [norm_mul]
      have ha : ‖Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ‖ ≤ 1 := by
        by_cases h : θ ∈ Lfreq N lam j
        · rw [Set.indicator_of_mem h]; simp
        · rw [Set.indicator_of_notMem h]; simp
      have hb2 : ‖Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ)))‖ = 1 := by
        have hph : -(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))
            = (↑(-(2*Real.pi*((r:ℝ))*θ)) : ℂ) * Complex.I := by push_cast; ring
        rw [hph, Complex.norm_exp_ofReal_mul_I]
      rw [hb2, mul_one]; exact ha
    calc ‖c‖ * ‖Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
          * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ)))‖ ≤ ‖c‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖c‖ := mul_one _
  refine ⟨MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas.restrict ‖c‖ ?_,
          MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas.restrict ‖c‖ ?_⟩
  · filter_upwards with x using hb x
  · filter_upwards with x using hb x

private lemma lattice_sum_eq (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) :
    (∑ n ∈ s, f n * (∫ θ in Set.Icc (0:ℝ) 1,
        Set.indicator (Lfreq N lam j) (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ))
      = ∫ θ in (0:ℝ)..1, Tfun N lam f s j m θ := by
  classical
  have hstep : ∀ n : ℤ, (∫ θ in Set.Icc (0:ℝ) 1,
        Set.indicator (Lfreq N lam j) (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ)
      = ∫ θ in (0:ℝ)..1, Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
          * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))) := by
    intro n
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply intervalIntegral.integral_congr
    intro θ hθ
    by_cases h : θ ∈ Lfreq N lam j
    · simp only [Set.indicator_of_mem h, one_mul]
    · simp only [Set.indicator_of_notMem h, zero_mul]
  rw [Finset.sum_congr rfl (fun n _ => by rw [hstep n])]
  have hfin : ∀ n ∈ s, IntervalIntegrable (fun θ : ℝ => f n * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))))) volume (0:ℝ) 1 :=
    fun n _ => intervalIntegrable_ind_bound N lam j 0 1 (m-n) (f n)
  rw [Finset.sum_congr rfl (fun n _ => by rw [← intervalIntegral.integral_const_mul])]
  have hgoal : (∑ n ∈ s, ∫ θ in (0:ℝ)..1, f n * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))))
      = ∫ θ in (0:ℝ)..1, ∑ n ∈ s, f n * (Set.indicator (Lfreq N lam j) (fun _ => (1:ℂ)) θ
          * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) :=
    (intervalIntegral.integral_finsetSum hfin).symm
  rw [hgoal]
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact TVint_eq N lam f s j m θ

private lemma multInt_Hm_eq (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) :
    multInt (Hm N lam f s j) (m:ℝ) = ∫ θ in (0:ℝ)..1, Tfun N lam f s j m θ := by
  have hExp : (fun ξ : ℝ => Hm N lam f s j ξ * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(((m:ℝ):ℂ))))
      = fun ξ : ℝ => Hm N lam f s j ξ * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*((m:ℂ))) := by
    funext ξ
    congr 2
  rw [multInt, hExp]
  rw [show (fun ξ : ℝ => Hm N lam f s j ξ * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*((m:ℂ))))
      = fun ξ : ℝ => Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (MIfun N lam f s j m) ξ from by
        funext ξ; exact Hm_mul_exp N lam f s j m ξ]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
  rw [show (∫ ξ in (-(1/2):ℝ)..(1/2), MIfun N lam f s j m ξ)
      = ∫ ξ in (-(1/2):ℝ)..(1/2), MIfun N lam f s j m (-ξ) from by
        simpa using (intervalIntegral.integral_comp_neg (f := MIfun N lam f s j m) (a := -(1/2)) (b := (1/2))).symm]
  rw [show (∫ ξ in (-(1/2):ℝ)..(1/2), MIfun N lam f s j m (-ξ))
      = ∫ ξ in (-(1/2):ℝ)..(1/2), Tfun N lam f s j m ξ from by
        apply intervalIntegral.integral_congr
        intro ξ hξ
        show MIfun N lam f s j m (-ξ) = Tfun N lam f s j m ξ
        rw [MIfun_neg, neg_neg]]
  have hper := Function.Periodic.intervalIntegral_add_eq (Tfun_periodic N lam f s j m) (-(1/2)) 0
  rw [show (-(1/2:ℝ) + 1) = 1/2 by norm_num, show ((0:ℝ) + 1) = 1 by norm_num] at hper
  exact hper

private noncomputable def Df (f : ℤ → ℂ) (s : Finset ℤ) : ℝ := ∑ n ∈ s, ‖f n‖^2
private noncomputable def Sf (f : ℤ → ℂ) (s : Finset ℤ) : ℝ := ∑ n ∈ s, ‖f n‖
private noncomputable def deltaF (f : ℤ → ℂ) (s : Finset ℤ) : ℝ := Df f s / (4 * (Sf f s ^ 2 + 1))

private lemma Df_nonneg (f : ℤ → ℂ) (s : Finset ℤ) : 0 ≤ Df f s :=
  Finset.sum_nonneg (fun n _ => sq_nonneg _)
private lemma Sf_nonneg (f : ℤ → ℂ) (s : Finset ℤ) : 0 ≤ Sf f s :=
  Finset.sum_nonneg (fun n _ => norm_nonneg _)
private lemma deltaF_pos (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) : 0 < deltaF f s :=
  div_pos hD (by positivity)

private noncomputable def cutBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) :=
  ⟨1/2, 1/2 + δ, by norm_num, by linarith⟩

private lemma cutBump_rIn (δ : ℝ) (hδ : 0 < δ) : (cutBump δ hδ).rIn = 1/2 := rfl
private lemma cutBump_rOut (δ : ℝ) (hδ : 0 < δ) : (cutBump δ hδ).rOut = 1/2 + δ := rfl

private lemma cutBump_eq_one (δ : ℝ) (hδ : 0 < δ) {ξ : ℝ}
    (hξ : ξ ∈ Metric.closedBall (0:ℝ) (1/2)) : ((cutBump δ hδ ξ : ℝ) : ℂ) = 1 := by
  have hmem : ξ ∈ Metric.closedBall (0:ℝ) (cutBump δ hδ).rIn := by rw [cutBump_rIn]; exact hξ
  rw [ContDiffBump.one_of_mem_closedBall (cutBump δ hδ) hmem, Complex.ofReal_one]

private lemma cutBump_zero (δ : ℝ) (hδ : 0 < δ) {ξ : ℝ} (hξ : (1/2 + δ) ≤ |ξ|) :
    ((cutBump δ hδ ξ : ℝ) : ℂ) = 0 := by
  rw [ContDiffBump.zero_of_le_dist]
  · simp only [Complex.ofReal_zero]
  · rw [cutBump_rOut, dist_zero_right, Real.norm_eq_abs]; exact hξ

private lemma cutBump_norm_le (δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    ‖((cutBump δ hδ ξ : ℝ) : ℂ)‖ ≤ 1 := by
  have h1 : ‖((cutBump δ hδ ξ : ℝ) : ℂ)‖ = |(cutBump δ hδ ξ : ℝ)| := by simp
  rw [h1, abs_of_nonneg (ContDiffBump.nonneg (cutBump δ hδ))]
  exact ContDiffBump.le_one (cutBump δ hδ)

private noncomputable def PsiF (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) : ℝ → ℂ :=
  fun ξ => ((cutBump δ hδ ξ : ℝ) : ℂ) * GLam f s ξ

private lemma GLam_contDiff (f : ℤ → ℂ) (s : Finset ℤ) : ContDiff ℝ (⊤ : ℕ∞) (GLam f s) := by
  unfold GLam
  refine ContDiff.sum (fun n hn => contDiff_const.mul ?_)
  refine Complex.contDiff_exp.comp ?_
  rw [show (fun x : ℝ => -(2 * Real.pi * Complex.I * (n:ℂ) * (x:ℂ)))
      = fun x : ℝ => (-(2 * Real.pi * Complex.I * (n:ℂ))) * (x:ℂ) from by funext x; ring]
  exact contDiff_const.mul Complex.ofRealCLM.contDiff

private lemma PsiF_contDiff (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (PsiF f s δ hδ) := by
  refine (Complex.ofRealCLM.contDiff.comp (ContDiffBump.contDiff (cutBump δ hδ))).mul (GLam_contDiff f s)

private lemma PsiF_hcs (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport (PsiF f s δ hδ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℝ) (1/2+δ)) (fun ξ hξ => ?_)
  simp only [Function.mem_support, ne_eq] at hξ
  by_contra hcon
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hcon
  have hzero : ((cutBump δ hδ ξ : ℝ) : ℂ) = 0 := cutBump_zero δ hδ (le_of_lt hcon)
  exact hξ (by rw [PsiF, hzero, zero_mul])

private noncomputable def PsiS (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  (PsiF_hcs f s δ hδ).toSchwartzMap (PsiF_contDiff f s δ hδ)

private lemma PsiS_coe (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
    (PsiS f s δ hδ : ℝ → ℂ) = PsiF f s δ hδ :=
  funext ((PsiF_hcs f s δ hδ).toSchwartzMap_toFun (PsiF_contDiff f s δ hδ))

private lemma PsiS_eq_GLam (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) {ξ : ℝ}
    (hξ : |ξ| ≤ 1/2) : PsiS f s δ hδ ξ = GLam f s ξ := by
  rw [show PsiS f s δ hδ ξ = PsiF f s δ hδ ξ from congrFun (PsiS_coe f s δ hδ) ξ]
  rw [PsiF, cutBump_eq_one δ hδ (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hξ), one_mul]

private noncomputable def NP (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  ∫ x : ℝ, ‖(PsiS f s δ hδ : ℝ → ℂ) x‖^2

private lemma NP_eq (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
    NP f s δ hδ = ∫ x : ℝ, ‖PsiF f s δ hδ x‖^2 := by
  rw [NP]; apply integral_congr_ae; filter_upwards with x; rw [PsiS_coe]

private lemma Sf_sq_lt (f : ℤ → ℂ) (s : Finset ℤ) : 0 < Sf f s ^ 2 + 1 := by
  have := Sf_nonneg f s; nlinarith [sq_nonneg (Sf f s)]

private lemma GLam_plancherel (f : ℤ → ℂ) (s : Finset ℤ) :
    (∫ ξ in (-(1/2):ℝ)..(1/2), ‖GLam f s ξ‖^2) = Df f s := by
  have hper2 : Function.Periodic (fun ξ : ℝ => ‖FLam f s ξ‖^2) 1 :=
    fun ξ => by simp only [FLam_periodic f s ξ]
  have h1 : (∫ ξ in (-(1/2):ℝ)..(1/2), ‖GLam f s ξ‖^2)
      = ∫ ξ in (-(1/2):ℝ)..(1/2), ‖FLam f s ξ‖^2 := by
    rw [show (∫ ξ in (-(1/2):ℝ)..(1/2), ‖GLam f s ξ‖^2)
        = ∫ ξ in (-(1/2):ℝ)..(1/2), ‖GLam f s (-ξ)‖^2 from by
          simpa using (intervalIntegral.integral_comp_neg (f := fun ξ : ℝ => ‖GLam f s ξ‖^2)
            (a := -(1/2)) (b := (1/2))).symm]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    simp only [GLam_neg]
  rw [h1]
  have h2 := Function.Periodic.intervalIntegral_add_eq hper2 (-(1/2)) 0
  rw [show (-(1/2:ℝ) + 1) = 1/2 by norm_num, show ((0:ℝ) + 1) = 1 by norm_num] at h2
  rw [h2]
  rw [show (∫ θ in (0:ℝ)..1, ‖FLam f s θ‖^2)
      = ∫ θ in (0:ℝ)..1, ‖∑ n ∈ s, f n * Complex.exp (2*Real.pi*Complex.I*((n:ℂ))*(θ:ℂ))‖^2 from
        intervalIntegral.integral_congr (fun θ _ => by rw [FLam])]
  rw [← plancherel_trig_polynomial s f, Df]

private lemma PsiF_norm_le (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    ‖PsiF f s δ hδ x‖ ≤ Sf f s := by
  rw [PsiF, norm_mul]
  calc ‖((cutBump δ hδ x : ℝ) : ℂ)‖ * ‖GLam f s x‖ ≤ 1 * Sf f s :=
        mul_le_mul (cutBump_norm_le δ hδ x) (GLam_bound f s x) (norm_nonneg _) (by norm_num)
    _ = Sf f s := one_mul _

private lemma PsiF_zero_of_not_mem (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) {x : ℝ}
    (hx : x ∉ Set.Icc (-(1/2)-δ) (1/2+δ)) : PsiF f s δ hδ x = 0 := by
  have hx' : (1/2 + δ) ≤ |x| := by
    simp only [Set.mem_Icc, not_and_or] at hx
    rcases hx with h | h
    · push Not at h; rw [abs_of_neg (by linarith)]; linarith
    · push Not at h; rw [abs_of_pos (by linarith)]; linarith
  rw [PsiF, cutBump_zero δ hδ hx', zero_mul]

private lemma NP_le (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
    NP f s δ hδ ≤ Df f s + 2 * δ * (Sf f s)^2 := by
  rw [NP_eq]
  set A : Set ℝ := Set.Icc (-(1/2):ℝ) (1/2) with hAdef
  set C : Set ℝ := Set.Icc (-(1/2)-δ) (1/2+δ) with hCdef
  have hAmeas : MeasurableSet A := measurableSet_Icc
  have hCmeas : MeasurableSet C := measurableSet_Icc
  have hbound : Integrable (fun x : ℝ => ‖PsiF f s δ hδ x‖^2) (volume : Measure ℝ) := by
    have h2 : MemLp (fun x : ℝ => ‖PsiF f s δ hδ x‖) 2 (volume : Measure ℝ) := by
      rw [← PsiS_coe f s δ hδ]; exact (PsiS f s δ hδ).memLp 2 |>.norm
    have h3 := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
    simpa using h3
  have hsplit := MeasureTheory.integral_add_compl (s := A) hAmeas hbound
  rw [← hsplit]
  have h1 : (∫ x in A, ‖PsiF f s δ hδ x‖^2) = Df f s := by
    have hcong : Set.EqOn (fun x => ‖PsiF f s δ hδ x‖^2) (fun x => ‖GLam f s x‖^2) A := by
      intro x hx
      beta_reduce
      have hx' : |x| ≤ 1/2 := by rw [hAdef, Set.mem_Icc] at hx; rw [abs_le]; exact hx
      have hPsi : PsiF f s δ hδ x = GLam f s x := by
        simp only [PsiF]
        rw [cutBump_eq_one δ hδ (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hx'), one_mul]
      rw [hPsi]
    rw [MeasureTheory.setIntegral_congr_fun hAmeas hcong]
    rw [hAdef, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
    exact GLam_plancherel f s
  have h2 : (∫ x in Aᶜ, ‖PsiF f s δ hδ x‖^2) ≤ 2 * δ * (Sf f s)^2 := by
    have hzero : ∀ x : ℝ, x ∉ C → ‖PsiF f s δ hδ x‖^2 = 0 := by
      intro x hx; rw [PsiF_zero_of_not_mem f s δ hδ hx, norm_zero]; norm_num
    have hsubset : Aᶜ ∩ C ⊆ Set.Ico (-(1/2)-δ) (-(1/2)) ∪ Set.Ioc (1/2) (1/2+δ) := by
      intro x hx
      have hxC : x ∈ C := hx.2
      have hxA : x ∉ A := hx.1
      rw [hCdef, Set.mem_Icc] at hxC
      rw [hAdef] at hxA
      simp only [Set.mem_Icc, not_and_or, not_le] at hxA
      rcases hxA with hxA | hxA
      · exact Or.inl ⟨hxC.1, hxA⟩
      · exact Or.inr ⟨hxA, hxC.2⟩
    have hvol : volume.real (Aᶜ ∩ C) ≤ 2 * δ := by
      have hd : Disjoint (Set.Ico (-(1/2)-δ) (-(1/2))) (Set.Ioc (1/2) (1/2+δ)) := by
        rw [Set.disjoint_left]; intro x hx1 hx2
        simp only [Set.mem_Ico] at hx1; simp only [Set.mem_Ioc] at hx2; linarith [hx1.2, hx2.1]
      have hmeas : volume (Aᶜ ∩ C) ≤ ENNReal.ofReal (2*δ) := by
        refine le_trans (measure_mono hsubset) ?_
        rw [measure_union hd measurableSet_Ioc, Real.volume_Ico, Real.volume_Ioc,
          ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ -(1/2)-(-(1/2)-δ))
            (by linarith : (0:ℝ) ≤ 1/2+δ-1/2)]
        exact le_of_eq (by ring_nf)
      have hreal : volume.real (Aᶜ ∩ C) = (volume (Aᶜ ∩ C)).toReal := rfl
      rw [hreal]
      exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeas)
        (le_of_eq (ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2*δ)))
    have hfin : volume (Aᶜ ∩ C) < ⊤ := by
      refine lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) ?_
      rw [hCdef, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hintC : IntegrableOn (fun x => ‖PsiF f s δ hδ x‖^2) (Aᶜ ∩ C) (volume : Measure ℝ) :=
      hbound.integrableOn.mono_set Set.inter_subset_left
    have hconst : IntegrableOn (fun _ : ℝ => (Sf f s)^2) (Aᶜ ∩ C) (volume : Measure ℝ) :=
      IntegrableOn.of_bound hfin aestronglyMeasurable_const _ (Filter.Eventually.of_forall (fun x => le_rfl))
    have hrec : (∫ x in Aᶜ, ‖PsiF f s δ hδ x‖^2) = ∫ x in Aᶜ ∩ C, ‖PsiF f s δ hδ x‖^2 := by
      have hdisj : Disjoint (Aᶜ ∩ C) (Aᶜ ∩ Cᶜ) := by
        rw [Set.disjoint_left]; intro x hx hx2
        exact absurd hx.2 (by simpa using hx2.2)
      have hunion : Aᶜ ∩ C ∪ Aᶜ ∩ Cᶜ = Aᶜ := by
        ext x; constructor
        · rintro (h | h) <;> exact h.1
        · intro hx; by_cases hx' : x ∈ C
          · exact Or.inl ⟨hx, hx'⟩
          · exact Or.inr ⟨hx, hx'⟩
      rw [show (∫ x in Aᶜ, ‖PsiF f s δ hδ x‖^2)
          = ∫ x in Aᶜ, C.indicator (fun x => ‖PsiF f s δ hδ x‖^2) x from by
        apply MeasureTheory.setIntegral_congr_fun hAmeas.compl
        intro x hx
        beta_reduce
        by_cases hxc : x ∈ C
        · rw [Set.indicator_of_mem hxc]
        · rw [Set.indicator_of_notMem hxc, hzero x hxc]]
      rw [MeasureTheory.setIntegral_indicator hCmeas]
    rw [hrec]
    have h6 := setIntegral_mono_on hintC hconst (hAmeas.compl.inter hCmeas) (fun x hx => by
      have := PsiF_norm_le f s δ hδ x
      nlinarith [norm_nonneg (PsiF f s δ hδ x)])
    rw [setIntegral_const, smul_eq_mul] at h6
    calc (∫ x in Aᶜ ∩ C, ‖PsiF f s δ hδ x‖^2) ≤ (volume.real (Aᶜ ∩ C)) * (Sf f s)^2 := h6
      _ ≤ (2*δ) * (Sf f s)^2 := mul_le_mul_of_nonneg_right hvol (sq_nonneg _)
      _ = 2 * δ * (Sf f s)^2 := by ring
  linarith

private lemma Df_le_NP (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
    Df f s ≤ NP f s δ hδ := by
  rw [NP_eq, ← GLam_plancherel f s]
  have hAmeas : MeasurableSet (Set.Icc (-(1/2):ℝ) (1/2)) := measurableSet_Icc
  have hcong : Set.EqOn (fun x => ‖PsiF f s δ hδ x‖^2) (fun x => ‖GLam f s x‖^2)
      (Set.Icc (-(1/2):ℝ) (1/2)) := by
    intro x hx
    beta_reduce
    have hx' : |x| ≤ 1/2 := by rw [Set.mem_Icc] at hx; rw [abs_le]; exact hx
    have hPsi : PsiF f s δ hδ x = GLam f s x := by
      simp only [PsiF]
      rw [cutBump_eq_one δ hδ (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hx'), one_mul]
    rw [hPsi]
  have hbound : Integrable (fun x : ℝ => ‖PsiF f s δ hδ x‖^2) (volume : Measure ℝ) := by
    have h2 : MemLp (fun x : ℝ => ‖PsiF f s δ hδ x‖) 2 (volume : Measure ℝ) := by
      rw [← PsiS_coe f s δ hδ]; exact (PsiS f s δ hδ).memLp 2 |>.norm
    have h3 := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
    simpa using h3
  have hconv : (∫ ξ in (-(1/2):ℝ)..(1/2), ‖GLam f s ξ‖^2)
      = ∫ x in Set.Icc (-(1/2):ℝ) (1/2), ‖GLam f s x‖^2 := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
  rw [hconv]
  have heq : (∫ x in Set.Icc (-(1/2):ℝ) (1/2), ‖GLam f s x‖^2)
      = ∫ x in Set.Icc (-(1/2):ℝ) (1/2), ‖PsiF f s δ hδ x‖^2 :=
    (MeasureTheory.setIntegral_congr_fun hAmeas hcong).symm
  rw [heq]
  exact setIntegral_le_integral hbound (Filter.Eventually.of_forall (fun x => by positivity))

private lemma deltaF_le (f : ℤ → ℂ) (s : Finset ℤ) :
    2 * deltaF f s * (Sf f s)^2 ≤ Df f s / 2 := by
  have h1 : (0:ℝ) < Sf f s ^ 2 + 1 := by have h := Sf_nonneg f s; nlinarith [sq_nonneg (Sf f s)]
  rw [deltaF]
  rw [show 2 * (Df f s / (4 * (Sf f s ^ 2 + 1))) * (Sf f s)^2
      = Df f s * (Sf f s)^2 / (2 * (Sf f s ^ 2 + 1)) by field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Sf f s), Df_nonneg f s]

private noncomputable def lamg (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) : ℝ :=
  Real.sqrt (Df f s / NP f s (deltaF f s) (deltaF_pos f s hD))

private noncomputable def gSch (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (lamg f s hD • PsiS f s (deltaF f s) (deltaF_pos f s hD))

private lemma NP_pos (f : ℤ → ℂ) (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) (hD : 0 < Df f s) :
    0 < NP f s δ hδ := lt_of_lt_of_le hD (Df_le_NP f s δ hδ)

private lemma lamg_sq (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) :
    (lamg f s hD)^2 = Df f s / NP f s (deltaF f s) (deltaF_pos f s hD) := by
  rw [lamg, Real.sq_sqrt]
  exact div_nonneg hD.le (NP_pos f s (deltaF f s) (deltaF_pos f s hD) hD).le

private lemma lamg_nonneg (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) : 0 ≤ lamg f s hD := by
  rw [lamg]; exact Real.sqrt_nonneg _

private lemma lamg_ge (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) :
    1/2 ≤ lamg f s hD := by
  have hNP := NP_le f s (deltaF f s) (deltaF_pos f s hD)
  have hdel := deltaF_le f s
  have hle : NP f s (deltaF f s) (deltaF_pos f s hD) ≤ 3 * Df f s / 2 := by linarith
  have hcast : Df f s / NP f s (deltaF f s) (deltaF_pos f s hD) ≥ 2/3 := by
    rw [ge_iff_le, le_div_iff₀ (NP_pos f s (deltaF f s) (deltaF_pos f s hD) hD)]
    nlinarith [hle, hD]
  have hpos := NP_pos f s (deltaF f s) (deltaF_pos f s hD) hD
  have hrat : Df f s / NP f s (deltaF f s) (deltaF_pos f s hD) ≥ 2/3 := by
    rw [ge_iff_le, le_div_iff₀ hpos]
    nlinarith [hle, hD]
  calc (1/2 : ℝ) ≤ Real.sqrt (2/3) := by
        have h1 : (1/2:ℝ)^2 ≤ 2/3 := by norm_num
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/3), Real.sqrt_nonneg (2/3:ℝ), h1]
    _ ≤ Real.sqrt (Df f s / NP f s (deltaF f s) (deltaF_pos f s hD)) := Real.sqrt_le_sqrt hrat
    _ = lamg f s hD := rfl

private lemma multInt_Hm_interval (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (x : ℝ) :
    multInt (Hm N lam f s j) x
      = ∫ ξ in (-(1/2):ℝ)..(1/2), Set.indicator (Mfreq N lam j) (fun _ => (1:ℂ)) ξ * GLam f s ξ
          * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ)) := by
  rw [multInt]
  rw [show (fun ξ : ℝ => Hm N lam f s j ξ * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ)))
      = fun ξ : ℝ => Set.indicator (Set.Icc (-(1/2):ℝ) (1/2))
          (fun ξ => Set.indicator (Mfreq N lam j) (fun _ => (1:ℂ)) ξ * GLam f s ξ
            * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ))) ξ from by
        funext ξ; rw [Hm]; classical
        by_cases h : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2)
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring]
  rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]

private lemma gS_fourier (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) (x : ℝ) :
    (𝓕 (⇑(gSch f s hD))) x = lamg f s hD * (PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x := by
  have hY : (𝓕 (𝓕⁻ (lamg f s hD • PsiS f s (deltaF f s) (deltaF_pos f s hD))) : SchwartzMap ℝ ℂ)
      = lamg f s hD • PsiS f s (deltaF f s) (deltaF_pos f s hD) :=
    FourierInvPair.fourier_fourierInv_eq _
  have hcoe : 𝓕 (⇑(gSch f s hD)) = ⇑(lamg f s hD • PsiS f s (deltaF f s) (deltaF_pos f s hD)) := by
    rw [gSch, ← SchwartzMap.fourier_coe _, hY]
  rw [hcoe, SchwartzMap.smul_apply, Complex.real_smul]

private lemma gS_lintegral (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s) :
    ∫⁻ x : ℝ, ‖(gSch f s hD : ℝ → ℂ) x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (Df f s) := by
  have hmem2 : MemLp (fun x : ℝ => lamg f s hD * (PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x) 2 (volume : Measure ℝ) :=
    ((PsiS f s (deltaF f s) (deltaF_pos f s hD)).memLp 2).const_mul _
  have hmem1 : MemLp (fun x : ℝ => lamg f s hD * (PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x) 1 (volume : Measure ℝ) :=
    ((PsiS f s (deltaF f s) (deltaF_pos f s hD)).memLp 1).const_mul _
  have hfun : (fun x : ℝ => lamg f s hD * (PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x)
      = ⇑(lamg f s hD • PsiS f s (deltaF f s) (deltaF_pos f s hD)) := by
    funext y; rw [SchwartzMap.smul_apply, Complex.real_smul]
  have hcong : ∫⁻ x : ℝ, ‖𝓕⁻ (fun x : ℝ => lamg f s hD * (PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x) x‖ₑ ^ (2:ℝ)
      = ∫⁻ x : ℝ, ‖(gSch f s hD : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
    apply lintegral_congr; intro x
    rw [gSch, SchwartzMap.fourierInv_coe, hfun]
  rw [← hcong, Commons.Analysis.Fourier.BoundaryLayer.lintegral_pwInv hmem1 hmem2]
  have hint : Integrable (fun x : ℝ => ‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ ^ 2) := by
    have h := (memLp_two_iff_integrable_sq_norm
      ((PsiS f s (deltaF f s) (deltaF_pos f s hD)).memLp 2).aestronglyMeasurable).mp
      ((PsiS f s (deltaF f s) (deltaF_pos f s hD)).memLp 2)
    simpa using h
  have hne : 0 ≤ᵐ[(volume : Measure ℝ)] (fun x : ℝ => ‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hPsiL : ∫⁻ x : ℝ, ‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal (NP f s (deltaF f s) (deltaF_pos f s hD)) := by
    rw [NP]
    rw [show (fun x : ℝ => ‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ₑ ^ (2:ℝ))
        = fun x : ℝ => ENNReal.ofReal (‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ ^ 2) from by
      funext x
      rw [show ‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ₑ
          = ENNReal.ofReal ‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ from
            Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm _,
        ENNReal.rpow_ofNat, ENNReal.ofReal_pow (norm_nonneg _)]]
    rw [ofReal_integral_eq_lintegral_ofReal hint hne]
  have hnorm : ∀ x : ℝ, ‖lamg f s hD * (PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal ((lamg f s hD)^2) * ‖(PsiS f s (deltaF f s) (deltaF_pos f s hD) : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
    intro x
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [show ‖((lamg f s hD : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (lamg f s hD) from by
      rw [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm,
        Commons.Analysis.Fourier.BoundaryLayer.norm_ofReal, abs_of_nonneg (lamg_nonneg f s hD)]]
    rw [ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (lamg_nonneg f s hD)]
  simp only [hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hPsiL,
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (lamg f s hD)^2),
    lamg_sq f s hD, div_mul_cancel₀ _ (NP_pos f s (deltaF f s) (deltaF_pos f s hD) hD).ne']

private lemma rhs_inner_eq (N : ℕ) (lam : Fin N → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (hD : 0 < Df f s)
    (j : ℕ) (x : ℝ) :
    (∫ ξ in (-(1/2):ℝ)..(1/2), (𝓕 (⇑(gSch f s hD))) ξ
        * Set.indicator (Mfreq N lam j) (fun _ => (1:ℂ)) ξ
        * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ)))
      = lamg f s hD * multInt (Hm N lam f s j) x := by
  rw [multInt_Hm_interval N lam f s j x, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro ξ hξ
  have hξ' : |ξ| ≤ 1/2 := by
    rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)] at hξ
    rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
  beta_reduce
  rw [gS_fourier f s hD ξ]
  rw [show PsiS f s (deltaF f s) (deltaF_pos f s hD) ξ = GLam f s ξ from
    PsiS_eq_GLam f s (deltaF f s) (deltaF_pos f s hD) hξ']
  ring

/-- Uniform-in-`lam` form of the `ℝ ⇒ ℤ` transference: there is a single constant `C`
(the same for every finite frequency family `lam` and every finitely supported `f`) such that
the `ℓ²(ℤ)` periodised-neighbourhood maximal function is bounded by `C` times the real-line
band-pass maximal function of the band-limited realisation `g` (with `∫‖g‖² = ∑‖f n‖²`). -/
theorem z_neighborhood_of_real_bandpass_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : Fin N → ℝ),
      ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n : ℤ, n ∉ s → f n = 0) →
      ∃ (g : ℝ → ℂ), MeasureTheory.MemLp g 2 MeasureTheory.volume ∧
        (∫⁻ (x : ℝ), ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume = ∑ n ∈ s, ‖f n‖ₑ ^ (2 : ℝ)) ∧
        (∫⁻ m : ℤ, (⨆ j : ℕ, ‖∑ n ∈ s, f n *
            (∫ θ in Set.Icc (0 : ℝ) 1,
              Set.indicator
                {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
                (fun θ => Complex.exp (-(2 * Real.pi * Complex.I * (((m - n : ℤ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
                  (𝓕 g) ξ *
                    Set.indicator {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
                      (fun _ => (1 : ℂ)) ξ *
                    Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))‖ₑ) ^ (2 : ℝ)
                ∂MeasureTheory.volume) := by
  obtain ⟨C0, hC0pos, hC0⟩ := lattice_sup_le_integral_sup_multiplier_aux
  refine ⟨4 * C0, by positivity, ?_⟩
  intro N lam f s hs
  by_cases hD : Df f s = 0
  · have hf0 : f = 0 := by
      funext n
      by_cases hn : n ∈ s
      · have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg ‖f m‖)).mp
          (by rw [Df] at hD; exact hD)
        have h1 : ‖f n‖ ^ 2 = 0 := h2 n hn
        have h3 : ‖f n‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
        simpa using h3
      · exact hs n hn
    refine ⟨0, MemLp.zero, ?_, ?_⟩
    · rw [show f = 0 from hf0]; simp
    · rw [show f = 0 from hf0]; simp
  · have hDpos : 0 < Df f s := lt_of_le_of_ne (Df_nonneg f s) (Ne.symm hD)
    refine ⟨⇑(gSch f s hDpos), (gSch f s hDpos).memLp 2, ?_, ?_⟩
    · rw [gS_lintegral f s hDpos, Df,
        ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg ‖f n‖)]
      apply Finset.sum_congr rfl; intro n hn
      rw [show ‖f n‖ₑ = ENNReal.ofReal ‖f n‖ from
          Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm _,
        ENNReal.rpow_ofNat, ENNReal.ofReal_pow (norm_nonneg (f n))]
    · set RHSg : ℝ≥0∞ := ∫⁻ x : ℝ, (⨆ j : ℕ, ‖∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
          (𝓕 (⇑(gSch f s hDpos))) ξ *
            Set.indicator (Mfreq N lam j) (fun _ => (1 : ℂ)) ξ *
            Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.volume with hRHSg
      set NN : ℝ≥0∞ := ∫⁻ x : ℝ, (⨆ j : ℕ, ‖multInt (Hm N lam f s j) x‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.volume with hNN
      have hLat := hC0 (Hm N lam f s)
        (fun j => Hm_memLp N lam f s j 1) (fun j => Hm_memLp N lam f s j 2)
        (fun j ξ hξ => by rw [Hm, Set.indicator_of_notMem hξ, zero_mul])
      have hLin : ∀ m : ℤ, ∀ j : ℕ,
          (∑ n ∈ s, f n * (∫ θ in Set.Icc (0 : ℝ) 1,
              Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
                (fun θ => Complex.exp (-(2 * Real.pi * Complex.I * (((m - n : ℤ) : ℂ)) * (θ : ℂ)))) θ))
            = multInt (Hm N lam f s j) (m : ℝ) := by
        intro m j
        rw [show {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
              = Lfreq N lam j from rfl]
        rw [lattice_sum_eq N lam f s j m, multInt_Hm_eq N lam f s j m]
      have hLHS : (∫⁻ m : ℤ, (⨆ j : ℕ, ‖∑ n ∈ s, f n *
              (∫ θ in Set.Icc (0 : ℝ) 1,
                Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
                  (fun θ => Complex.exp (-(2 * Real.pi * Complex.I * (((m - n : ℤ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count)
          = ∫⁻ m : ℤ, (⨆ j : ℕ, ‖multInt (Hm N lam f s j) (m : ℝ)‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count := by
        apply lintegral_congr; intro m
        congr 1
        apply iSup_congr; intro j
        rw [show ‖∑ n ∈ s, f n * (∫ θ in Set.Icc (0 : ℝ) 1,
                Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
                  (fun θ => Complex.exp (-(2 * Real.pi * Complex.I * (((m - n : ℤ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ
            = ‖multInt (Hm N lam f s j) (m : ℝ)‖ₑ from by rw [hLin m j]]
      have hbase : ∀ x : ℝ, (⨆ j : ℕ, ‖∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
              (𝓕 (⇑(gSch f s hDpos))) ξ *
                Set.indicator (Mfreq N lam j) (fun _ => (1 : ℂ)) ξ *
                Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))‖ₑ)
          = ENNReal.ofReal (lamg f s hDpos) * (⨆ j : ℕ, ‖multInt (Hm N lam f s j) x‖ₑ) := by
        intro x
        rw [ENNReal.mul_iSup]
        apply iSup_congr; intro j
        rw [rhs_inner_eq N lam f s hDpos j x, enorm_mul,
          show ‖((lamg f s hDpos : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (lamg f s hDpos) from by
            rw [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm,
              Commons.Analysis.Fourier.BoundaryLayer.norm_ofReal,
              abs_of_nonneg (lamg_nonneg f s hDpos)]]
      have hRHS : RHSg = ENNReal.ofReal ((lamg f s hDpos) ^ 2) * NN := by
        rw [hRHSg, hNN, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr; intro x
        rw [hbase x, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        rw [ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (lamg_nonneg f s hDpos)]
      have hN : NN ≤ 4 * RHSg := by
        have h1 : ENNReal.ofReal ((1:ℝ) / 4) * NN ≤ RHSg := by
          rw [hRHS]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by
            have := lamg_ge f s hDpos; nlinarith [this, lamg_nonneg f s hDpos])) le_rfl
        have h2 : NN = 4 * (ENNReal.ofReal ((1:ℝ) / 4) * NN) := by
          rw [← mul_assoc, show ((4:ℝ≥0∞)) * ENNReal.ofReal ((1:ℝ) / 4) = 1 by
            rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
            norm_num, one_mul]
        rw [h2]
        exact mul_le_mul' le_rfl h1
      calc (∫⁻ m : ℤ, (⨆ j : ℕ, ‖∑ n ∈ s, f n *
              (∫ θ in Set.Icc (0 : ℝ) 1,
                Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
                  (fun θ => Complex.exp (-(2 * Real.pi * Complex.I * (((m - n : ℤ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count)
          = ∫⁻ m : ℤ, (⨆ j : ℕ, ‖multInt (Hm N lam f s j) (m : ℝ)‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count := hLHS
        _ ≤ ENNReal.ofReal C0 * NN :=
            (by simpa only [hNN, Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm] using hLat)
        _ ≤ ENNReal.ofReal C0 * (4 * RHSg) := mul_le_mul' le_rfl hN
        _ = ENNReal.ofReal (4 * C0) * RHSg := by
          rw [← mul_assoc, show ((4:ℝ≥0∞)) = ENNReal.ofReal (4:ℝ) from by norm_num,
            ← ENNReal.ofReal_mul hC0pos.le,
            show C0 * (4:ℝ) = 4 * C0 from by ring]

end
end Commons.Analysis.Fourier
