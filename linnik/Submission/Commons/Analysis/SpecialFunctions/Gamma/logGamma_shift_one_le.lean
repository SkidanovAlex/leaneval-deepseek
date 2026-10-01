import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_Binet
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_nonneg
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_le_t_div_12
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le

/-!
# A sharp vertical increment bound for `log ‖Γ‖` on the strip `1/2 ≤ Re s ≤ 4`

We prove

`log ‖Γ(u + i v)‖ ≤ log ‖Γ(1/2 + i v)‖ + (u - 1/2) (log (2 + |v|) + 1) + 3/5`

for `1/2 ≤ u ≤ 4` and all real `v`.  This is the standard "Stirling / Binet"
increment estimate: to first order the left-hand side equals
`(u - 1/2) log |v|`, and `log (2 + |v|) ≥ log |v|`, so the bound has room to spare.

## Method

For fixed `v` let `Φ(σ) = log ‖Γ(σ + i v)‖`.  The Binet formula

`ψ(z) - log z + 1/(2z) = -∫₀^∞ K(t) e^{-zt} dt`, `K(t) = 1/(e^t - 1) - 1/t + 1/2`,

(`digamma_logRem_Binet`) gives, on taking real parts at `z = σ + i v`,

`Re ψ(σ + i v) ≤ log |σ + i v| - σ/(2|σ + i v|²) + ∫₀^∞ K(t) e^{-σ t} dt`,

because `|Re e^{-zt}| ≤ e^{-σt}`.  Since `0 ≤ K(t) ≤ t/12`
(`digamma_logRem_kernel_nonneg`, `digamma_logRem_kernel_le_t_div_12`) and
`∫₀^∞ t e^{-σt} dt = 1/σ²`, the last term is at most `1/(12 σ²)`.  Finally
`log |σ + i v| ≤ log (2 + |v|) + 1` for `σ ≤ 4`, because `σ² + v² ≤ 4 (2 + |v|)²`.

Hence, with `C = log (2 + |v|) + 1`,

`deriv (fun σ => log ‖Γ(σ + i v)‖ - σ C + 1/(12 σ)) ≤ 0` on `(1/2, 4)`,

so `σ ↦ log ‖Γ(σ + i v)‖ - σ C + 1/(12 σ)` is antitone there
(`monotoneOn_of_deriv_nonneg`); evaluating at `u` and `1/2` and using
`1/(12 · 1/2) = 1/6 ≤ 3/5` gives the claim.

The derivative of `σ ↦ log ‖Γ(σ + i v)‖` is `Re ψ(σ + i v)`
(`hasDerivAt_log_norm_Gamma`, from the commons).
-/

open Complex MeasureTheory Set
open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

noncomputable section

lemma lgs_integral_id_exp_neg_mul (σ : ℝ) (hσ : 0 < σ) :
    (∫ t : ℝ in Ioi (0 : ℝ), t * Real.exp (-σ * t)) = 1 / σ ^ 2 := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := σ) (by norm_num) hσ
  have hR : (1 / σ) ^ (2 : ℝ) * Real.Gamma (2 : ℝ) = 1 / σ ^ 2 := by
    rw [Real.Gamma_two, Real.rpow_two]
    field_simp [hσ.ne']
  have hEqI : (∫ t in Ioi (0 : ℝ), t * Real.exp (-σ * t)) =
      (∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(σ * t))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change t * Real.exp (-σ * t) = t ^ ((2 : ℝ) - 1) * Real.exp (-(σ * t))
    have hpow : t ^ ((2 : ℝ) - 1) = t := by norm_num
    rw [hpow]
    congr 1
    ring
  calc
    (∫ t in Ioi (0 : ℝ), t * Real.exp (-σ * t))
        = ∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(σ * t)) := hEqI
    _ = (1 / σ) ^ (2 : ℝ) * Real.Gamma (2 : ℝ) := key
    _ = 1 / σ ^ 2 := hR

lemma lgs_integrable_id_exp_neg_mul (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-σ * t)) (Ioi (0 : ℝ)) := by
  refine Integrable.of_integral_ne_zero ?_
  change (∫ t : ℝ in Ioi (0 : ℝ), t * Real.exp (-σ * t)) ≠ 0
  rw [lgs_integral_id_exp_neg_mul σ hσ]
  positivity

lemma lgs_integrable_div12_exp (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => (t / 12) * Real.exp (-σ * t)) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun t : ℝ => (1 / 12) * (t * Real.exp (-σ * t))) (Ioi (0 : ℝ)) :=
    Integrable.const_mul (lgs_integrable_id_exp_neg_mul σ hσ) (1 / 12)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro t ht
  ring

lemma lgs_kernel_integral_le (σ : ℝ) (hσ : 0 < σ) :
    (∫ t in Ioi (0 : ℝ),
        (1 / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) * Real.exp (-σ * t))
      ≤ 1 / (12 * σ ^ 2) := by
  have hg_int := lgs_integrable_div12_exp σ hσ
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ),
      0 ≤ (1 / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) * Real.exp (-σ * t) := by
    intro t ht
    exact mul_nonneg (digamma_logRem_kernel_nonneg ht) (Real.exp_nonneg _)
  have hfg : ∀ t ∈ Ioi (0 : ℝ),
      (1 / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) * Real.exp (-σ * t)
        ≤ (t / 12) * Real.exp (-σ * t) := by
    intro t ht
    exact mul_le_mul_of_nonneg_right (digamma_logRem_kernel_le_t_div_12 t ht) (Real.exp_nonneg _)
  have hmono := setIntegral_mono_of_nonneg hnonneg hfg hg_int
  have hval : (∫ t in Ioi (0 : ℝ), (t / 12) * Real.exp (-σ * t)) = 1 / (12 * σ ^ 2) := by
    rw [show (fun t : ℝ => (t / 12) * Real.exp (-σ * t))
        = fun t : ℝ => (1 / 12) * (t * Real.exp (-σ * t)) by ext t; ring]
    rw [integral_const_mul, lgs_integral_id_exp_neg_mul σ hσ]
    field_simp [hσ.ne']
  linarith [hmono, hval.symm.le]

/-- Vertical bound on the real part of the digamma function: for `1/2 ≤ x ≤ 4` and all
real `v`, `Re ψ(x + iv) ≤ log(2+|v|) + 1 + 1/(12 x²)`. -/
lemma lgs_re_digamma_le (x v : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 4) :
    (Complex.digamma ((x : ℂ) + (v : ℂ) * Complex.I)).re
      ≤ Real.log (2 + |v|) + 1 + 1 / (12 * x ^ 2) := by
  set z : ℂ := (x : ℂ) + (v : ℂ) * Complex.I with hzdef
  have hzre : z.re = x := by simp [hzdef]
  have hzim : z.im = v := by simp [hzdef]
  have hz : 0 < z.re := by rw [hzre]; linarith
  have hxpos : 0 < x := by linarith
  have hB := digamma_logRem_Binet z hz
  have hre := congrArg Complex.re hB
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.log_re] at hre
  have hmulre : ((2 : ℂ)⁻¹ * z⁻¹).re = x / (2 * ‖z‖ ^ 2) := by
    have h2c : ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have h2re : ((2 : ℂ)⁻¹).re = (1 : ℝ) / 2 := by rw [h2c]; norm_num
    have h2im : ((2 : ℂ)⁻¹).im = 0 := by rw [h2c]; norm_num
    have h1 : ((2 : ℂ)⁻¹ * z⁻¹).re = ((2 : ℂ)⁻¹).re * (z⁻¹).re - ((2 : ℂ)⁻¹).im * (z⁻¹).im :=
      Complex.mul_re _ _
    have h4 : (z⁻¹).re = x / ‖z‖ ^ 2 := by
      rw [Complex.inv_re, Complex.normSq_eq_norm_sq, hzre]
    rw [h1, h2re, h2im, h4]
    ring
  rw [hmulre] at hre
  -- hre : (ψ z).re - Real.log ‖z‖ + x / (2 * ‖z‖^2) = -(∫ ...).re
  have hnorm : -((∫ t in Ioi (0 : ℝ),
        ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(z * (t : ℂ))))).re ≤ 1 / (12 * x ^ 2) := by
    calc -((∫ t in Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))).re
        = (-(∫ t in Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))).re := by rw [Complex.neg_re]
      _ ≤ ‖-(∫ t in Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))‖ := Complex.re_le_norm _
      _ = ‖(∫ t in Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))‖ := by rw [norm_neg]
      _ ≤ ∫ t in Ioi (0 : ℝ), ‖((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ)))‖ := norm_integral_le_integral_norm _
      _ = ∫ t in Ioi (0 : ℝ),
            (1 / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) * Real.exp (-x * t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht0 : 0 < t := ht
          have hk0 : 0 ≤ (1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2 :=
            digamma_logRem_kernel_nonneg ht0
          have hzx : (-(z * (t : ℂ))).re = -(x * t) := by
            simp [Complex.mul_re, hzre, hzim]
          simp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0, Complex.norm_exp, hzx]
          ring
      _ ≤ 1 / (12 * x ^ 2) := lgs_kernel_integral_le x hxpos
  have hlog : Real.log ‖z‖ ≤ Real.log (2 + |v|) + 1 := by
    have hsq : ‖z‖ ^ 2 = x ^ 2 + v ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hzre, hzim]
      ring
    have hvn : (0 : ℝ) ≤ |v| := abs_nonneg v
    have hle : ‖z‖ ≤ 2 * (2 + |v|) := by
      have h2 : ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      rw [h2, hsq]
      have hbb : x ^ 2 + v ^ 2 ≤ (2 * (2 + |v|)) ^ 2 := by
        have hv2 : v ^ 2 = |v| ^ 2 := by rw [sq_abs]
        rw [hv2]
        nlinarith [hvn, sq_nonneg (|v| - 4), sq_nonneg (x - 4)]
      calc Real.sqrt (x ^ 2 + v ^ 2) ≤ Real.sqrt ((2 * (2 + |v|)) ^ 2) :=
            Real.sqrt_le_sqrt hbb
        _ = 2 * (2 + |v|) := Real.sqrt_sq (by positivity)
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.re_le_norm z)
    calc Real.log ‖z‖ ≤ Real.log (2 * (2 + |v|)) := Real.log_le_log hzpos hle
      _ = Real.log 2 + Real.log (2 + |v|) :=
            Real.log_mul (by norm_num) (by positivity)
      _ ≤ Real.log (2 + |v|) + 1 := by
            have h : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
              linarith
            linarith
  have hkey : (Complex.digamma z).re ≤ Real.log (2 + |v|) + 1 + 1 / (12 * x ^ 2) := by
    have hval : (Complex.digamma z).re = Real.log ‖z‖ - x / (2 * ‖z‖ ^ 2) - (∫ t in Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ)))).re := by linarith [hre]
    rw [hval]
    have hx2nn : 0 ≤ x / (2 * ‖z‖ ^ 2) := by positivity
    linarith [hnorm, hlog, hx2nn]
  simpa [hzdef] using hkey



theorem logGamma_shift_one_le (u v : ℝ) (h1 : (1 : ℝ) / 2 ≤ u) (h2 : u ≤ 4) :
    Real.log ‖Complex.Gamma ((u : ℂ) + Complex.I * (v : ℂ))‖ ≤
      Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (v : ℂ))‖ +
        (u - 1 / 2) * (Real.log (2 + |v|) + 1) + 3 / 5 := by
  have hgoal : Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ +
        (u - 1 / 2) * (Real.log (2 + |v|) + 1) + 3 / 5 := by
    set C : ℝ := Real.log (2 + |v|) + 1 with hC
    set F : ℝ → ℝ := fun σ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖
      - σ * C + (1 / 12) * σ⁻¹ with hF
    have hcont : ContinuousOn (fun σ : ℝ => -F σ) (Icc (1 / 2 : ℝ) 4) := by
      have hA : ContinuousOn
          (fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖)
          (Icc (1 / 2 : ℝ) 4) := by
        intro σ hσ
        have hσ0 : 0 < σ := by linarith [hσ.1]
        exact (hasDerivAt_log_norm_Gamma σ v hσ0).continuousAt.continuousWithinAt
      have hB : ContinuousOn (fun σ : ℝ => σ * C) (Icc (1 / 2 : ℝ) 4) :=
        continuousOn_id.mul continuousOn_const
      have hD : ContinuousOn (fun σ : ℝ => (1 / 12) * σ⁻¹) (Icc (1 / 2 : ℝ) 4) :=
        (ContinuousOn.inv₀ continuousOn_id (by
          intro σ hσ
          exact ne_of_gt (by linarith [hσ.1] : (0 : ℝ) < σ))).const_mul (1 / 12)
      have hmain : ContinuousOn (fun σ : ℝ =>
          -((fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖) σ
            - (fun σ : ℝ => σ * C) σ + ((1 / 12) * σ⁻¹))) (Icc (1 / 2 : ℝ) 4) :=
        ((hA.sub hB).add hD).neg
      convert hmain using 1
    have hdiff : DifferentiableOn ℝ (fun σ : ℝ => -F σ) (interior (Icc (1 / 2 : ℝ) 4)) := by
      rw [interior_Icc]
      intro σ hσ
      have hσ0 : 0 < σ := by linarith [hσ.1]
      have hA : DifferentiableAt ℝ
          (fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖) σ :=
        (hasDerivAt_log_norm_Gamma σ v hσ0).differentiableAt
      have hB : DifferentiableAt ℝ (fun σ : ℝ => σ * C) σ :=
        differentiableAt_id.mul_const C
      have hD : DifferentiableAt ℝ (fun σ : ℝ => (1 / 12) * σ⁻¹) σ :=
        (hasDerivAt_inv hσ0.ne').const_mul (1 / 12) |>.differentiableAt
      have hmain : DifferentiableAt ℝ (fun σ : ℝ =>
          -((fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖) σ
            - (fun σ : ℝ => σ * C) σ + ((1 / 12) * σ⁻¹))) σ :=
        ((hA.sub hB).add hD).neg
      have hw : DifferentiableWithinAt ℝ (fun σ : ℝ =>
          -((fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖) σ
            - (fun σ : ℝ => σ * C) σ + ((1 / 12) * σ⁻¹)))
          (Ioo (1 / 2 : ℝ) 4) σ :=
        hmain.differentiableWithinAt
      convert hw using 1
    have hderiv : ∀ σ ∈ interior (Icc (1 / 2 : ℝ) 4), 0 ≤ deriv (fun σ : ℝ => -F σ) σ := by
      rw [interior_Icc]
      intro σ hσ
      have hσ0 : 0 < σ := by linarith [hσ.1]
      have hσ4 : σ ≤ 4 := le_of_lt hσ.2
      have hd1 : HasDerivAt
          (fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖)
          ((Complex.digamma ((σ : ℂ) + (v : ℂ) * Complex.I)).re) σ :=
        hasDerivAt_log_norm_Gamma σ v hσ0
      have hd2 : HasDerivAt (fun σ : ℝ => σ * C) C σ := by
        simpa using (hasDerivAt_id σ).mul_const C
      have hd3 : HasDerivAt (fun σ : ℝ => (1 / 12) * σ⁻¹) ((1 / 12) * (-(σ ^ 2)⁻¹)) σ :=
        (hasDerivAt_inv hσ0.ne').const_mul (1 / 12)
      have hFd : HasDerivAt (fun σ : ℝ =>
          (fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖) σ
            - (fun σ : ℝ => σ * C) σ + ((1 / 12) * σ⁻¹))
          ((Complex.digamma ((σ : ℂ) + (v : ℂ) * Complex.I)).re - C + (1 / 12) * (-(σ ^ 2)⁻¹)) σ :=
        (hd1.sub hd2).add hd3
      have hderivneg : deriv (fun σ : ℝ => -F σ) σ =
          -((Complex.digamma ((σ : ℂ) + (v : ℂ) * Complex.I)).re - C + (1 / 12) * (-(σ ^ 2)⁻¹)) := by
        have hFF : (fun σ : ℝ => -F σ) = fun σ : ℝ =>
            -((fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖) σ
              - (fun σ : ℝ => σ * C) σ + ((1 / 12) * σ⁻¹)) := by
          ext τ
          simp [hF]
        rw [hFF]
        exact hFd.neg.deriv
      rw [hderivneg]
      have hψ := lgs_re_digamma_le σ v (le_of_lt hσ.1) hσ4
      have hinv : (1 / 12) * (-(σ ^ 2)⁻¹) = -(1 / (12 * σ ^ 2)) := by field_simp
      rw [hinv, hC]
      linarith [hψ]
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (1 / 2 : ℝ) 4) hcont hdiff hderiv
    have hle : -F (1 / 2) ≤ -F u :=
      hmono (by constructor <;> norm_num) ⟨h1, h2⟩ h1
    have hFu : F u ≤ F (1 / 2) := by linarith
    simp only [hF] at hFu
    have hu0 : 0 < u := by linarith
    have hhalf : (1 / 12) * ((1 / 2 : ℝ))⁻¹ = 1 / 6 := by norm_num
    have hinvnn : 0 ≤ (1 / 12) * u⁻¹ := by positivity
    have hmain2 : Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
        Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ + (u - 1 / 2) * C + 3 / 5 := by
      linarith [hFu, hhalf, hinvnn]
    rw [hC] at hmain2
    exact hmain2
  have hIv : Complex.I * (v : ℂ) = (v : ℂ) * Complex.I := mul_comm _ _
  rw [hIv, show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num]
  exact hgoal

end

end Commons.Analysis.SpecialFunctions.Gamma
