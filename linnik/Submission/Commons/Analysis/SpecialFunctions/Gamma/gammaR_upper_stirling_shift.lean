import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_Binet
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_nonneg
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_le_t_div_12
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logGamma_shift_one_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_sharp_upper
import Submission.Commons.Analysis.SpecialFunctions.Gamma.arctan_shift_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.hasDerivAt_stirling_Q
import Submission.Commons.Analysis.SpecialFunctions.Gamma.stirling_shift_aux
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_circleExcess_le

open Complex MeasureTheory Set
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

open Commons.NumberTheory.DirichletCharacter (log_Gamma_half_vertical_le)

/-- `log (2 * π) ≤ 2`. -/
lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  have he : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [sq, ← Real.exp_add]; norm_num
  have hlt : 2 * Real.pi < Real.exp 1 ^ 2 := by
    nlinarith [Real.exp_one_gt_d9, Real.pi_lt_d4]
  have := Real.log_lt_log (by positivity : (0:ℝ) < 2 * Real.pi) hlt
  rw [he, Real.log_exp] at this
  linarith

/-- **Sharp vertical bound for the real part of the digamma function.**
For `u > 0` and any real `v`,
`Re ψ(u + i v) ≤ log |u + i v| - u/(2|u+i v|²) + 1/(12 u²)`. -/
lemma digamma_re_vertical_sharp_le (u v : ℝ) (hu : 0 < u) :
    (Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)).re ≤
      Real.log (Real.sqrt (u ^ 2 + v ^ 2)) - u / (2 * (u ^ 2 + v ^ 2)) + 1 / (12 * u ^ 2) := by
  set z : ℂ := (u : ℂ) + (v : ℂ) * Complex.I with hzdef
  have hzre : z.re = u := by simp [hzdef]
  have hzim : z.im = v := by simp [hzdef]
  have hz : 0 < z.re := by rw [hzre]; exact hu
  have hB := digamma_logRem_Binet z hz
  have hre := congrArg Complex.re hB
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.log_re] at hre
  have hmulre : ((2 : ℂ)⁻¹ * z⁻¹).re = u / (2 * ‖z‖ ^ 2) := by
    have h2c : ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have h2re : ((2 : ℂ)⁻¹).re = (1 : ℝ) / 2 := by rw [h2c]; norm_num
    have h2im : ((2 : ℂ)⁻¹).im = 0 := by rw [h2c]; norm_num
    have h1 : ((2 : ℂ)⁻¹ * z⁻¹).re = ((2 : ℂ)⁻¹).re * (z⁻¹).re - ((2 : ℂ)⁻¹).im * (z⁻¹).im :=
      Complex.mul_re _ _
    have h4 : (z⁻¹).re = u / ‖z‖ ^ 2 := by
      rw [Complex.inv_re, Complex.normSq_eq_norm_sq, hzre]
    rw [h1, h2re, h2im, h4]
    ring
  rw [hmulre] at hre
  have hnorm : -((∫ t in Set.Ioi (0 : ℝ),
        ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(z * (t : ℂ))))).re ≤ 1 / (12 * u ^ 2) := by
    calc -((∫ t in Set.Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))).re
        = (-(∫ t in Set.Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))).re := by rw [Complex.neg_re]
      _ ≤ ‖-(∫ t in Set.Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))‖ := Complex.re_le_norm _
      _ = ‖(∫ t in Set.Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ))))‖ := by rw [norm_neg]
      _ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ)))‖ := norm_integral_le_integral_norm _
      _ = ∫ t in Set.Ioi (0 : ℝ),
            (1 / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) * Real.exp (-u * t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht0 : 0 < t := ht
          have hk0 : 0 ≤ (1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2 :=
            digamma_logRem_kernel_nonneg ht0
          have hzx : (-(z * (t : ℂ))).re = -(u * t) := by
            simp [Complex.mul_re, hzre, hzim]
          simp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0, Complex.norm_exp, hzx]
          ring_nf
      _ ≤ 1 / (12 * u ^ 2) := lgs_kernel_integral_le u hu
  have hzsq : ‖z‖ ^ 2 = u ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hzre, hzim]
    ring
  have hlogeq : Real.log ‖z‖ = Real.log (Real.sqrt (u ^ 2 + v ^ 2)) := by
    congr 1
    rw [← hzsq]
    exact (Real.sqrt_sq (norm_nonneg z)).symm
  have hval : (Complex.digamma z).re =
      Real.log ‖z‖ - u / (2 * ‖z‖ ^ 2) - (∫ t in Set.Ioi (0 : ℝ),
          ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(z * (t : ℂ)))).re := by linarith [hre]
  rw [hval, hlogeq]
  have : u / (2 * ‖z‖ ^ 2) = u / (2 * (u ^ 2 + v ^ 2)) := by rw [hzsq]
  rw [this]
  linarith [hnorm]

/-- **Vertical increment bound for `log ‖Γ‖`.**  For `1/2 ≤ u ≤ 8` and `v ≥ 0`,
`log ‖Γ(u + i v)‖ - log ‖Γ(1/2 + i v)‖ ≤ (u - 1/2) log (4 + 2 v) + (1 - (1/2) log (2π))`.

This is the sharp Stirling-type increment: the derivative bound
`Re ψ(s + iv) ≤ log|s + iv| - s/(2|s+iv|²) + 1/(12 s²)`
is integrated against the explicit antiderivative
`Q(s) = (s-1/2) log|s+iv| - s + v arctan(s/v) - 1/(12s)`; the remaining real inequality
uses `stirling_shift_aux` and `arctan_shift_bound`. -/
lemma log_Gamma_shift_increment (u v : ℝ) (hu1 : (1 : ℝ) / 2 ≤ u) (hu2 : u ≤ 8) (hv : 0 ≤ v) :
    Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ -
        Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (u - 1 / 2) * Real.log (4 + 2 * v) + (1 - (1 / 2) * Real.log (2 * Real.pi)) := by
  let Q : ℝ → ℝ := fun s => (s - 1 / 2) * Real.log (Real.sqrt (s ^ 2 + v ^ 2)) - s
      + v * Real.arctan (s / v) - 1 / (12 * s)
  let Ψ : ℝ → ℝ := fun s => Real.log ‖Complex.Gamma ((s : ℂ) + (v : ℂ) * Complex.I)‖ - Q s
  have hQderiv : ∀ s : ℝ, 0 < s → HasDerivAt Q
      (Real.log (Real.sqrt (s ^ 2 + v ^ 2)) - s / (2 * (s ^ 2 + v ^ 2)) + 1 / (12 * s ^ 2)) s := by
    intro s hs
    exact hasDerivAt_stirling_Q s v hs
  have hcont : ContinuousOn Ψ (Set.Icc (1 / 2 : ℝ) u) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hf : ContinuousAt (fun σ : ℝ => Real.log ‖Complex.Gamma ((σ : ℂ) + (v : ℂ) * Complex.I)‖) s :=
      (hasDerivAt_log_norm_Gamma s v hs0).continuousAt
    have hq : ContinuousAt Q s := (hQderiv s hs0).continuousAt
    exact (hf.sub hq).continuousWithinAt
  have hdiff : DifferentiableOn ℝ Ψ (interior (Set.Icc (1 / 2 : ℝ) u)) := by
    intro s hs
    rw [interior_Icc] at hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hd := (hasDerivAt_log_norm_Gamma s v hs0).sub (hQderiv s hs0)
    exact hd.differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ interior (Set.Icc (1 / 2 : ℝ) u), deriv Ψ s ≤ 0 := by
    intro s hs
    rw [interior_Icc] at hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hd : HasDerivAt Ψ ((Complex.digamma ((s : ℂ) + (v : ℂ) * Complex.I)).re -
        (Real.log (Real.sqrt (s ^ 2 + v ^ 2)) - s / (2 * (s ^ 2 + v ^ 2)) + 1 / (12 * s ^ 2))) s :=
      (hasDerivAt_log_norm_Gamma s v hs0).sub (hQderiv s hs0)
    rw [hd.deriv]
    have hdψ := digamma_re_vertical_sharp_le s v hs0
    linarith
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc (1 / 2 : ℝ) u) hcont hdiff hderiv
  have hle := hanti (Set.left_mem_Icc.mpr hu1) (Set.right_mem_Icc.mpr hu1) hu1
  have hle' : Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ - Q u ≤
      Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖ - Q (1 / 2) := hle
  have hQbound : Q u - Q (1 / 2) ≤
      (u - 1 / 2) * Real.log (4 + 2 * v) + (1 - (1 / 2) * Real.log (2 * Real.pi)) := by
    have hsplit : Q u - Q (1 / 2) = (u - 1 / 2) * Real.log (Real.sqrt (u ^ 2 + v ^ 2)) - u
        + v * (Real.arctan (u / v) - Real.arctan (1 / (2 * v))) - 1 / (12 * u) + 2 / 3 := by
      have h12 : ((1 : ℝ) / 2) / v = 1 / (2 * v) := by rw [div_div]
      simp only [Q, h12]
      ring
    rw [hsplit]
    have harctan := arctan_shift_bound u v hu1 hv
    have hF := stirling_shift_aux u v hu1 hu2 hv
    have hconst : (0 : ℝ) ≤ 1 - (1 / 2) * Real.log (2 * Real.pi) := by
      linarith [log_two_pi_le_two]
    have hE : (0 : ℝ) ≤ (u - 1 / 2) * Real.log (4 + 2 * v) -
        (u - 1 / 2) * Real.log (Real.sqrt (u ^ 2 + v ^ 2)) + u - (2 * u - 1) * v ^ 2 / (2 * v ^ 2 + u)
        + 1 / (12 * u) + 1 / 3 - (1 / 2) * Real.log (2 * Real.pi) := by
      have hlogdiv : Real.log ((4 + 2 * v) / Real.sqrt (u ^ 2 + v ^ 2))
          = Real.log (4 + 2 * v) - Real.log (Real.sqrt (u ^ 2 + v ^ 2)) := by
        rw [Real.log_div] <;> positivity
      have hid : (u - 1 / 2) * Real.log (4 + 2 * v) -
          (u - 1 / 2) * Real.log (Real.sqrt (u ^ 2 + v ^ 2)) + u - (2 * u - 1) * v ^ 2 / (2 * v ^ 2 + u)
          + 1 / (12 * u) + 1 / 3 - (1 / 2) * Real.log (2 * Real.pi)
          = (u - 1 / 2) * (Real.log ((4 + 2 * v) / Real.sqrt (u ^ 2 + v ^ 2)) + u / (2 * v ^ 2 + u) - 1 / (6 * u))
            + (1 - (1 / 2) * Real.log (2 * Real.pi)) := by
        rw [hlogdiv]
        have hu : u ≠ 0 := by linarith
        have hden : 2 * v ^ 2 + u ≠ 0 := by positivity
        field_simp
        ring
      rw [hid]
      have : (0 : ℝ) ≤ (u - 1 / 2) * (Real.log ((4 + 2 * v) / Real.sqrt (u ^ 2 + v ^ 2)) +
          u / (2 * v ^ 2 + u) - 1 / (6 * u)) := mul_nonneg (by linarith) hF
      linarith
    linarith
  linarith


/-- **Upper bound for `log ‖Γ‖` on the vertical strip `1/2 ≤ Re ≤ 8`.**
For `1/2 ≤ u ≤ 8` and all real `v`,
`log ‖Γ(u + i v)‖ ≤ (u - 1/2) log (4 + 2|v|) + 1 - (π/2)|v|`. -/
lemma log_Gamma_vertical_le (u v : ℝ) (hu1 : (1 : ℝ) / 2 ≤ u) (hu2 : u ≤ 8) :
    Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (u - 1 / 2) * Real.log (4 + 2 * |v|) + 1 - (Real.pi / 2) * |v| := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
    have hinc := log_Gamma_shift_increment u v hu1 hu2 hv
    have hhalf := log_Gamma_half_vertical_le v
    rw [abs_of_nonneg hv] at hhalf
    have harg : ((1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I = (1 / 2 : ℂ) + Complex.I * (v : ℂ) := by
      apply Complex.ext <;> simp
    rw [← harg] at hhalf
    linarith
  · rw [not_le] at hv
    rw [abs_of_neg hv]
    have hw : 0 ≤ -v := by linarith
    have hconj : ((u : ℂ) + (v : ℂ) * Complex.I) =
        (starRingEnd ℂ) ((u : ℂ) + (((-v) : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    have hnormeq : ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ =
        ‖Complex.Gamma ((u : ℂ) + (((-v) : ℝ) : ℂ) * Complex.I)‖ := by
      rw [hconj, Complex.Gamma_conj, Complex.norm_conj]
    rw [hnormeq]
    have hinc := log_Gamma_shift_increment u (-v) hu1 hu2 hw
    have hhalf := log_Gamma_half_vertical_le (-v)
    rw [abs_of_nonneg hw] at hhalf
    have harg : ((1 / 2 : ℝ) : ℂ) + (((-v) : ℝ) : ℂ) * Complex.I =
        (1 / 2 : ℂ) + Complex.I * (((-v) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [← harg] at hhalf
    linarith

/-- **An explicit upper Stirling bound for `Γℝ` with a shift.**
For `1 ≤ σ ≤ 16` and all real `T`,
`log ‖Γℝ (σ + i T)‖ ≤ ((σ-1)/2) log (4 + |T|) + 1 - (σ/2) log π - (π/4)|T|`. -/
theorem gammaR_upper_stirling_shift {σ T : ℝ} (hσ : 1 ≤ σ) (hσ' : σ ≤ 16) :
    Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
      ((σ - 1) / 2) * Real.log (4 + |T|) + 1 - (σ / 2) * Real.log Real.pi -
        (Real.pi / 4) * |T| := by
  have hσpos : 0 < σ := by linarith
  rw [log_norm_gammaR_eq σ T hσpos]
  have hu1 : (1 : ℝ) / 2 ≤ σ / 2 := by linarith
  have hu2 : σ / 2 ≤ 8 := by linarith
  have h := log_Gamma_vertical_le (σ / 2) (T / 2) hu1 hu2
  have habs : |T / 2| = |T| / 2 := by rw [abs_div]; norm_num
  rw [habs] at h
  have h4 : 4 + 2 * (|T| / 2) = 4 + |T| := by ring
  rw [h4] at h
  have hpi : (Real.pi / 2) * (|T| / 2) = (Real.pi / 4) * |T| := by ring
  rw [hpi] at h
  have hcoef : σ / 2 - 1 / 2 = (σ - 1) / 2 := by ring
  rw [hcoef] at h
  have he : (((σ / 2 : ℝ)) : ℂ) + Complex.I * ((T / 2 : ℝ) : ℂ) =
      (((σ / 2 : ℝ)) : ℂ) + (((T / 2 : ℝ)) : ℂ) * Complex.I := by
    rw [mul_comm]
  rw [he]
  linarith


end Commons.Analysis.SpecialFunctions.Gamma
