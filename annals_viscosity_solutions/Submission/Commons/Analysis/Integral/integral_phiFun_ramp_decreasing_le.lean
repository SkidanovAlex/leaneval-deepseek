import Mathlib
import Submission.Commons.Analysis.Integral.phiFun_nonneg_of_le_eighth
import Submission.Commons.Analysis.Integral.abs_phiFun_le_six_mul
import Submission.Commons.Analysis.Integral.measurable_phiFun_kernel

namespace Commons.Analysis.Integral

open MeasureTheory Set intervalIntegral

/-- The transfer function of the circle average:
`phiFun v = (1/(2π)) ∫_θ ((1 + v² + 2 v cos θ) ^ (-1/2) - 1) dθ`. -/
private noncomputable def phiFun (v : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
    (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1)

private lemma phiFun_zero : phiFun 0 = 0 := by
  unfold phiFun
  have h : (fun theta : ℝ =>
      ((1 + (0:ℝ) ^ 2 + 2 * (0:ℝ) * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1) = fun _ => (0:ℝ) := by
    funext theta
    simp [Real.one_rpow]
  rw [h, intervalIntegral.integral_zero, mul_zero]

/-- Pointwise bound `|phiFun v| ≤ 6 v` for `0 ≤ v ≤ 1/2`. -/
private lemma abs_phiFun_le_six_mul' {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 2) :
    |phiFun v| ≤ 6 * v := by
  rcases lt_or_eq_of_le hv0 with hvpos | rfl
  · unfold phiFun
    exact abs_phiFun_le_six_mul v hvpos hv
  · rw [phiFun_zero]; simp

/-- `0 ≤ phiFun v` for `0 ≤ v ≤ 1/8`. -/
private lemma phiFun_nonneg' {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 8) : 0 ≤ phiFun v := by
  unfold phiFun
  exact phiFun_nonneg_of_le_eighth v hv0 hv

/-- The scaled variable `a(t) = (T - t) / (c t ^ (2/3) z)` lies in `[0, 1/8]` on `[T-ρ, T]`. -/
private lemma ramp_a_mem {c z ρ T : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z)
    (hρT : ρ < T) (hsmall : ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) ≤ 1/8) {t : ℝ}
    (ht : t ∈ Icc (T - ρ) T) :
    0 ≤ (T - t) / (c * t ^ ((2:ℝ)/3) * z) ∧ (T - t) / (c * t ^ ((2:ℝ)/3) * z) ≤ 1/8 := by
  obtain ⟨htlo, hthi⟩ := ht
  have htpos : 0 < t := by linarith
  have hTρpos : 0 < T - ρ := by linarith
  have hdenpos : 0 < c * t ^ ((2:ℝ)/3) * z :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos htpos _)) hz
  have hdenρpos : 0 < c * (T - ρ) ^ ((2:ℝ)/3) * z :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos hTρpos _)) hz
  have hnum_nonneg : 0 ≤ T - t := by linarith
  have hnum_le : T - t ≤ ρ := by linarith
  have hpow_le : (T - ρ) ^ ((2:ℝ)/3) ≤ t ^ ((2:ℝ)/3) :=
    Real.rpow_le_rpow (by linarith) htlo (by norm_num)
  have hden_le : c * (T - ρ) ^ ((2:ℝ)/3) * z ≤ c * t ^ ((2:ℝ)/3) * z := by
    have h1 : c * (T - ρ) ^ ((2:ℝ)/3) ≤ c * t ^ ((2:ℝ)/3) :=
      mul_le_mul_of_nonneg_left hpow_le hc.le
    exact mul_le_mul_of_nonneg_right h1 hz.le
  refine ⟨div_nonneg hnum_nonneg hdenpos.le, ?_⟩
  exact le_trans (div_le_div₀ hρ.le hnum_le hdenρpos hden_le) hsmall

/-- Dominating bound for the `ramp` integrand on `[T-ρ, T]`. -/
private lemma ramp_integrand_abs_le {c z ρ T : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z)
    (hρT : ρ < T) (hsmall : ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) ≤ 1/8) {t : ℝ}
    (ht : t ∈ Icc (T - ρ) T) :
    |(1 / (c * t ^ ((2:ℝ)/3) * z)) * phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))|
      ≤ 6 * ρ / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := by
  obtain ⟨ha0, ha8⟩ := ramp_a_mem hc hρ hz hρT hsmall ht
  obtain ⟨htlo, hthi⟩ := ht
  have hTρpos : 0 < T - ρ := by linarith
  have htpos : 0 < t := by linarith
  have hdenpos : 0 < c * t ^ ((2:ℝ)/3) * z :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos htpos _)) hz
  have hphi : |phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))| ≤ 6 * ((T - t) / (c * t ^ ((2:ℝ)/3) * z)) :=
    abs_phiFun_le_six_mul' ha0 (by linarith)
  have hhalf_pos : (0:ℝ) < 1 / (c * t ^ ((2:ℝ)/3) * z) := one_div_pos.mpr hdenpos
  have hstep1 :
      |(1 / (c * t ^ ((2:ℝ)/3) * z)) * phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))|
        = (1 / (c * t ^ ((2:ℝ)/3) * z)) * |phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))| := by
    rw [abs_mul, abs_of_pos hhalf_pos]
  have hstep2 :
      (1 / (c * t ^ ((2:ℝ)/3) * z)) * |phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))|
        ≤ (1 / (c * t ^ ((2:ℝ)/3) * z)) * (6 * ((T - t) / (c * t ^ ((2:ℝ)/3) * z))) :=
    mul_le_mul_of_nonneg_left hphi (le_of_lt hhalf_pos)
  have hstep3 :
      (1 / (c * t ^ ((2:ℝ)/3) * z)) * (6 * ((T - t) / (c * t ^ ((2:ℝ)/3) * z)))
        = 6 * (T - t) / (c ^ 2 * t ^ ((4:ℝ)/3) * z ^ 2) := by
    have hpow : t ^ ((2:ℝ)/3) * t ^ ((2:ℝ)/3) = t ^ ((4:ℝ)/3) := by
      rw [← Real.rpow_add htpos]; norm_num
    rw [← hpow]
    field_simp
  have hstep4 :
      6 * (T - t) / (c ^ 2 * t ^ ((4:ℝ)/3) * z ^ 2)
        ≤ 6 * ρ / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := by
    have ht4 : (T - ρ) ^ ((4:ℝ)/3) ≤ t ^ ((4:ℝ)/3) :=
      Real.rpow_le_rpow (by linarith) htlo (by norm_num)
    have hden2_le : c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2 ≤ c ^ 2 * t ^ ((4:ℝ)/3) * z ^ 2 := by
      have h1 : c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) ≤ c ^ 2 * t ^ ((4:ℝ)/3) :=
        mul_le_mul_of_nonneg_left ht4 (sq_nonneg c)
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg z)
    have hden2_pos : 0 < c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2 :=
      mul_pos (mul_pos (pow_pos hc 2) (Real.rpow_pos_of_pos hTρpos _)) (pow_pos hz 2)
    have hden1_pos : (0:ℝ) < c ^ 2 * t ^ ((4:ℝ)/3) * z ^ 2 :=
      mul_pos (mul_pos (pow_pos hc 2) (Real.rpow_pos_of_pos htpos _)) (pow_pos hz 2)
    calc 6 * (T - t) / (c ^ 2 * t ^ ((4:ℝ)/3) * z ^ 2)
        ≤ 6 * ρ / (c ^ 2 * t ^ ((4:ℝ)/3) * z ^ 2) :=
          div_le_div_of_nonneg_right (by linarith) hden1_pos.le
      _ ≤ 6 * ρ / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hden2_pos hden2_le
  calc |(1 / (c * t ^ ((2:ℝ)/3) * z)) * phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))|
      = (1 / (c * t ^ ((2:ℝ)/3) * z)) * |phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))| := hstep1
    _ ≤ (1 / (c * t ^ ((2:ℝ)/3) * z)) * (6 * ((T - t) / (c * t ^ ((2:ℝ)/3) * z))) := hstep2
    _ = 6 * (T - t) / (c ^ 2 * t ^ ((4:ℝ)/3) * z ^ 2) := hstep3
    _ ≤ 6 * ρ / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := hstep4

theorem integral_phiFun_ramp_decreasing_le {c z ρ T : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z)
    (hρT : ρ < T) (hsmall : ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) ≤ 1/8) :
    ∫ t in (T-ρ)..T, (1 / (c * t ^ ((2:ℝ)/3) * z)) *
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
          (((1 + ((T - t) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
            + 2 * ((T - t) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos theta)
            ^ (-(1:ℝ)/2)) - 1))
      ≤ 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := by
  have hle : T - ρ ≤ T := by linarith
  have hTρpos : 0 < T - ρ := by linarith
  set F : ℝ → ℝ := fun t => (1 / (c * t ^ ((2:ℝ)/3) * z)) * phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z)) with hF
  set K : ℝ := 6 * ρ / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) with hK
  change ∫ t in (T-ρ)..T, F t ≤ 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2)
  have hFmeas : Measurable F := by
    rw [hF]
    have h1 : Measurable (fun t : ℝ => (1:ℝ) / (c * t ^ ((2:ℝ)/3) * z)) := by fun_prop
    have h2 : Measurable (fun t : ℝ => (T - t) / (c * t ^ ((2:ℝ)/3) * z)) := by fun_prop
    have h3 : Measurable (fun t : ℝ => phiFun ((T - t) / (c * t ^ ((2:ℝ)/3) * z))) := by
      unfold phiFun
      exact measurable_phiFun_kernel.comp h2
    exact h1.mul h3
  have hFint : IntegrableOn F (Ioc (T-ρ) T) volume := by
    refine IntegrableOn.of_bound ?_ ?_ K ?_
    · exact measure_Ioc_lt_top
    · rw [hF]; exact hFmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htIcc : t ∈ Icc (T - ρ) T := ⟨le_of_lt ht.1, ht.2⟩
      rw [Real.norm_eq_abs, hF, hK]
      exact ramp_integrand_abs_le hc hρ hz hρT hsmall htIcc
  have hKint : IntegrableOn (fun _ : ℝ => K) (Ioc (T-ρ) T) volume := by
    refine IntegrableOn.of_bound ?_ ?_ |K| ?_
    · exact measure_Ioc_lt_top
    · exact measurable_const.aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_eq_abs]
  have hF_int : IntervalIntegrable F volume (T-ρ) T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr hFint
  have hK_int : IntervalIntegrable (fun _ : ℝ => K) volume (T-ρ) T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr hKint
  have hmain : ∫ t in (T-ρ)..T, F t ≤ ∫ t in (T-ρ)..T, K :=
    intervalIntegral.integral_mono_on hle hF_int hK_int (fun t ht => by
      rw [hF, hK]
      exact le_trans (le_abs_self _) (ramp_integrand_abs_le hc hρ hz hρT hsmall ht))
  have hKval : ∫ t in (T-ρ)..T, K = 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hK]
    have hdiff : T - (T - ρ) = ρ := by ring
    rw [hdiff]
    field_simp
  calc ∫ t in (T-ρ)..T, F t ≤ ∫ t in (T-ρ)..T, K := hmain
    _ = 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := hKval

end Commons.Analysis.Integral
