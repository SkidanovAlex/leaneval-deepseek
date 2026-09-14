import Mathlib
import Submission.Commons.Analysis.Integral.phiFun_nonneg_of_le_eighth
import Submission.Commons.Analysis.Integral.abs_phiFun_le_six_mul
import Submission.Commons.Analysis.Integral.integral_phi_rpow_neg_three_halves_neg
import Submission.Commons.Analysis.Integral.phiFun_v_neg_three_halves_tail_le
import Submission.Commons.Analysis.Integral.integral_phiFun_ramp_decreasing_le
import Submission.Commons.Analysis.Integral.measurable_phiFun_kernel
import Submission.Commons.Analysis.Integral.integrableOn_phiFun_stdVarRamp_integrand
import Submission.Commons.Analysis.Integral.integral_Ioo_subst_rpow_neg_two_thirds

open MeasureTheory Set intervalIntegral

namespace Commons.Analysis.Integral

/-- The circle-average transfer kernel `phiFun v = (1/(2π)) ∫_θ ((1+v²+2v cos θ)^{-1/2} - 1) dθ`. -/
private noncomputable def phiKern (v : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
    (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1:ℝ)/2)) - 1)

private lemma min_max_eq_rho {T ρ t : ℝ} (hρ : 0 ≤ ρ)
    (ht : t ∈ Icc 0 (T - ρ)) : min ρ (max 0 (T - t)) = ρ := by
  rw [max_eq_right (by linarith [ht.2] : (0:ℝ) ≤ T - t),
      min_eq_left (by linarith [ht.2] : ρ ≤ T - t)]

private lemma min_max_eq_sub {T ρ t : ℝ} (ht : t ∈ Icc (T - ρ) T) :
    min ρ (max 0 (T - t)) = T - t := by
  rw [max_eq_right (by linarith [ht.2] : (0:ℝ) ≤ T - t),
      min_eq_right (by linarith [ht.1] : T - t ≤ ρ)]

private lemma Ioc_ae_eq_Ioo (a b : ℝ) : Set.Ioc a b =ᵐ[volume] Set.Ioo a b := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton b)
    intro x hx
    rw [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo] at hx
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hx.2 ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hne⟩
  · have h : Set.Ioo a b \ Set.Ioc a b = ∅ := by
      rw [Set.sdiff_eq_empty]
      intro x hx
      rw [Set.mem_Ioo] at hx
      rw [Set.mem_Ioc]
      exact ⟨hx.1, hx.2.le⟩
    rw [h, MeasureTheory.measure_empty]

private lemma rpow_neg_three_halves_mul {c z : ℝ} (hc : 0 < c) (hz : 0 < z) :
    (c * z) ^ (-((3:ℝ)/2)) = c ^ (-((3:ℝ)/2)) * z ^ (-((3:ℝ)/2)) := by
  have hcz : (0:ℝ) ≤ c * z := (mul_pos hc hz).le
  rw [Real.rpow_neg hcz (3/2), Real.mul_rpow hc.le hz.le, mul_inv,
      ← Real.rpow_neg hc.le (3/2), ← Real.rpow_neg hz.le (3/2)]

private lemma rpow_neg_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(2:ℝ)/3) = (x ^ ((2:ℝ)/3))⁻¹ := by
  rw [show ((-(2:ℝ))/3 : ℝ) = -((2:ℝ)/3) by norm_num, Real.rpow_neg hx]

private lemma C1_eq {c ρ z : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) :
    (3/2) * (ρ / (c * z)) ^ ((1:ℝ)/2) / (c * z)
      = (3/2) * ρ ^ ((1:ℝ)/2) * c ^ (-(3:ℝ)/2) * z ^ (-(3:ℝ)/2) := by
  rw [show ((-(3:ℝ))/2 : ℝ) = -((3:ℝ)/2) by norm_num]
  have hcz : (0:ℝ) < c * z := mul_pos hc hz
  have key : ((c * z) ^ ((1:ℝ)/2))⁻¹ * (c * z)⁻¹ = (c * z) ^ (-((3:ℝ)/2)) := by
    rw [← Real.rpow_neg hcz.le (1/2), ← Real.rpow_neg_one, ← Real.rpow_add hcz]
    norm_num
  have h1 : (ρ / (c * z)) ^ ((1:ℝ)/2) = ρ ^ ((1:ℝ)/2) * ((c*z) ^ ((1:ℝ)/2))⁻¹ := by
    rw [Real.div_rpow hρ.le hcz.le, div_eq_mul_inv]
  have h2 : (3/2) * (ρ ^ ((1:ℝ)/2) * ((c * z) ^ ((1:ℝ)/2))⁻¹) / (c * z)
      = (3/2) * ρ ^ ((1:ℝ)/2) * (((c*z)^((1:ℝ)/2))⁻¹ * (c*z)⁻¹) := by ring
  rw [h1, h2, key, rpow_neg_three_halves_mul hc hz]
  ring

theorem integral_phiFun_stdVarRamp_realpow_le {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ)
    (hρT : ρ < T) (hz : 0 < z)
    (hsmall : ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) ≤ 1/8) :
    ∫ t in (0:ℝ)..T, (1 / (c * t ^ ((2:ℝ)/3) * z)) *
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
          (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
            + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos theta)
            ^ (-(1:ℝ)/2)) - 1))
      ≤ (3/2) * ρ ^ ((1:ℝ)/2) * c ^ (-(3:ℝ)/2) * z ^ (-(3:ℝ)/2)
          * (∫ v in Set.Ioi (0:ℝ),
              ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
                (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1))
                * v ^ (-(3 : ℝ) / 2))
        + 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2) := by
  have hcz : (0:ℝ) < c * z := mul_pos hc hz
  have hTρ : (0:ℝ) < T - ρ := by linarith
  let F : ℝ → ℝ := fun t => (1 / (c * t ^ ((2:ℝ)/3) * z)) *
      phiKern (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z))
  let G1 : ℝ → ℝ := fun t => (1 / (c * t ^ ((2:ℝ)/3) * z)) *
      phiKern (ρ / (c * t ^ ((2:ℝ)/3) * z))
  let G2 : ℝ → ℝ := fun t => (1 / (c * t ^ ((2:ℝ)/3) * z)) *
      phiKern ((T - t) / (c * t ^ ((2:ℝ)/3) * z))
  let W : ℝ := ∫ v in Set.Ioi (0:ℝ), phiKern v * v ^ (-(3:ℝ)/2)
  let C1 : ℝ := (3/2) * ρ ^ ((1:ℝ)/2) * c ^ (-(3:ℝ)/2) * z ^ (-(3:ℝ)/2)
  let C2 : ℝ := 6 * ρ ^ 2 / (c ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * z ^ 2)
  change ∫ t in (0:ℝ)..T, F t ≤ C1 * W + C2
  have hInt : IntegrableOn F (Set.Ioc 0 T) :=
    integrableOn_phiFun_stdVarRamp_integrand hc hT hρ hρT.le hz
  have hI1 : IntervalIntegrable F volume 0 (T - ρ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hTρ.le).mpr
      (hInt.mono_set (fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 (by linarith))⟩))
  have hI2 : IntervalIntegrable F volume (T - ρ) T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : T - ρ ≤ T)).mpr
      (hInt.mono_set (fun x hx => ⟨lt_trans hTρ hx.1, hx.2⟩))
  have hsplit : ∫ t in (0:ℝ)..T, F t
      = (∫ t in (0:ℝ)..(T-ρ), F t) + (∫ t in (T-ρ)..T, F t) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hp1 : ∫ t in (0:ℝ)..(T-ρ), F t = ∫ t in (0:ℝ)..(T-ρ), G1 t := by
    rw [intervalIntegral.integral_of_le hTρ.le, intervalIntegral.integral_of_le hTρ.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [F, G1]
    rw [min_max_eq_rho hρ.le ⟨ht.1.le, ht.2⟩]
  have hp2 : ∫ t in (T-ρ)..T, F t = ∫ t in (T-ρ)..T, G2 t := by
    rw [intervalIntegral.integral_of_le (by linarith : T - ρ ≤ T),
        intervalIntegral.integral_of_le (by linarith : T - ρ ≤ T)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [F, G2]
    rw [min_max_eq_sub ⟨le_of_lt ht.1, ht.2⟩]
  have hbound2 : ∫ t in (T-ρ)..T, G2 t ≤ C2 :=
    integral_phiFun_ramp_decreasing_le hc hρ hz hρT hsmall
  have hC1pos : 0 ≤ C1 := by
    simp only [C1]; positivity
  have hv1pos : 0 < ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) := by positivity
  have htail : ∫ v in Set.Ioi (ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z)), phiKern v * v ^ (-(3:ℝ)/2)
      ≤ W := phiFun_v_neg_three_halves_tail_le hv1pos hsmall
  have hsub : ∫ t in Set.Ioo (0:ℝ) (T-ρ), G1 t
      = C1 * ∫ v in Set.Ioi (ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z)), phiKern v * v ^ (-(3:ℝ)/2) := by
    have hk : (0:ℝ) < ρ / (c * z) := by positivity
    have hpoint : Set.EqOn
        (fun t : ℝ => (1 / (c * t ^ ((2:ℝ)/3) * z)) * phiKern ((ρ/(c*z)) * t ^ (-(2:ℝ)/3)))
        G1 (Set.Ioo 0 (T-ρ)) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht.1
      simp only [G1]
      congr 1
      rw [rpow_neg_two_thirds (le_of_lt ht0)]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    have hv1 : (ρ/(c*z)) * (T-ρ) ^ (-(2:ℝ)/3) = ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) := by
      rw [rpow_neg_two_thirds (le_of_lt hTρ)]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [← setIntegral_congr_fun measurableSet_Ioo hpoint]
    rw [integral_Ioo_subst_rpow_neg_two_thirds hc hz hk hTρ phiKern, C1_eq hc hρ hz, hv1]
  have hbound1 : ∫ t in (0:ℝ)..(T-ρ), G1 t ≤ C1 * W := by
    rw [intervalIntegral.integral_of_le hTρ.le, setIntegral_congr_set (Ioc_ae_eq_Ioo 0 (T-ρ)), hsub]
    exact mul_le_mul_of_nonneg_left htail hC1pos
  calc ∫ t in (0:ℝ)..T, F t
      = (∫ t in (0:ℝ)..(T-ρ), F t) + (∫ t in (T-ρ)..T, F t) := hsplit
    _ = (∫ t in (0:ℝ)..(T-ρ), G1 t) + (∫ t in (T-ρ)..T, F t) := by rw [hp1]
    _ = (∫ t in (0:ℝ)..(T-ρ), G1 t) + (∫ t in (T-ρ)..T, G2 t) := by rw [hp2]
    _ ≤ C1 * W + C2 := add_le_add hbound1 hbound2

end Commons.Analysis.Integral
