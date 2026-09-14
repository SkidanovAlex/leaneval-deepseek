import Mathlib
import Submission.Commons.Analysis.Integral.integrableOn_phiFun_mul_rpow

namespace Commons.Analysis.Integral

open MeasureTheory Set Real
open scoped Topology

/-! ## Definitions -/

private noncomputable def rampK (c z : ℝ) (t : ℝ) : ℝ := c * t ^ ((2:ℝ)/3) * z
private noncomputable def rampM (T ρ : ℝ) (t : ℝ) : ℝ := min ρ (max 0 (T - t))
private noncomputable def rampA (c T ρ z : ℝ) (t : ℝ) : ℝ := rampM T ρ t / rampK c z t
private noncomputable def rampD1 (c z ρ : ℝ) (t : ℝ) : ℝ := -(2/3) * ρ / (c * z) * t ^ (-(5:ℝ)/3)
private noncomputable def rampD2 (c z T : ℝ) (t : ℝ) : ℝ := -((c*z)⁻¹ * t ^ (-(5:ℝ)/3) * ((1/3)*t + (2/3)*T))
private noncomputable def phiFunI (v : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
    ((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1:ℝ)/2) - 1)
private noncomputable def C0 (c z ρ : ℝ) : ℝ := (3/2) * ρ ^ ((1:ℝ)/2) * (c*z) ^ (-(3:ℝ)/2)
private noncomputable def Gv (v : ℝ) : ℝ := |phiFunI v| * v ^ (-(3:ℝ)/2)

/-! ## Measurability of the parametrised circle integral -/

private theorem measurable_phiFunIntegral_aux :
    Measurable (fun v : ℝ => ∫ θ in (0)..(2*Real.pi),
      ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1)) := by
  have h : Measurable (fun p : ℝ × ℝ => (1 + p.1^2 + 2*p.1*Real.cos p.2) ^ (-(1:ℝ)/2) - 1) := by
    fun_prop
  have h2 : StronglyMeasurable (fun p : ℝ × ℝ =>
      (Set.univ ×ˢ Set.Ioc (0:ℝ) (2*Real.pi)).indicator
        (fun q : ℝ × ℝ => ((1 + q.1^2 + 2*q.1*Real.cos q.2) ^ (-(1:ℝ)/2) - 1)) p) :=
    h.stronglyMeasurable.indicator (MeasurableSet.univ.prod measurableSet_Ioc)
  have h3 : StronglyMeasurable (fun v : ℝ => ∫ θ, (Set.univ ×ˢ Set.Ioc (0:ℝ) (2*Real.pi)).indicator
        (fun q : ℝ × ℝ => ((1 + q.1^2 + 2*q.1*Real.cos q.2) ^ (-(1:ℝ)/2) - 1)) (v, θ)) :=
    h2.integral_prod_right'
  have hEq : (fun v : ℝ => ∫ θ in (0)..(2*Real.pi),
      ((1 + v^2 + 2*v*Real.cos θ) ^ (-(1:ℝ)/2) - 1))
      = fun v : ℝ => ∫ θ, (Set.univ ×ˢ Set.Ioc (0:ℝ) (2*Real.pi)).indicator
          (fun q : ℝ × ℝ => ((1 + q.1^2 + 2*q.1*Real.cos q.2) ^ (-(1:ℝ)/2) - 1)) (v, θ) := by
    funext v
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    by_cases hθ : θ ∈ Set.Ioc (0:ℝ) (2*Real.pi)
    · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem (by simpa using hθ)]
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem (by simpa using hθ)]
  rw [hEq]
  exact h3.measurable

private lemma measurable_phiFunI : Measurable phiFunI := by
  unfold phiFunI
  exact measurable_const.mul measurable_phiFunIntegral_aux

/-! ## The ramp function -/

private lemma rampK_pos (c z : ℝ) (hc : 0 < c) (hz : 0 < z) {t : ℝ} (ht : 0 < t) : 0 < rampK c z t := by
  unfold rampK; positivity

private lemma rampM_eq_rho {T ρ t : ℝ} (hρ : 0 < ρ) (ht2 : t < T - ρ) : rampM T ρ t = ρ := by
  unfold rampM; rw [max_eq_right (by linarith), min_eq_left (by linarith)]

private lemma rampM_eq_Tsub {T ρ t : ℝ} (ht1 : T - ρ < t) (ht2 : t < T) : rampM T ρ t = T - t := by
  unfold rampM; rw [max_eq_right (by linarith), min_eq_right (by linarith)]

private lemma rampM_pos {T ρ t : ℝ} (hρ : 0 < ρ) (ht : t < T) : 0 < rampM T ρ t := by
  unfold rampM
  rw [max_eq_right (by linarith)]
  exact lt_min hρ (by linarith)

private lemma rampA_pos {c T ρ z t : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hz : 0 < z)
    (ht1 : 0 < t) (ht2 : t < T) : 0 < rampA c T ρ z t := by
  unfold rampA
  exact div_pos (rampM_pos hρ ht2) (rampK_pos c z hc hz ht1)

private lemma inv_rampK {c z t : ℝ} (hz : 0 < z) (ht : 0 < t) :
    (rampK c z t)⁻¹ = (c*z)⁻¹ * t ^ (-(2:ℝ)/3) := by
  unfold rampK
  rw [mul_inv, mul_inv, ← Real.rpow_neg (le_of_lt ht) (2/3)]
  ring

private lemma rpow_one_third_eq {t : ℝ} (ht : 0 < t) : t ^ ((1:ℝ)/3) = t * t ^ (-(2:ℝ)/3) := by
  have h : t ^ (-(2:ℝ)/3) * t ^ (1:ℝ) = t ^ ((1:ℝ)/3) := by
    rw [← Real.rpow_add ht (-(2:ℝ)/3) (1:ℝ)]; norm_num
  rw [Real.rpow_one] at h
  rw [← h, mul_comm]

private lemma rampA_eq_s1 {c T ρ z t : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z)
    (ht1 : 0 < t) (ht2 : t < T - ρ) :
    rampA c T ρ z t = (ρ/(c*z)) * t ^ (-(2:ℝ)/3) := by
  unfold rampA
  rw [rampM_eq_rho hρ ht2, div_eq_mul_inv, inv_rampK hz ht1]
  ring

private lemma rampA_eq_s2 {c T ρ z t : ℝ} (hc : 0 < c) (hρT : ρ ≤ T) (hz : 0 < z)
    (ht1 : T - ρ < t) (ht2 : t < T) :
    rampA c T ρ z t = (T/(c*z)) * t ^ (-(2:ℝ)/3) - (1/(c*z)) * t ^ ((1:ℝ)/3) := by
  have ht : (0:ℝ) < t := by linarith
  unfold rampA
  rw [rampM_eq_Tsub ht1 ht2, div_eq_mul_inv, inv_rampK hz ht, rpow_one_third_eq ht]
  ring

private lemma rampA_eq_s2div {c T ρ z t : ℝ} (hρT : ρ ≤ T) (ht1 : T - ρ < t) (ht2 : t < T) :
    rampA c T ρ z t = (T - t) / (c * t ^ ((2:ℝ)/3) * z) := by
  unfold rampA rampK
  rw [rampM_eq_Tsub ht1 ht2]

/-! ## Derivatives -/

private lemma hasDerivAt_cf1 (c z ρ : ℝ) (hc : 0 < c) (hz : 0 < z) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (ρ/(c*z)) * s ^ (-(2:ℝ)/3)) (rampD1 c z ρ t) t := by
  have h : HasDerivAt (fun s : ℝ => s ^ (-(2:ℝ)/3)) ((-(2:ℝ)/3) * t ^ (-(2:ℝ)/3 - 1)) t :=
    hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 := h.const_mul (ρ/(c*z))
  refine h2.congr_deriv ?_
  unfold rampD1
  rw [show (-(2:ℝ)/3 - 1 : ℝ) = -(5:ℝ)/3 by norm_num]
  ring

private lemma hasDerivAt_cf2 (c z T : ℝ) (hc : 0 < c) (hz : 0 < z) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (T/(c*z)) * s ^ (-(2:ℝ)/3) - (1/(c*z)) * s ^ ((1:ℝ)/3))
      (rampD2 c z T t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ (-(2:ℝ)/3)) ((-(2:ℝ)/3) * t ^ (-(2:ℝ)/3-1)) t :=
    hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 : HasDerivAt (fun s : ℝ => s ^ ((1:ℝ)/3)) (((1:ℝ)/3) * t ^ ((1:ℝ)/3-1)) t :=
    hasDerivAt_rpow_const (Or.inl ht.ne')
  have h := (h1.const_mul (T/(c*z))).sub (h2.const_mul (1/(c*z)))
  refine h.congr_deriv ?_
  unfold rampD2
  rw [show (-(2:ℝ)/3 - 1 : ℝ) = -(5:ℝ)/3 by norm_num]
  rw [show ((1:ℝ)/3 - 1 : ℝ) = -(2:ℝ)/3 by norm_num]
  field_simp
  have hpow : t ^ (-((5:ℝ)/3)) * t = t ^ (-((2:ℝ)/3)) := by
    have hh : t ^ (-((5:ℝ)/3)) * t ^ (1:ℝ) = t ^ (-((2:ℝ)/3)) := by
      rw [← Real.rpow_add ht (-((5:ℝ)/3)) (1:ℝ)]
      congr 1; norm_num
    simpa [Real.rpow_one] using hh
  rw [mul_add, hpow]; ring

private lemma hasDerivAt_rampA_s1 (c T ρ z : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z)
    {t : ℝ} (ht : t ∈ Ioo 0 (T - ρ)) :
    HasDerivAt (rampA c T ρ z) (rampD1 c z ρ t) t := by
  have hcf := hasDerivAt_cf1 c z ρ hc hz ht.1
  refine hcf.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact rampA_eq_s1 hc hρ hz hs.1 hs.2

private lemma hasDerivAt_rampA_s2 (c T ρ z : ℝ) (hc : 0 < c) (hρT : ρ ≤ T) (hz : 0 < z)
    {t : ℝ} (ht : t ∈ Ioo (T - ρ) T) :
    HasDerivAt (rampA c T ρ z) (rampD2 c z T t) t := by
  have htpos : (0:ℝ) < t := by linarith [ht.1, hρT]
  have hcf := hasDerivAt_cf2 c z T hc hz htpos
  refine hcf.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact rampA_eq_s2 hc hρT hz hs.1 hs.2

/-! ## Strict antitonicity -/

private lemma strictAntiOn_rampA_s1 (c T ρ z : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) :
    StrictAntiOn (rampA c T ρ z) (Ioo 0 (T - ρ)) := by
  intro s1 hs1 s2 hs2 h12
  rw [rampA_eq_s1 hc hρ hz hs1.1 hs1.2, rampA_eq_s1 hc hρ hz hs2.1 hs2.2]
  have hpos : 0 < ρ/(c*z) := by positivity
  have h := Real.rpow_lt_rpow_of_neg hs1.1 h12 (by norm_num : (-(2:ℝ)/3) < 0)
  have := mul_lt_mul_of_pos_left h hpos
  linarith

private lemma strictAntiOn_rampA_s2 (c T ρ z : ℝ) (hc : 0 < c) (hρT : ρ ≤ T) (hz : 0 < z) :
    StrictAntiOn (rampA c T ρ z) (Ioo (T - ρ) T) := by
  intro s1 hs1 s2 hs2 h12
  have hs1pos : 0 < s1 := by linarith [hs1.1, hρT]
  have hs2pos : 0 < s2 := by linarith [hs2.1, hρT]
  rw [rampA_eq_s2div hρT hs1.1 hs1.2, rampA_eq_s2div hρT hs2.1 hs2.2]
  have hden1 : 0 < c * s1 ^ ((2:ℝ)/3) * z := by positivity
  have hle : c * s1 ^ ((2:ℝ)/3) * z < c * s2 ^ ((2:ℝ)/3) * z := by
    have h := Real.rpow_lt_rpow hs1pos.le h12 (by norm_num : (0:ℝ) < (2:ℝ)/3)
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h hc) hz
  have hA : (T - s2) / (c * s2 ^ ((2:ℝ)/3) * z) < (T - s2) / (c * s1 ^ ((2:ℝ)/3) * z) :=
    div_lt_div_of_pos_left (by linarith [hs2.2]) hden1 hle
  have hB : (T - s2) / (c * s1 ^ ((2:ℝ)/3) * z) < (T - s1) / (c * s1 ^ ((2:ℝ)/3) * z) :=
    div_lt_div_of_pos_right (by linarith) hden1
  exact lt_trans hA hB

/-! ## The pointwise bounds -/

private lemma key_s1 {c z ρ t : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) (ht : 0 < t) :
    1 / (c * t ^ ((2:ℝ)/3) * z)
      ≤ (3/2) * ρ ^ ((1:ℝ)/2) * (c*z) ^ (-(3:ℝ)/2)
        * ((2/3) * ρ / (c*z) * t ^ (-(5:ℝ)/3))
        * (((ρ/(c*z)) * t ^ (-(2:ℝ)/3))) ^ (-(3:ℝ)/2) := by
  have hcz : 0 < c*z := mul_pos hc hz
  have hL : (1:ℝ)/(c*t^((2:ℝ)/3)*z) = (c*z)⁻¹ * t^(-(2:ℝ)/3) := by
    rw [one_div, mul_inv, mul_inv, ← Real.rpow_neg (le_of_lt ht) (2/3)]; ring
  have hpow : ((ρ/(c*z)) * t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2)
      = ρ ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) * t := by
    rw [Real.mul_rpow (le_of_lt (div_pos hρ hcz)) (Real.rpow_nonneg ht.le _)]
    rw [Real.div_rpow hρ.le hcz.le]
    rw [show (c*z) ^ (-(3:ℝ)/2) = ((c*z)^((3:ℝ)/2))⁻¹ by
      rw [show (-(3:ℝ)/2) = -((3:ℝ)/2) by norm_num, Real.rpow_neg hcz.le]]
    rw [div_inv_eq_mul]
    rw [show (t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2) = t by
      rw [← Real.rpow_mul ht.le, show (-(2:ℝ)/3) * (-(3:ℝ)/2) = 1 by norm_num, Real.rpow_one]]
  have e1 : ρ ^ ((1:ℝ)/2) * ρ * ρ ^ (-(3:ℝ)/2) = 1 := by
    nth_rewrite 2 [show ρ = ρ ^ (1:ℝ) from (Real.rpow_one ρ).symm]
    rw [← Real.rpow_add hρ (1/2) 1, ← Real.rpow_add hρ ((1:ℝ)/2 + 1) (-(3:ℝ)/2)]
    rw [show ((1:ℝ)/2 + 1 + -(3:ℝ)/2) = 0 by norm_num, Real.rpow_zero]
  have e2 : (c*z) ^ (-(3:ℝ)/2) * (c*z)⁻¹ * (c*z) ^ ((3:ℝ)/2) = (c*z)⁻¹ := by
    have h1 : (c*z) ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) = 1 := by
      rw [← Real.rpow_add hcz (-(3:ℝ)/2) ((3:ℝ)/2)]
      rw [show (-(3:ℝ)/2 + (3:ℝ)/2) = 0 by norm_num, Real.rpow_zero]
    rw [mul_assoc, mul_comm ((c*z)⁻¹) ((c*z)^((3:ℝ)/2)), ← mul_assoc, h1, one_mul]
  have e3 : t ^ (-(5:ℝ)/3) * t = t ^ (-(2:ℝ)/3) := by
    rw [← Real.rpow_add_one ht.ne' (-(5:ℝ)/3)]; norm_num
  have hR : (3/2) * ρ ^ ((1:ℝ)/2) * (c*z) ^ (-(3:ℝ)/2)
        * ((2/3) * ρ / (c*z) * t ^ (-(5:ℝ)/3))
        * (ρ ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) * t) = (c*z)⁻¹ * t ^ (-(2:ℝ)/3) := by
    rw [div_eq_mul_inv]
    calc (3/2) * ρ ^ ((1:ℝ)/2) * (c*z) ^ (-(3:ℝ)/2)
        * ((2/3) * ρ * (c*z)⁻¹ * t ^ (-(5:ℝ)/3))
        * (ρ ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) * t)
        = (3/2)*(2/3) * (ρ ^ ((1:ℝ)/2) * ρ * ρ ^ (-(3:ℝ)/2))
            * ((c*z) ^ (-(3:ℝ)/2) * (c*z)⁻¹ * (c*z) ^ ((3:ℝ)/2))
            * (t ^ (-(5:ℝ)/3) * t) := by ring
      _ = (c*z)⁻¹ * t ^ (-(2:ℝ)/3) := by rw [e1, e2, e3]; ring
  rw [hL, hpow, hR]

private lemma key_s2 {c z ρ T t : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) (hρT : ρ ≤ T)
    (ht1 : T - ρ < t) (ht2 : t < T) :
    1 / (c * t ^ ((2:ℝ)/3) * z)
      ≤ (3/2) * ρ ^ ((1:ℝ)/2) * (c*z) ^ (-(3:ℝ)/2)
        * ((c*z)⁻¹ * t ^ (-(5:ℝ)/3) * ((1/3)*t + (2/3)*T))
        * (((T/(c*z)) * t ^ (-(2:ℝ)/3) - (1/(c*z)) * t ^ ((1:ℝ)/3))) ^ (-(3:ℝ)/2) := by
  have ht : (0:ℝ) < t := by linarith
  have hcz : 0 < c*z := mul_pos hc hz
  have hTt : (0:ℝ) < T - t := by linarith
  have hinv : (c*z)⁻¹ * t ^ (-(2:ℝ)/3) = (c*t^((2:ℝ)/3)*z)⁻¹ := by
    rw [show t^(-(2:ℝ)/3) = (t^((2:ℝ)/3))⁻¹ by
      rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by norm_num, Real.rpow_neg ht.le]]
    rw [← mul_inv]
    congr 1
    ring
  have hL : (1:ℝ)/(c*t^((2:ℝ)/3)*z) = (c*z)⁻¹ * t^(-(2:ℝ)/3) := by
    rw [one_div, ← hinv]
  have hAeq : (T/(c*z)) * t ^ (-(2:ℝ)/3) - (1/(c*z)) * t ^ ((1:ℝ)/3)
      = (T - t) * (c*z)⁻¹ * t ^ (-(2:ℝ)/3) := by
    rw [div_eq_mul_inv, one_div, rpow_one_third_eq ht]
    ring
  have hApow : ((T - t) * (c*z)⁻¹ * t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2)
      = (T-t) ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) * t := by
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (T-t) * (c*z)⁻¹) (Real.rpow_nonneg ht.le _)]
    rw [Real.mul_rpow hTt.le (by positivity : (0:ℝ) ≤ (c*z)⁻¹)]
    rw [Real.inv_rpow hcz.le]
    rw [show (c*z) ^ (-(3:ℝ)/2) = ((c*z) ^ ((3:ℝ)/2))⁻¹ by
      rw [show (-(3:ℝ)/2) = -((3:ℝ)/2) by norm_num, Real.rpow_neg hcz.le]]
    rw [inv_inv]
    rw [show (t ^ (-(2:ℝ)/3)) ^ (-(3:ℝ)/2) = t by
      rw [← Real.rpow_mul ht.le, show (-(2:ℝ)/3) * (-(3:ℝ)/2) = 1 by norm_num, Real.rpow_one]]
  have e2 : (c*z) ^ (-(3:ℝ)/2) * (c*z)⁻¹ * (c*z) ^ ((3:ℝ)/2) = (c*z)⁻¹ := by
    have h1 : (c*z) ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) = 1 := by
      rw [← Real.rpow_add hcz (-(3:ℝ)/2) ((3:ℝ)/2)]
      rw [show (-(3:ℝ)/2 + (3:ℝ)/2) = 0 by norm_num, Real.rpow_zero]
    rw [mul_assoc, mul_comm ((c*z)⁻¹) ((c*z)^((3:ℝ)/2)), ← mul_assoc, h1, one_mul]
  have e3 : t ^ (-(5:ℝ)/3) * t = t ^ (-(2:ℝ)/3) := by
    rw [← Real.rpow_add_one ht.ne' (-(5:ℝ)/3)]; norm_num
  have hK : 1 ≤ (3/2) * ρ ^ ((1:ℝ)/2) * ((1/3)*t + (2/3)*T) * (T-t) ^ (-(3:ℝ)/2) := by
    have h6 : (T-t) ^ (-(3:ℝ)/2) = ((T-t)^((3:ℝ)/2))⁻¹ := by
      rw [show (-(3:ℝ)/2) = -((3:ℝ)/2) by norm_num, Real.rpow_neg hTt.le]
    have hb : 0 < (T-t) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hTt _
    rw [h6, ← div_eq_mul_inv, show (3/2) * ρ ^ ((1:ℝ)/2) * ((1/3)*t + (2/3)*T)
        = ρ ^ ((1:ℝ)/2) * ((1/2)*(t + 2*T)) by ring, le_div_iff₀ hb, one_mul]
    calc (T-t) ^ ((3:ℝ)/2) ≤ ρ ^ ((3:ℝ)/2) :=
          Real.rpow_le_rpow hTt.le (by linarith) (by norm_num)
      _ = ρ ^ ((1:ℝ)/2) * ρ := by
          rw [show (3:ℝ)/2 = (1:ℝ)/2 + 1 by norm_num, Real.rpow_add hρ, Real.rpow_one]
      _ ≤ ρ ^ ((1:ℝ)/2) * ((1/2)*(t + 2*T)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hρ.le _)
  have hR : (3/2) * ρ ^ ((1:ℝ)/2) * (c*z) ^ (-(3:ℝ)/2)
        * ((c*z)⁻¹ * t ^ (-(5:ℝ)/3) * ((1/3)*t + (2/3)*T))
        * ((T-t) ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) * t)
      = (c*z)⁻¹ * t ^ (-(2:ℝ)/3)
        * ((3/2) * ρ ^ ((1:ℝ)/2) * ((1/3)*t + (2/3)*T) * (T-t) ^ (-(3:ℝ)/2)) := by
    calc (3/2) * ρ ^ ((1:ℝ)/2) * (c*z) ^ (-(3:ℝ)/2)
        * ((c*z)⁻¹ * t ^ (-(5:ℝ)/3) * ((1/3)*t + (2/3)*T))
        * ((T-t) ^ (-(3:ℝ)/2) * (c*z) ^ ((3:ℝ)/2) * t)
        = ((c*z) ^ (-(3:ℝ)/2) * (c*z)⁻¹ * (c*z) ^ ((3:ℝ)/2)) * (t ^ (-(5:ℝ)/3) * t)
            * ((3/2) * ρ ^ ((1:ℝ)/2) * ((1/3)*t + (2/3)*T) * (T-t) ^ (-(3:ℝ)/2)) := by ring
      _ = (c*z)⁻¹ * t ^ (-(2:ℝ)/3)
            * ((3/2) * ρ ^ ((1:ℝ)/2) * ((1/3)*t + (2/3)*T) * (T-t) ^ (-(3:ℝ)/2)) := by
          rw [e2, e3]
  rw [hL, hAeq, hApow, hR]
  exact le_mul_of_one_le_right (by positivity) hK

/-! ## Wrappers in terms of `rampA`, `rampD1`, `rampD2` -/

private lemma rampD1_abs {c z ρ t : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) (ht : 0 < t) :
    |rampD1 c z ρ t| = (2/3) * ρ / (c*z) * t ^ (-(5:ℝ)/3) := by
  have h : rampD1 c z ρ t = -((2/3) * ρ / (c*z) * t ^ (-(5:ℝ)/3)) := by
    unfold rampD1; ring
  rw [h, abs_neg, abs_of_nonneg (by positivity)]

private lemma key_s1' (c T ρ z : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z)
    {t : ℝ} (ht1 : 0 < t) (ht2 : t < T - ρ) :
    1 / rampK c z t ≤ C0 c z ρ * |rampD1 c z ρ t| * (rampA c T ρ z t) ^ (-(3:ℝ)/2) := by
  have h := key_s1 (c:=c) (z:=z) (ρ:=ρ) (t:=t) hc hρ hz ht1
  rw [rampA_eq_s1 hc hρ hz ht1 ht2, rampD1_abs hc hρ hz ht1, C0, rampK] at *
  exact h

private lemma key_s2' (c T ρ z : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hz : 0 < z) (hρT : ρ ≤ T)
    {t : ℝ} (ht1 : T - ρ < t) (ht2 : t < T) :
    1 / rampK c z t ≤ C0 c z ρ * |rampD2 c z T t| * (rampA c T ρ z t) ^ (-(3:ℝ)/2) := by
  have ht : (0:ℝ) < t := by linarith
  have h := key_s2 (c:=c) (z:=z) (ρ:=ρ) (T:=T) (t:=t) hc hρ hz hρT ht1 ht2
  have ha : |rampD2 c z T t| = (c*z)⁻¹ * t ^ (-(5:ℝ)/3) * ((1/3)*t + (2/3)*T) := by
    have hh : rampD2 c z T t = -((c*z)⁻¹ * t ^ (-(5:ℝ)/3) * ((1/3)*t + (2/3)*T)) := by
      unfold rampD2; ring
    have h3 : (0:ℝ) < (1/3)*t + (2/3)*T := by nlinarith [ht, hρ, hρT]
    have hpos : 0 ≤ (c*z)⁻¹ * t ^ (-(5:ℝ)/3) * ((1/3)*t + (2/3)*T) := by positivity
    rw [hh, abs_neg]
    exact abs_of_nonneg hpos
  rw [rampA_eq_s2 hc hρT hz ht1 ht2, ha, C0, rampK] at *
  exact h


theorem integrableOn_phiFun_stdVarRamp_integrand {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hρ : 0 < ρ) (hρT : ρ ≤ T) (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (1 / (c * t ^ ((2:ℝ)/3) * z)) *
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
          (((1 + (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) ^ 2
              + 2 * (min ρ (max 0 (T - t)) / (c * t ^ ((2:ℝ)/3) * z)) * Real.cos theta)
              ^ (-(1:ℝ)/2)) - 1)))
      (Set.Ioc 0 T) := by
  change MeasureTheory.IntegrableOn
    (fun t : ℝ => (1 / rampK c z t) * phiFunI (rampA c T ρ z t)) (Set.Ioc 0 T)
  -- integrability of Gv on (0,∞)
  have hGint : MeasureTheory.IntegrableOn Gv (Ioi 0) := by
    have h2 : MeasureTheory.IntegrableOn (fun v : ℝ => |phiFunI v * v ^ (-(3:ℝ)/2)|) (Ioi 0) := by
      have h := integrableOn_phiFun_mul_rpow
      exact h.abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro v hv
    show |phiFunI v * v ^ (-(3:ℝ)/2)| = Gv v
    unfold Gv
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hv) _)]
  -- change of variables on the two pieces
  have hcv1 : MeasureTheory.IntegrableOn
      (fun t : ℝ => |rampD1 c z ρ t| * Gv (rampA c T ρ z t)) (Ioo 0 (T - ρ)) := by
    have hsub : rampA c T ρ z '' (Ioo 0 (T - ρ)) ⊆ Ioi 0 := by
      rintro v ⟨s, hs, rfl⟩
      exact rampA_pos hρ hc hz hs.1 (lt_of_lt_of_le hs.2 (by linarith))
    have key := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioo
      (fun x hx => (hasDerivAt_rampA_s1 c T ρ z hc hρ hz hx).hasDerivWithinAt)
      (strictAntiOn_rampA_s1 c T ρ z hc hρ hz).injOn Gv).mp (hGint.mono_set hsub)
    simpa only [smul_eq_mul] using key
  have hcv2 : MeasureTheory.IntegrableOn
      (fun t : ℝ => |rampD2 c z T t| * Gv (rampA c T ρ z t)) (Ioo (T - ρ) T) := by
    have hsub : rampA c T ρ z '' (Ioo (T - ρ) T) ⊆ Ioi 0 := by
      rintro v ⟨s, hs, rfl⟩
      exact rampA_pos hρ hc hz (by linarith [hs.1, hρT]) hs.2
    have key := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioo
      (fun x hx => (hasDerivAt_rampA_s2 c T ρ z hc hρT hz hx).hasDerivWithinAt)
      (strictAntiOn_rampA_s2 c T ρ z hc hρT hz).injOn Gv).mp (hGint.mono_set hsub)
    simpa only [smul_eq_mul] using key
  -- measurability
  have hfmeas : Measurable
      (fun t : ℝ => (1 / rampK c z t) * phiFunI (rampA c T ρ z t)) := by
    have hA : Measurable (rampA c T ρ z) := by unfold rampA rampM rampK; fun_prop
    have hK : Measurable (fun t : ℝ => (1:ℝ) / rampK c z t) := by
      have h : Measurable (rampK c z) := by unfold rampK; fun_prop
      have h' : Measurable (fun t : ℝ => (rampK c z t)⁻¹) := h.inv
      simpa only [one_div] using h' 
    exact hK.mul (measurable_phiFunI.comp hA)
  -- domination on piece 1
  have hint1 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (1 / rampK c z t) * phiFunI (rampA c T ρ z t)) (Ioo 0 (T - ρ)) := by
    refine Integrable.mono' (Integrable.const_mul hcv1 (C0 c z ρ))
      hfmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hb := key_s1' (c:=c) (T:=T) (ρ:=ρ) (z:=z) hc hρ hz ht.1 ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (one_div_pos.mpr (rampK_pos c z hc hz ht.1))]
    unfold Gv
    calc (1 / rampK c z t) * |phiFunI (rampA c T ρ z t)|
        ≤ (C0 c z ρ * |rampD1 c z ρ t| * (rampA c T ρ z t) ^ (-(3:ℝ)/2))
            * |phiFunI (rampA c T ρ z t)| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = C0 c z ρ * (|rampD1 c z ρ t|
            * (|phiFunI (rampA c T ρ z t)| * (rampA c T ρ z t) ^ (-(3:ℝ)/2))) := by ring
  have hint2 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (1 / rampK c z t) * phiFunI (rampA c T ρ z t)) (Ioo (T - ρ) T) := by
    refine Integrable.mono' (Integrable.const_mul hcv2 (C0 c z ρ))
      hfmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hb := key_s2' (c:=c) (T:=T) (ρ:=ρ) (z:=z) hc hρ hz hρT ht.1 ht.2
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_pos (one_div_pos.mpr (rampK_pos c z hc hz (by linarith [ht.1, hρT])))]
    unfold Gv
    calc (1 / rampK c z t) * |phiFunI (rampA c T ρ z t)|
        ≤ (C0 c z ρ * |rampD2 c z T t| * (rampA c T ρ z t) ^ (-(3:ℝ)/2))
            * |phiFunI (rampA c T ρ z t)| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = C0 c z ρ * (|rampD2 c z T t|
            * (|phiFunI (rampA c T ρ z t)| * (rampA c T ρ z t) ^ (-(3:ℝ)/2))) := by ring
  have hunion := hint1.union hint2
  -- null set bookkeeping
  have hnull : volume ({T - ρ, T} : Set ℝ) = 0 := by
    rw [Set.insert_eq]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton _)
      (MeasureTheory.measure_singleton _)
  have hae : Ioc (0:ℝ) T =ᵐ[volume] (Set.Ioo 0 (T - ρ) ∪ Set.Ioo (T - ρ) T : Set ℝ) := by
    refine MeasureTheory.ae_eq_set.mpr ?_
    constructor
    · refine MeasureTheory.measure_mono_null ?_ hnull
      rintro x hx
      rw [Set.mem_diff, Set.mem_Ioc, Set.mem_union, Set.mem_Ioo, Set.mem_Ioo, not_or] at hx
      obtain ⟨⟨hx0, hxTle⟩, hnotA, hnotB⟩ := hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases lt_trichotomy x (T - ρ) with h | h | h
      · exact absurd ⟨hx0, h⟩ hnotA
      · exact Or.inl h
      · rcases lt_trichotomy x T with h2 | h2 | h2
        · exact absurd ⟨h, h2⟩ hnotB
        · exact Or.inr h2
        · exact absurd h2 (not_lt.mpr hxTle)
    · have hempty : (Ioo (0:ℝ) (T - ρ) ∪ Ioo (T - ρ) T) \ Ioc 0 T = ∅ := by
        rw [Set.diff_eq_empty]
        rintro x (hx | hx)
        · exact ⟨hx.1, le_of_lt (lt_of_lt_of_le hx.2 (by linarith))⟩
        · exact ⟨by linarith [hx.1, hρT], le_of_lt hx.2⟩
      rw [hempty, MeasureTheory.measure_empty]
  exact hunion.congr_set_ae hae

end Commons.Analysis.Integral
