import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Complex

open MeasureTheory Set Real Filter
open scoped Topology

noncomputable section

private def psiR (t : ℝ) : ℝ := (Real.log t)⁻¹ + ((Real.log t)^2)⁻¹
private def psiD (t : ℝ) : ℝ := -(1/(t*(Real.log t)^2) + 2/(t*(Real.log t)^3))
private def PP (t : ℝ) : ℂ := Complex.ofReal ((Real.log t)⁻¹) + Complex.ofReal (((Real.log t)^2)⁻¹)
private def FF (z : ℂ) (t : ℝ) : ℂ := (t:ℂ)^(z-2) * PP t
private def GG (z : ℂ) (t : ℝ) : ℂ := (t:ℂ)^(z-1) / (z-1)
private def HH (z : ℂ) (t : ℝ) : ℂ := GG z t * PP t
private def RR (z : ℂ) (t : ℝ) : ℂ := GG z t * ((psiD t : ℝ) : ℂ)

private lemma PP_eq (t : ℝ) : PP t = ((psiR t : ℝ) : ℂ) := by
  simp only [PP, psiR, Complex.ofReal_add]

private lemma psiR_pos {t : ℝ} (ht : 1 < t) : 0 < psiR t := by
  have h : 0 < Real.log t := Real.log_pos ht
  simp only [psiR]; positivity

private lemma norm_PP {t : ℝ} (ht : 1 < t) : ‖PP t‖ = psiR t := by
  rw [PP_eq]
  have h : ‖((psiR t : ℝ) : ℂ)‖ = |psiR t| := by simp
  rw [h, abs_of_pos (psiR_pos ht)]

private lemma psiR_anti {t : ℝ} (ht : 2 ≤ t) : psiR t ≤ psiR 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hle : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  simp only [psiR]
  exact add_le_add (inv_anti₀ hlog2 hle)
    (inv_anti₀ (pow_pos hlog2 2) (pow_le_pow_left₀ hlog2.le hle 2))

private lemma hasDerivAt_psiR {t : ℝ} (ht : 2 ≤ t) : HasDerivAt psiR (psiD t) t := by
  change HasDerivAt (fun s : ℝ => (Real.log s)⁻¹ + ((Real.log s)^2)⁻¹)
      (-(1/(t*(Real.log t)^2) + 2/(t*(Real.log t)^3))) t
  have ht0 : t ≠ 0 := by positivity
  have ht1 : (1:ℝ) < t := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  have hA : HasDerivAt (fun s : ℝ => (Real.log s)⁻¹) (-t⁻¹ / (Real.log t)^2) t :=
    Real.hasDerivAt_inv_log ht0 (by linarith) (by linarith)
  have hsq : HasDerivAt (fun s : ℝ => (Real.log s)^2) (2 * Real.log t * t⁻¹) t := by
    have h := (Real.hasDerivAt_log ht0).pow 2
    have h' : HasDerivAt ((fun s : ℝ => Real.log s) ^ 2)
        (2 * (Real.log t) ^ (2 - 1) * t⁻¹) t := h
    rw [show (fun s : ℝ => Real.log s) ^ 2 = fun s : ℝ => (Real.log s)^2 from rfl] at h'
    convert h' using 1
    ring
  have hB : HasDerivAt (fun s : ℝ => ((Real.log s)^2)⁻¹)
      (-(2 * Real.log t * t⁻¹)/((Real.log t)^2)^2) t := hsq.inv (pow_ne_zero 2 hlog)
  have hsum := hA.add hB
  refine hsum.congr_deriv ?_
  field_simp; ring

private lemma hasDerivAt_PP {t : ℝ} (ht : 2 ≤ t) : HasDerivAt PP ((psiD t : ℝ) : ℂ) t := by
  have h := (hasDerivAt_psiR ht).ofReal_comp
  refine h.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall (fun s => by simp only [PP, psiR, Complex.ofReal_add])

private lemma hasDerivAt_GG {z : ℂ} (hz1 : z ≠ 1) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (GG z) ((t:ℂ)^(z-2)) t := by
  have hmem : (t:ℂ) ∈ Complex.slitPlane := by rw [Complex.ofReal_mem_slitPlane]; exact ht
  have h1 : HasDerivAt (fun s : ℝ => (s:ℂ)) (1:ℂ) t := by
    simpa using (hasDerivAt_id (t:ℝ)).ofReal_comp
  have h2 := (Complex.hasStrictDerivAt_cpow_const (c := z-1) hmem).hasDerivAt.comp t h1
  have h3 : HasDerivAt (fun y : ℝ => (y:ℂ)^(z-1)/(z-1))
      (((z-1)*(t:ℂ)^((z-1)-1)*1)/(z-1)) t := h2.div_const (z-1)
  have hder : ((z-1)*(t:ℂ)^((z-1)-1)*1)/(z-1) = (t:ℂ)^(z-2) := by
    rw [show (z-1:ℂ)-1 = z-2 by ring]; field_simp
  rw [hder] at h3
  have : GG z = fun y : ℝ => (y:ℂ)^(z-1)/(z-1) := rfl
  rw [this]; exact h3

private lemma hasDerivAt_HH {z : ℂ} (hz1 : z ≠ 1) {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (HH z) (FF z t + RR z t) t := by
  have ht0 : 0 < t := by linarith
  have h := (hasDerivAt_GG hz1 ht0).mul (hasDerivAt_PP ht)
  change HasDerivAt (fun s : ℝ => GG z s * PP s)
    ((t:ℂ)^(z-2) * PP t + GG z t * ((psiD t : ℝ):ℂ)) t
  exact h

private lemma continuousAt_PP {t : ℝ} (ht : 1 < t) : ContinuousAt PP t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hc : ContinuousAt (fun s : ℝ => Real.log s) t := Real.continuousAt_log ht0
  have h1 : ContinuousAt (fun s : ℝ => (Real.log s)⁻¹) t := hc.inv₀ hlog
  have h2 : ContinuousAt (fun s : ℝ => ((Real.log s)^2)⁻¹) t := (hc.pow 2).inv₀ (pow_ne_zero 2 hlog)
  have e1 : ContinuousAt (fun s : ℝ => Complex.ofReal ((Real.log s)⁻¹)) t :=
    Complex.continuous_ofReal.continuousAt.comp h1
  have e2 : ContinuousAt (fun s : ℝ => Complex.ofReal (((Real.log s)^2)⁻¹)) t :=
    Complex.continuous_ofReal.continuousAt.comp h2
  have h := e1.add e2
  change ContinuousAt (fun s : ℝ => Complex.ofReal ((Real.log s)⁻¹)
    + Complex.ofReal (((Real.log s)^2)⁻¹)) t
  exact h

private lemma continuousAt_psiD {t : ℝ} (ht : 1 < t) : ContinuousAt psiD t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have htpos : 0 < t := by linarith
  have hc : ContinuousAt (fun s : ℝ => Real.log s) t := Real.continuousAt_log ht0
  have ha : ContinuousAt (fun s : ℝ => 1/(s*(Real.log s)^2)) t := by
    have hden : ContinuousAt (fun s : ℝ => s*(Real.log s)^2) t :=
      continuousAt_id.mul (hc.pow 2)
    exact continuousAt_const.div hden (by positivity)
  have hb : ContinuousAt (fun s : ℝ => 2/(s*(Real.log s)^3)) t := by
    have hden : ContinuousAt (fun s : ℝ => s*(Real.log s)^3) t :=
      continuousAt_id.mul (hc.pow 3)
    exact continuousAt_const.div hden (by positivity)
  have h := (ha.add hb).neg
  change ContinuousAt (fun s : ℝ => -(1/(s*(Real.log s)^2) + 2/(s*(Real.log s)^3))) t
  exact h

private lemma continuousAt_cpow_ofReal {w : ℂ} {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => (s:ℂ)^w) t := by
  have hmem : (t:ℂ) ∈ Complex.slitPlane := by rw [Complex.ofReal_mem_slitPlane]; exact ht
  exact Complex.continuous_ofReal.continuousAt.cpow continuousAt_const hmem

private lemma norm_GG {z : ℂ} {t : ℝ} (ht : 0 < t) : ‖GG z t‖ = t ^ ((z-1).re) / ‖z-1‖ := by
  rw [GG, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht]

private lemma norm_RR {z : ℂ} (hz : z.re = 1/2) {t : ℝ} (ht : 0 < t) :
    ‖RR z t‖ = t ^ (-(1/2):ℝ) / ‖z-1‖ * |psiD t| := by
  rw [RR, norm_mul, norm_GG ht,
    show (z-1).re = -(1/2:ℝ) by rw [Complex.sub_re, Complex.one_re, hz]; norm_num]
  have : ‖(((psiD t : ℝ)) : ℂ)‖ = |psiD t| := by simp
  rw [this]

private lemma abs_psiD {t : ℝ} (ht : 1 < t) :
    |psiD t| = 1/(t*(Real.log t)^2) + 2/(t*(Real.log t)^3) := by
  have hlog : 0 < Real.log t := Real.log_pos ht
  have h : 0 ≤ 1/(t*(Real.log t)^2) + 2/(t*(Real.log t)^3) := by positivity
  rw [psiD, abs_neg, abs_of_nonneg h]

-- ===== new material =====

private lemma tendsto_PP : Tendsto PP atTop (𝓝 0) := by
  have hlinv : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have h2 : Tendsto (fun t : ℝ => ((Real.log t)^2)⁻¹) atTop (𝓝 0) := by
    have h := hlinv.pow 2
    simpa [inv_pow] using h
  have hpsi : Tendsto (fun t : ℝ => (Real.log t)⁻¹ + ((Real.log t)^2)⁻¹) atTop (𝓝 0) := by
    have h := hlinv.add h2
    simpa using h
  have hcomp : Tendsto (fun t : ℝ => Complex.ofReal ((Real.log t)⁻¹ + ((Real.log t)^2)⁻¹))
      atTop (𝓝 0) := by
    have h := (tendsto_ofReal_iff (f := fun t : ℝ => (Real.log t)⁻¹ + ((Real.log t)^2)⁻¹)
      (x := (0:ℝ))).mpr hpsi
    simpa using h
  have hx : (fun t : ℝ => Complex.ofReal ((Real.log t)⁻¹ + ((Real.log t)^2)⁻¹))
      = fun t : ℝ => Complex.ofReal ((Real.log t)⁻¹) + Complex.ofReal (((Real.log t)^2)⁻¹) := by
    funext t; rw [Complex.ofReal_add]
  rw [hx] at hcomp
  change Tendsto (fun t : ℝ => Complex.ofReal ((Real.log t)⁻¹)
    + Complex.ofReal (((Real.log t)^2)⁻¹)) atTop (𝓝 0)
  exact hcomp

private lemma tendsto_GG {z : ℂ} (hz : z.re = 1/2) : Tendsto (GG z) atTop (𝓝 0) := by
  have hc : Tendsto (fun t : ℝ => (t:ℂ)^(z-1)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hev : (fun t : ℝ => ‖(t:ℂ)^(z-1)‖) =ᶠ[atTop] (fun t : ℝ => t ^ (-(1/2):ℝ)) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
        show (z-1).re = -(1/2:ℝ) by rw [Complex.sub_re, Complex.one_re, hz]; norm_num]
    exact (tendsto_congr' hev).mpr (tendsto_rpow_neg_atTop (by norm_num))
  have h := hc.div_const (z-1)
  change Tendsto (fun t : ℝ => (t:ℂ)^(z-1)/(z-1)) atTop (𝓝 0)
  simpa using h

private lemma tendsto_HH {z : ℂ} (hz : z.re = 1/2) : Tendsto (HH z) atTop (𝓝 0) := by
  have h := (tendsto_GG hz).mul tendsto_PP
  change Tendsto (fun t : ℝ => GG z t * PP t) atTop (𝓝 0)
  simpa using h

private lemma integrableOn_Ioi_rpow_three_halves {f : ℝ → ℂ} {x C : ℝ} (hx : 0 < x) (_hC : 0 ≤ C)
    (hcont : ContinuousOn f (Ioi x))
    (hbound : ∀ t ∈ Ioi x, ‖f t‖ ≤ C * t ^ (-(3/2) : ℝ)) :
    IntegrableOn f (Ioi x) := by
  have hgrp : Integrable (fun t : ℝ => t ^ (-(3/2):ℝ)) (volume.restrict (Ioi x)) :=
    integrableOn_Ioi_rpow_of_lt (a := -(3/2)) (c := x) (by norm_num) hx
  have hg : Integrable (fun t : ℝ => C * t ^ (-(3/2):ℝ)) (volume.restrict (Ioi x)) :=
    hgrp.const_mul C
  refine Integrable.mono' hg ?_ ?_
  · exact hcont.aestronglyMeasurable isOpen_Ioi.measurableSet
  · rw [ae_restrict_iff' isOpen_Ioi.measurableSet]
    exact Filter.Eventually.of_forall hbound

private lemma continuousOn_FF {z : ℂ} {x : ℝ} (hx0 : 0 < x) (hx1 : 1 < x) :
    ContinuousOn (FF z) (Ioi x) := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
  have ht1 : 1 < t := lt_of_lt_of_le hx1 (le_of_lt ht)
  exact ((continuousAt_cpow_ofReal ht0).mul (continuousAt_PP ht1)).continuousWithinAt

private lemma continuousOn_RR {z : ℂ} {x : ℝ} (hx0 : 0 < x) (hx1 : 1 < x) :
    ContinuousOn (RR z) (Ioi x) := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le hx0 (le_of_lt ht)
  have ht1 : 1 < t := lt_of_lt_of_le hx1 (le_of_lt ht)
  have hD : ContinuousAt (fun s : ℝ => ((psiD s : ℝ) : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_psiD ht1)
  exact (((continuousAt_cpow_ofReal ht0).div_const (z-1)).mul hD).continuousWithinAt

private lemma norm_FF_le {z : ℂ} (hz : z.re = 1/2) {x t : ℝ} (hx : 2 ≤ x) (ht : x ≤ t) :
    ‖FF z t‖ ≤ psiR 2 * t ^ (-(3/2):ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith) ht
  have ht2 : 2 ≤ t := le_trans hx ht
  have ht1 : 1 < t := by linarith
  rw [FF, norm_mul, norm_PP ht1, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
    show (z-2).re = -(3/2:ℝ) by rw [Complex.sub_re, hz]; norm_num]
  calc t ^ (-(3/2):ℝ) * psiR t ≤ t ^ (-(3/2):ℝ) * psiR 2 :=
        mul_le_mul_of_nonneg_left (psiR_anti ht2) (Real.rpow_nonneg ht0.le _)
    _ = psiR 2 * t ^ (-(3/2):ℝ) := by ring

private lemma psiD_bound {a t : ℝ} (ha : 1 < a) (ht : a ≤ t) :
    t ^ (-(1/2):ℝ) * |psiD t| ≤ (1/(Real.log a)^2 + 2/(Real.log a)^3) * t ^ (-(3/2):ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith) ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hle : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht
  have hB : t ^ (-(3/2):ℝ) = t ^ (-(1/2):ℝ) * t⁻¹ := by
    rw [show (-(3/2):ℝ) = (-(1/2)) + (-1) by norm_num, Real.rpow_add ht0, Real.rpow_neg_one]
  have e1 : t ^ (-(1/2):ℝ) * (1/(t*(Real.log t)^2))
      = t ^ (-(3/2):ℝ) * (1/(Real.log t)^2) := by
    rw [hB, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
  have e2 : t ^ (-(1/2):ℝ) * (2/(t*(Real.log t)^3))
      = t ^ (-(3/2):ℝ) * (2/(Real.log t)^3) := by
    rw [hB, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
  have hsq1 : 1/(Real.log t)^2 ≤ 1/(Real.log a)^2 :=
    one_div_le_one_div_of_le (pow_pos hloga 2) (pow_le_pow_left₀ hloga.le hle 2)
  have hsq2 : 2/(Real.log t)^3 ≤ 2/(Real.log a)^3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hloga 3) (pow_le_pow_left₀ hloga.le hle 3)
  have ht32nn : 0 ≤ t ^ (-(3/2):ℝ) := Real.rpow_nonneg ht0.le _
  rw [abs_psiD ht1]
  calc t ^ (-(1/2):ℝ) * (1/(t*(Real.log t)^2) + 2/(t*(Real.log t)^3))
      = t ^ (-(1/2):ℝ) * (1/(t*(Real.log t)^2)) + t ^ (-(1/2):ℝ) * (2/(t*(Real.log t)^3)) := by ring
    _ = t ^ (-(3/2):ℝ) * (1/(Real.log t)^2) + t ^ (-(3/2):ℝ) * (2/(Real.log t)^3) := by rw [e1, e2]
    _ = t ^ (-(3/2):ℝ) * (1/(Real.log t)^2 + 2/(Real.log t)^3) := by ring
    _ ≤ t ^ (-(3/2):ℝ) * (1/(Real.log a)^2 + 2/(Real.log a)^3) :=
        mul_le_mul_of_nonneg_left (add_le_add hsq1 hsq2) ht32nn
    _ = (1/(Real.log a)^2 + 2/(Real.log a)^3) * t ^ (-(3/2):ℝ) := by ring

private lemma norm_RR_le {z : ℂ} (hz : z.re = 1/2) {a t : ℝ} (ha : 1 < a) (ht : a ≤ t) :
    ‖RR z t‖ ≤ (1/‖z-1‖) * (1/(Real.log a)^2 + 2/(Real.log a)^3) * t ^ (-(3/2):ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith) ht
  rw [norm_RR hz ht0]
  have h := psiD_bound ha ht
  have hz1nn : 0 ≤ 1/‖z-1‖ := div_nonneg zero_le_one (norm_nonneg _)
  calc t ^ (-(1/2):ℝ) / ‖z-1‖ * |psiD t|
      = (1/‖z-1‖) * (t ^ (-(1/2):ℝ) * |psiD t|) := by ring
    _ ≤ (1/‖z-1‖) * ((1/(Real.log a)^2 + 2/(Real.log a)^3) * t ^ (-(3/2):ℝ)) :=
        mul_le_mul_of_nonneg_left h hz1nn
    _ = (1/‖z-1‖) * (1/(Real.log a)^2 + 2/(Real.log a)^3) * t ^ (-(3/2):ℝ) := by ring

theorem integral_Fz_bound {z : ℂ} (hz : z.re = 1/2) {x : ℝ} (hx : 2 ≤ x) :
    ‖∫ t in Set.Ioi x, (t : ℂ) ^ (z - 2) * ((Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹)‖
      ≤ 2 / ‖1 - z‖ * x ^ (-(1 / 2) : ℝ) / Real.log x
        + 2 / ‖1 - z‖ * x ^ (-(1 / 2) : ℝ) / (Real.log x) ^ 2 * (1 + 4 / Real.log x) := by
  change ‖∫ t in Set.Ioi x, FF z t‖ ≤ _
  have hx0 : 0 < x := by linarith
  have hx1 : (1:ℝ) < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
  have hPpos : 0 < ‖z - 1‖ := by rw [norm_pos_iff]; intro h; exact hz1 (sub_eq_zero.mp h)
  have hFint : IntegrableOn (FF z) (Ioi x) :=
    integrableOn_Ioi_rpow_three_halves hx0 (le_of_lt (psiR_pos (by norm_num : (1:ℝ) < 2)))
      (continuousOn_FF hx0 hx1) (fun t ht => norm_FF_le hz hx (le_of_lt ht))
  have hRconst_nn : 0 ≤ (1/‖z-1‖) * (1/(Real.log x)^2 + 2/(Real.log x)^3) :=
    mul_nonneg (div_nonneg zero_le_one (norm_nonneg _)) (by positivity)
  have hRint : IntegrableOn (RR z) (Ioi x) :=
    integrableOn_Ioi_rpow_three_halves hx0 hRconst_nn (continuousOn_RR hx0 hx1)
      (fun t ht => norm_RR_le hz hx1 (le_of_lt ht))
  have hIntFR : IntegrableOn (fun t => FF z t + RR z t) (Ioi x) := hFint.add hRint
  have hHtend : Tendsto (HH z) atTop (𝓝 0) := tendsto_HH hz
  have hHderiv : ∀ t ∈ Ici x, HasDerivAt (HH z) (FF z t + RR z t) t :=
    fun t ht => hasDerivAt_HH hz1 (le_trans hx (mem_Ici.mp ht))
  have hkey := integral_Ioi_of_hasDerivAt_of_tendsto' hHderiv hIntFR hHtend
  have hsplit : ∫ t in Ioi x, (FF z t + RR z t)
      = (∫ t in Ioi x, FF z t) + (∫ t in Ioi x, RR z t) := integral_add hFint hRint
  have hI : ∫ t in Ioi x, FF z t = - HH z x - ∫ t in Ioi x, RR z t := by
    rw [hsplit, zero_sub] at hkey
    rw [eq_sub_iff_add_eq]
    exact hkey
  have hnorm1 : ‖∫ t in Ioi x, FF z t‖ ≤ ‖HH z x‖ + ‖∫ t in Ioi x, RR z t‖ := by
    rw [hI]
    rw [show -HH z x - (∫ t in Ioi x, RR z t)
        = -(HH z x + ∫ t in Ioi x, RR z t) by ring, norm_neg]
    exact norm_add_le _ _
  have hnorm2 : ‖∫ t in Ioi x, RR z t‖ ≤ ∫ t in Ioi x, ‖RR z t‖ :=
    norm_integral_le_integral_norm (fun t : ℝ => RR z t)
  have hHx : ‖HH z x‖ ≤ x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/Real.log x + 1/(Real.log x)^2) := by
    have e1 : ‖HH z x‖ = ‖GG z x‖ * ‖PP x‖ := by rw [HH, norm_mul]
    have e2 : ‖GG z x‖ * ‖PP x‖ = x ^ (-(1/2):ℝ) / ‖z-1‖ * psiR x := by
      rw [norm_GG hx0, norm_PP hx1,
        show (z-1).re = -(1/2:ℝ) by rw [Complex.sub_re, Complex.one_re, hz]; norm_num]
    have e3 : x ^ (-(1/2):ℝ) / ‖z-1‖ * psiR x
        = x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/Real.log x + 1/(Real.log x)^2) := by
      simp only [psiR]; ring
    rw [e1, e2, e3]
  have hRx : (∫ t in Ioi x, ‖RR z t‖)
      ≤ 2 * x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/(Real.log x)^2 + 2/(Real.log x)^3) := by
    have hgint : IntegrableOn (fun t : ℝ =>
        (1/‖z-1‖) * (1/(Real.log x)^2 + 2/(Real.log x)^3) * t ^ (-(3/2):ℝ)) (Ioi x) := by
      have hrp : Integrable (fun t : ℝ => t ^ (-(3/2):ℝ)) (volume.restrict (Ioi x)) :=
        integrableOn_Ioi_rpow_of_lt (a := -(3/2)) (c := x) (by norm_num) hx0
      exact hrp.const_mul _
    have hRi : Integrable (fun t : ℝ => ‖RR z t‖) (volume.restrict (Ioi x)) :=
      (show Integrable (RR z) (volume.restrict (Ioi x)) from hRint).norm
    have hmono : (∫ t in Ioi x, ‖RR z t‖)
        ≤ ∫ t in Ioi x, (1/‖z-1‖) * (1/(Real.log x)^2 + 2/(Real.log x)^3) * t ^ (-(3/2):ℝ) := by
      apply integral_mono_ae hRi hgint
      filter_upwards [ae_restrict_mem isOpen_Ioi.measurableSet] with t ht
      exact norm_RR_le hz hx1 (le_of_lt ht)
    rw [integral_const_mul] at hmono
    have hrpval : (∫ t in Ioi x, t ^ (-(3/2):ℝ)) = 2 * x ^ (-(1/2):ℝ) := by
      rw [integral_Ioi_rpow_of_lt (a := -(3/2)) (c := x) (by norm_num) hx0,
        show (-(3/2):ℝ) + 1 = -(1/2) by norm_num]
      ring
    rw [hrpval] at hmono
    have heq : (1/‖z-1‖) * (1/(Real.log x)^2 + 2/(Real.log x)^3) * (2 * x ^ (-(1/2):ℝ))
        = 2 * x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/(Real.log x)^2 + 2/(Real.log x)^3) := by ring
    rwa [heq] at hmono
  have hbnd : ‖∫ t in Ioi x, FF z t‖
      ≤ x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/Real.log x + 1/(Real.log x)^2)
        + 2 * x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/(Real.log x)^2 + 2/(Real.log x)^3) :=
    le_trans hnorm1 (add_le_add hHx (le_trans hnorm2 hRx))
  have hfin : x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/Real.log x + 1/(Real.log x)^2)
        + 2 * x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/(Real.log x)^2 + 2/(Real.log x)^3)
      ≤ 2 / ‖1 - z‖ * x ^ (-(1/2):ℝ) / Real.log x
        + 2 / ‖1 - z‖ * x ^ (-(1/2):ℝ) / (Real.log x)^2 * (1 + 4/Real.log x) := by
    rw [← norm_sub_rev z 1]
    have hX : 0 < x ^ (-(1/2):ℝ) := Real.rpow_pos_of_pos hx0 _
    have hAnn : 0 ≤ x ^ (-(1/2):ℝ) / ‖z-1‖ := div_nonneg hX.le hPpos.le
    have key : 1/Real.log x + 3/(Real.log x)^2 + 4/(Real.log x)^3
        ≤ 2/Real.log x + 2/(Real.log x)^2 * (1 + 4/Real.log x) := by
      have hL3 : 0 < (Real.log x)^3 := by positivity
      rw [← sub_nonneg]
      have heq : 2/Real.log x + 2/(Real.log x)^2 * (1 + 4/Real.log x)
          - (1/Real.log x + 3/(Real.log x)^2 + 4/(Real.log x)^3)
          = ((Real.log x)^2 - Real.log x + 4) / (Real.log x)^3 := by
        field_simp
        ring
      rw [heq]
      apply div_nonneg _ hL3.le
      nlinarith [sq_nonneg (Real.log x - 1/2)]
    have hm := mul_le_mul_of_nonneg_left key hAnn
    have hL : x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/Real.log x + 1/(Real.log x)^2)
        + 2 * x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/(Real.log x)^2 + 2/(Real.log x)^3)
        = x ^ (-(1/2):ℝ) / ‖z-1‖ * (1/Real.log x + 3/(Real.log x)^2 + 4/(Real.log x)^3) := by ring
    have hR : 2 / ‖z-1‖ * x ^ (-(1/2):ℝ) / Real.log x
          + 2 / ‖z-1‖ * x ^ (-(1/2):ℝ) / (Real.log x)^2 * (1 + 4/Real.log x)
        = x ^ (-(1/2):ℝ) / ‖z-1‖ * (2/Real.log x + 2/(Real.log x)^2 * (1 + 4/Real.log x)) := by ring
    rw [hL, hR]
    exact hm
  exact le_trans hbnd hfin


end

end Commons.Analysis.Complex