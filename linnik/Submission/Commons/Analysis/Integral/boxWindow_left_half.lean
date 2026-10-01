import Mathlib
import Submission.Commons.Analysis.Integral.wg_nonneg
import Submission.Commons.Analysis.Integral.boxWindow_C_lower
import Submission.Commons.Analysis.Integral.boxWindow_sixth_lower
import Submission.Commons.Analysis.Integral.boxWindow_sixth_upper
import Submission.Commons.Analysis.Integral.boxWindow_threequarter_pointwise
import Submission.Commons.Analysis.Real.WJ_sixth_lower
import Submission.Commons.Analysis.Real.WJ_threequarter_lower
import Submission.Commons.Analysis.Real.WJ_pair_half_lower
import Submission.Commons.Analysis.Real.WJ_pair_quarter_lower
import Submission.Commons.Analysis.Integral.boxMaj_le_target_kernel_ge_sixth
import Submission.Commons.Analysis.Integral.boxWindow_A0_lower
import Submission.Commons.Analysis.Integral.boxWindow_B_lower_11_20
import Submission.Commons.Analysis.Real.log_one_add_ge_two_mul_div
import Submission.Commons.Analysis.Integral.integral_inv_sq_add
import Submission.Commons.Analysis.Integral.boxWindow_C1_facts
import Submission.Commons.Analysis.Integral.boxWindow_Lb_facts
import Submission.Commons.Analysis.Integral.boxWindow_regionB_mid
import Submission.Commons.Analysis.Integral.boxWindow_F2f_bound
import Submission.Commons.Analysis.Integral.L2log_lower_bound

namespace Commons.Analysis.Integral

namespace BWLH

/-! ## Auxiliary development for `boxWindow_lowrange_nonneg` (ported, self-contained) -/
namespace BWL

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-!
# `boxWindow_left_half`

The target statement: for `0 < β < 1` and `δ ∈ [-1/2,-1/6]`, the window integral
`∫_δ^{δ+1} E(β,s) ds ≥ 0`, where `E` is the (even) difference between the target kernel
`(13/5)h` plus its Taylor correction and the elementary majorant for the box kernel.

Strategy of the proof:

* `E(β,s) = WK β s` is even in `s`, so that for `δ = -a`,
  `∫_δ^{δ+1} E = ∫_0^a WK + ∫_0^{1-a} WK`.
* Pointwise, `WK β t ≥ Wg β t` on `(0,5/6]`, where `Wg` is obtained by replacing the two
  majorants by the elementary upper bounds `WhBf`, `Whbf`.
* Hence `∫_0^t WK ≥ WJ β t := ∫_0^t Wg` for `t ∈ [0,5/6]`.
* Finally `WJ β x + WJ β (1-x) ≥ 0` for `x ∈ [1/6,1/2]`.
-/

/-- Positive (target-kernel) part of the integrand, as a function of `t = |s|`. -/
noncomputable def WTT (β t : ℝ) : ℝ :=
  (13/5)*((3/2-β)/((3/2-β)^2+t^2)+(1+β)/((1+β)^2+t^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2+t^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+t^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+t^2)^3)

/-- The `2-β` majorant with its branch cut. -/
noncomputable def WMBbig (β t : ℝ) : ℝ :=
  if t ≤ 2-β then Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t))*(1-t^2/(4*(2-β)^2))
  else (2-β)^2/(t*Real.sqrt ((2-β)^2+t^2))

/-- The `β` majorant with its branch cut. -/
noncomputable def WMb (β t : ℝ) : ℝ :=
  if t ≤ β then Real.log ((4*β^2+t^2)/(2*β*t))*(1-t^2/(2*((2-β)^2+β^2)))
  else (2-β)*β/(t*Real.sqrt ((2-β)^2+t^2))

/-- The integrand of the target statement (as a function of `s`). -/
noncomputable def WK (β s : ℝ) : ℝ := WTT β |s| - WMBbig β |s| - WMb β |s|

/-- Elementary upper bound for the `2-β` majorant. -/
noncomputable def WhBf (β t : ℝ) : ℝ := Real.log (2*(2-β)) - Real.log t + t^2/(4*(2-β)^2)

/-- Elementary upper bound for the `β` majorant. -/
noncomputable def Whbf (β t : ℝ) : ℝ :=
  if t ≤ β then Real.log (2*β) - Real.log t + t^2/(4*β^2) else β/t

/-- Pointwise lower bound for the integrand. -/
noncomputable def Wg (β t : ℝ) : ℝ := WTT β t - WhBf β t - Whbf β t

/-- The statement's integrand is `WK`. -/
lemma WK_eq (β s : ℝ) :
    WK β s =
        ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        - ( (if (|s|:ℝ) ≤ 2-β then
              Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
           + (if (|s|:ℝ) ≤ β then
              Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) ) := by
  simp only [WK, WTT, WMBbig, WMb]
  rw [sq_abs]
  ring

lemma WK_neg (β s : ℝ) : WK β (-s) = WK β s := by
  simp [WK]

/-- The integrand without the `|·|` (used for `t > 0`, where `WK β t = WKcore β t`). -/
noncomputable def WKcore (β t : ℝ) : ℝ := WTT β t - WMBbig β t - WMb β t

lemma WK_eq_core (β s : ℝ) : WK β s = WKcore β |s| := rfl

/-! ## The elementary majorant is dominated by the target kernel -/

lemma WMBbig_le_WhBf {β t : ℝ} (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 5/6) :
    WMBbig β t ≤ WhBf β t := by
  have hA : (0:ℝ) < 2-β := by linarith
  have htA : t ≤ 2-β := by linarith
  rw [WMBbig, if_pos htA, WhBf]
  set A : ℝ := 2-β with hAdef
  have hApos : 0 < A := by rw [hAdef]; exact hA
  have hAne : A ≠ 0 := ne_of_gt hApos
  have htne : t ≠ 0 := ne_of_gt ht0
  set u : ℝ := t^2/(4*A^2) with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have hu1 : u ≤ 1 := by
    rw [hudef, div_le_one (by positivity)]
    nlinarith [hApos, ht, htA]
  have hlogeq : (4*A^2+t^2)/(2*A*t) = (2*A/t)*(1+u) := by
    rw [hudef]; field_simp; ring
  have hLdef : Real.log (2*A) - Real.log t + u = Real.log (2*A/t) + u := by
    rw [Real.log_div (by positivity) htne]
  have hlogle : Real.log ((4*A^2+t^2)/(2*A*t)) ≤ Real.log (2*A) - Real.log t + u := by
    rw [hlogeq, Real.log_mul (by positivity) (by positivity), hLdef]
    have h1 : Real.log (1+u) ≤ u := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1+u by linarith)
      linarith
    linarith
  have hLnn : 0 ≤ Real.log (2*A) - Real.log t + u := by
    have h2 : (1:ℝ) ≤ 2*A/t := by
      rw [le_div_iff₀ ht0]; linarith
    have h3 : 0 ≤ Real.log (2*A/t) := Real.log_nonneg h2
    rw [hLdef]; exact add_nonneg h3 hu0
  have hLnn2 : 0 ≤ Real.log ((4*A^2+t^2)/(2*A*t)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc Real.log ((4*A^2+t^2)/(2*A*t)) * (1-u)
      ≤ (Real.log (2*A) - Real.log t + u) * (1-u) := by
        apply mul_le_mul_of_nonneg_right hlogle; linarith
    _ ≤ (Real.log (2*A) - Real.log t + u) * 1 := by
        apply mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) - u ≤ 1) hLnn
    _ = Real.log (2*A) - Real.log t + t^2/(4*A^2) := by
        rw [mul_one, hudef, hAdef]

lemma WMb_le_Whbf {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    WMb β t ≤ Whbf β t := by
  have hA : (0:ℝ) < 2-β := by linarith
  rw [WMb, Whbf]
  by_cases h : t ≤ β
  · rw [if_pos h, if_pos h]
    set B : ℝ := β with hBdef
    have hBpos : 0 < B := by rw [hBdef]; exact hβ0
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have htne : t ≠ 0 := ne_of_gt ht0
    set v : ℝ := t^2/(4*B^2) with hvdef
    have hv0 : 0 ≤ v := by rw [hvdef]; positivity
    have hlogeq : (4*B^2+t^2)/(2*B*t) = (2*B/t)*(1+v) := by
      rw [hvdef]; field_simp; ring
    have hLdef : Real.log (2*B) - Real.log t + v = Real.log (2*B/t) + v := by
      rw [Real.log_div (by positivity) htne]
    have hlogle : Real.log ((4*B^2+t^2)/(2*B*t)) ≤ Real.log (2*B) - Real.log t + v := by
      rw [hlogeq, Real.log_mul (by positivity) (by positivity), hLdef]
      have h1 : Real.log (1+v) ≤ v := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1+v by linarith)
        linarith
      linarith
    have hLnn : 0 ≤ Real.log (2*B) - Real.log t + v := by
      have h2 : (1:ℝ) ≤ 2*B/t := by
        rw [le_div_iff₀ ht0]; linarith
      have h3 : 0 ≤ Real.log (2*B/t) := Real.log_nonneg h2
      rw [hLdef]; exact add_nonneg h3 hv0
    have hw0 : 0 ≤ 1 - t^2/(2*((2-B)^2+B^2)) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith [hBpos, h, hA]
    have hlog0 : 0 ≤ Real.log ((4*B^2+t^2)/(2*B*t)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hBpos, h]
    calc Real.log ((4*B^2+t^2)/(2*B*t)) * (1-t^2/(2*((2-B)^2+B^2)))
        ≤ Real.log ((4*B^2+t^2)/(2*B*t)) * 1 := by
          apply mul_le_mul_of_nonneg_left (by
            have : (0:ℝ) ≤ t^2/(2*((2-B)^2+B^2)) := by positivity
            linarith) hlog0
      _ ≤ Real.log (2*B) - Real.log t + v := by
          rw [mul_one]; exact hlogle
      _ = Real.log (2*B) - Real.log t + t^2/(4*B^2) := by rw [hvdef, hBdef]
  · rw [if_neg h, if_neg h]
    have hsp : (0:ℝ) < Real.sqrt ((2-β)^2+t^2) := Real.sqrt_pos.mpr (by positivity)
    have h1 : (2-β) ≤ Real.sqrt ((2-β)^2+t^2) := by
      have h2 : Real.sqrt ((2-β)^2) ≤ Real.sqrt ((2-β)^2+t^2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq hA.le] at h2
    rw [div_le_iff₀ (by positivity : (0:ℝ) < t*Real.sqrt ((2-β)^2+t^2))]
    have h3 : β/t*(t*Real.sqrt ((2-β)^2+t^2)) = β*Real.sqrt ((2-β)^2+t^2) := by
      field_simp
    rw [h3]
    nlinarith [hβ0, h1]

/-- The pointwise lower bound `Wg` for the integrand, on `(0,5/6]`. -/
lemma WK_core_ge_Wg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 5/6) :
    Wg β t ≤ WKcore β t := by
  have h1 := WMBbig_le_WhBf hβ1 ht0 ht
  have h2 := WMb_le_Whbf hβ0 hβ1 ht0
  simp only [Wg, WKcore]
  linarith


/-! ## The closed forms -/

/-- Closed form for `∫_0^t WTT β`. -/
noncomputable def WPT (β t : ℝ) : ℝ :=
  (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β)))
  + ((2-β)^2-β^2)/(2*(2-β)) * Real.arctan (t/(2-β))
  + ((2-β)^2-β^2)^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*t/((2-β)^2+t^2))/(2*(2-β)^3))
  + ((2-β)^2-β^2)^3/16 *
      (3*Real.arctan (t/(2-β))/(8*(2-β)^5)
        + t*(5*(2-β)^2+3*t^2)/(8*(2-β)^4*((2-β)^2+t^2)^2))

/-- Closed form for `∫_0^t Whbf β`. -/
noncomputable def Whbfint (β t : ℝ) : ℝ :=
  if t ≤ β then t*(Real.log (2*β) - Real.log t + 1) + t^3/(12*β^2)
  else β*(Real.log 2 + 13/12) + β*Real.log (t/β)

/-- Closed form for `∫_0^t Wg β`. -/
noncomputable def WJ (β t : ℝ) : ℝ :=
  WPT β t - (t*(Real.log (2*(2-β)) - Real.log t + 1) + t^3/(12*(2-β)^2)) - Whbfint β t

lemma integral_zero_t_const_mul {c t : ℝ} (f : ℝ → ℝ) :
    (∫ s in (0:ℝ)..t, c * f s) = c * (∫ s in (0:ℝ)..t, f s) :=
  intervalIntegral.integral_const_mul c f

lemma integral_WTT {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    (∫ s in (0:ℝ)..t, WTT β s) = WPT β t := by
  have ht0le : (0:ℝ) ≤ t := le_of_lt ht0
  have hA : (0:ℝ) < 2-β := by linarith
  have ha1 : (0:ℝ) < 3/2-β := by linarith
  have hc1 : (0:ℝ) < 1+β := by linarith
  set C : ℝ := (2-β)^2-β^2 with hCdef
  have hWTT : WTT β = fun s : ℝ =>
      (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
      + C/(2*((2-β)^2+s^2)) + C^2/(8*((2-β)^2+s^2)^2) + C^3/(16*((2-β)^2+s^2)^3) := by
    funext s; rw [hCdef]; rfl
  have hi1 : IntervalIntegrable (fun s : ℝ => (3/2-β)/((3/2-β)^2+s^2)) volume (0:ℝ) t :=
    (Continuous.div continuous_const (by fun_prop) (fun s => by positivity)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s : ℝ => (1+β)/((1+β)^2+s^2)) volume (0:ℝ) t :=
    (Continuous.div continuous_const (by fun_prop) (fun s => by positivity)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun s : ℝ => ((2-β)^2+s^2)⁻¹) volume (0:ℝ) t := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.inv₀ (by fun_prop) (fun x _ => by positivity)
  have hi4 : IntervalIntegrable (fun s : ℝ => (((2-β)^2+s^2)^2)⁻¹) volume (0:ℝ) t := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.inv₀ (by fun_prop) (fun x _ => by positivity)
  have hi5 : IntervalIntegrable (fun s : ℝ => (((2-β)^2+s^2)^3)⁻¹) volume (0:ℝ) t := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.inv₀ (by fun_prop) (fun x _ => by positivity)
  have hF1 : (∫ s in (0:ℝ)..t, (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)))
      = (13/5)*(Real.arctan (t/(3/2-β)) + Real.arctan (t/(1+β))) := by
    have e1 : (∫ s in (0:ℝ)..t, (3/2-β)/((3/2-β)^2+s^2)) = Real.arctan (t/(3/2-β)) := by
      rw [integral_inv_sq_add (k := 3/2-β) (p := (0:ℝ)) (q := t) ha1]
      simp
    have e2 : (∫ s in (0:ℝ)..t, (1+β)/((1+β)^2+s^2)) = Real.arctan (t/(1+β)) := by
      rw [integral_inv_sq_add (k := 1+β) (p := (0:ℝ)) (q := t) hc1]
      simp
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2, e1, e2]
  have hF2 : (∫ s in (0:ℝ)..t, C/(2*((2-β)^2+s^2)))
      = C/(2*(2-β)) * Real.arctan (t/(2-β)) := by
    rw [show (fun s : ℝ => C/(2*((2-β)^2+s^2))) = fun s : ℝ => (C/2) * ((2-β)^2+s^2)⁻¹ by
      funext s; rw [div_eq_mul_inv, mul_inv]; ring]
    rw [intervalIntegral.integral_const_mul, integral_zero_u_inv_sq_add hA ht0le]
    field_simp
  have hF3 : (∫ s in (0:ℝ)..t, C^2/(8*((2-β)^2+s^2)^2))
      = C^2/8 * ((Real.arctan (t/(2-β)) + (2-β)*t/((2-β)^2+t^2))/(2*(2-β)^3)) := by
    rw [show (fun s : ℝ => C^2/(8*((2-β)^2+s^2)^2)) = fun s : ℝ => (C^2/8) * (((2-β)^2+s^2)^2)⁻¹ by
      funext s; rw [div_eq_mul_inv, mul_inv]; ring]
    rw [intervalIntegral.integral_const_mul, integral_zero_u_inv_sq_add_sq hA ht0le]
  have hF4 : (∫ s in (0:ℝ)..t, C^3/(16*((2-β)^2+s^2)^3))
      = C^3/16 * (3*Real.arctan (t/(2-β))/(8*(2-β)^5)
        + t*(5*(2-β)^2+3*t^2)/(8*(2-β)^4*((2-β)^2+t^2)^2)) := by
    rw [show (fun s : ℝ => C^3/(16*((2-β)^2+s^2)^3)) = fun s : ℝ => (C^3/16) * (((2-β)^2+s^2)^3)⁻¹ by
      funext s; rw [div_eq_mul_inv, mul_inv]; ring]
    rw [intervalIntegral.integral_const_mul, integral_zero_u_inv_sq_add_cube hA ht0le]
  have hiF1 : IntervalIntegrable
      (fun s : ℝ => (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))) volume (0:ℝ) t :=
    (hi1.add hi2).const_mul _
  have hiF2 : IntervalIntegrable (fun s : ℝ => C/(2*((2-β)^2+s^2))) volume (0:ℝ) t := by
    apply Continuous.intervalIntegrable
    exact Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
  have hiF3 : IntervalIntegrable (fun s : ℝ => C^2/(8*((2-β)^2+s^2)^2)) volume (0:ℝ) t := by
    apply Continuous.intervalIntegrable
    exact Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
  have hiF4 : IntervalIntegrable (fun s : ℝ => C^3/(16*((2-β)^2+s^2)^3)) volume (0:ℝ) t := by
    apply Continuous.intervalIntegrable
    exact Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
  rw [hWTT]
  rw [intervalIntegral.integral_add ((hiF1.add hiF2).add hiF3) hiF4,
      intervalIntegral.integral_add (hiF1.add hiF2) hiF3,
      intervalIntegral.integral_add hiF1 hiF2,
      hF1, hF2, hF3, hF4]
  simp only [WPT, hCdef]

lemma integral_zero_t_sq_div {c t : ℝ} (hc : c ≠ 0) :
    (∫ s in (0:ℝ)..t, s^2/c) = t^3/(3*c) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) t, HasDerivAt (fun s : ℝ => s^3/(3*c)) (x^2/c) x := by
    intro x _
    have h := (hasDerivAt_pow 3 x).div_const (3*c)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun s : ℝ => s^2/c) volume (0:ℝ) t := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) continuous_const (fun s => hc)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using h

lemma integral_WhBf {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    (∫ s in (0:ℝ)..t, WhBf β s)
      = t*(Real.log (2*(2-β)) - Real.log t + 1) + t^3/(12*(2-β)^2) := by
  have hA : (0:ℝ) < 2-β := by linarith
  have hAne : (2-β) ≠ 0 := ne_of_gt hA
  have htne : t ≠ 0 := ne_of_gt ht0
  have heq : (fun s : ℝ => WhBf β s) = fun s : ℝ =>
      Real.log (2*(2-β)) - Real.log s + s^2/(4*(2-β)^2) := by
    funext s; simp only [WhBf]
  rw [heq]
  have hi1 : IntervalIntegrable (fun _ : ℝ => Real.log (2*(2-β))) volume (0:ℝ) t :=
    intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) t := intervalIntegrable_log'
  have hi3 : IntervalIntegrable (fun s : ℝ => s^2/(4*(2-β)^2)) volume (0:ℝ) t := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) continuous_const (fun s => by positivity)
  rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2]
  rw [intervalIntegral.integral_const, integral_zero_u_log ht0,
      integral_zero_t_sq_div (by positivity : (4:ℝ)*(2-β)^2 ≠ 0)]
  field_simp
  ring

lemma integral_Whbf {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    (∫ s in (0:ℝ)..t, Whbf β s) = Whbfint β t := by
  have hB : (0:ℝ) < β := hβ0
  have hBne : β ≠ 0 := ne_of_gt hB
  have htne : t ≠ 0 := ne_of_gt ht0
  have hlogbr : ∀ x ∈ Set.Ioo (0:ℝ) β, Whbf β x = Real.log (2*β) - Real.log x + x^2/(4*β^2) := by
    intro x hx
    simp only [Whbf]
    rw [if_pos (le_of_lt hx.2)]
  have hlogbr' : ∀ x ∈ Set.Ioc (0:ℝ) β, Whbf β x = Real.log (2*β) - Real.log x + x^2/(4*β^2) := by
    intro x hx
    simp only [Whbf]
    rw [if_pos hx.2]
  have helse : ∀ x ∈ Set.Ioc β t, Whbf β x = β/x := by
    intro x hx
    simp only [Whbf]
    rw [if_neg (not_le.mpr hx.1)]
  rw [Whbfint]
  by_cases h : t ≤ β
  · rw [if_pos h]
    have hcongr : (∫ s in (0:ℝ)..t, Whbf β s)
        = (∫ s in (0:ℝ)..t, Real.log (2*β) - Real.log s + s^2/(4*β^2)) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [Set.uIoo_of_le ht0.le] at hx
      exact hlogbr x ⟨hx.1, lt_of_lt_of_le hx.2 h⟩
    rw [hcongr]
    have hi1 : IntervalIntegrable (fun _ : ℝ => Real.log (2*β)) volume (0:ℝ) t :=
      intervalIntegrable_const
    have hi2 : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) t := intervalIntegrable_log'
    have hi3 : IntervalIntegrable (fun s : ℝ => s^2/(4*β^2)) volume (0:ℝ) t := by
      apply Continuous.intervalIntegrable
      exact Continuous.div (by fun_prop) continuous_const (fun s => by positivity)
    rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2]
    rw [intervalIntegral.integral_const, integral_zero_u_log ht0,
        integral_zero_t_sq_div (by positivity : (4:ℝ)*β^2 ≠ 0)]
    field_simp
    ring
  · have h' : β < t := not_le.mp h
    rw [if_neg h]
    have hgb : IntervalIntegrable
        (fun s : ℝ => Real.log (2*β) - Real.log s + s^2/(4*β^2)) volume (0:ℝ) β := by
      exact (intervalIntegrable_const.sub intervalIntegrable_log').add
        (Continuous.intervalIntegrable (by fun_prop) _ _)
    have hint1 : IntervalIntegrable (fun s : ℝ => Whbf β s) volume (0:ℝ) β := by
      refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => Whbf β s)
        (g := fun s : ℝ => Real.log (2*β) - Real.log s + s^2/(4*β^2)) hgb ?_ ?_
      · apply Measurable.aestronglyMeasurable
        show Measurable (fun s : ℝ => if s ≤ β then
          Real.log (2*β) - Real.log s + s^2/(4*β^2) else β/s)
        apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
      · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        apply Filter.Eventually.of_forall
        intro x hx
        rw [Set.uIoc_of_le hβ0.le] at hx
        have hxpos : 0 < x := hx.1
        rw [hlogbr' x hx]
        have h1 : 0 ≤ Real.log (2*β) - Real.log x := by
          rw [sub_nonneg, Real.log_le_log_iff hxpos (by positivity : (0:ℝ) < 2*β)]
          linarith [hx.2]
        have h2 : 0 ≤ x^2/(4*β^2) := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hint2 : IntervalIntegrable (fun s : ℝ => Whbf β s) volume β t := by
      refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => Whbf β s)
        (g := fun s : ℝ => β/s) ?_ ?_ ?_
      · apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.div continuousOn_const continuousOn_id (fun x hx => by
          rw [Set.uIcc_of_le (le_of_lt h')] at hx
          exact ne_of_gt (lt_of_lt_of_le hB hx.1))
      · apply Measurable.aestronglyMeasurable
        show Measurable (fun s : ℝ => if s ≤ β then
          Real.log (2*β) - Real.log s + s^2/(4*β^2) else β/s)
        apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
      · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        apply Filter.Eventually.of_forall
        intro x hx
        rw [Set.uIoc_of_le (le_of_lt h')] at hx
        have hxpos : 0 < x := lt_trans hB hx.1
        rw [helse x hx]
        rw [Real.norm_eq_abs, abs_of_pos (div_pos hB hxpos)]
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hfirst : (∫ s in (0:ℝ)..β, Whbf β s) = β*(Real.log 2 + 13/12) := by
      have hcongr : (∫ s in (0:ℝ)..β, Whbf β s)
          = (∫ s in (0:ℝ)..β, Real.log (2*β) - Real.log s + s^2/(4*β^2)) := by
        apply intervalIntegral.integral_congr_uIoo
        intro x hx
        rw [Set.uIoo_of_le hβ0.le] at hx
        exact hlogbr x hx
      rw [hcongr]
      have hi1 : IntervalIntegrable (fun _ : ℝ => Real.log (2*β)) volume (0:ℝ) β :=
        intervalIntegrable_const
      have hi2 : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) β := intervalIntegrable_log'
      have hi3 : IntervalIntegrable (fun s : ℝ => s^2/(4*β^2)) volume (0:ℝ) β := by
        apply Continuous.intervalIntegrable
        exact Continuous.div (by fun_prop) continuous_const (fun s => by positivity)
      rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2]
      rw [intervalIntegral.integral_const, integral_zero_u_log hB,
          integral_zero_t_sq_div (by positivity : (4:ℝ)*β^2 ≠ 0)]
      rw [Real.log_mul (by norm_num) hBne]
      field_simp
      ring
    have hsecond : (∫ s in β..t, Whbf β s) = β*Real.log (t/β) := by
      have hcongr : (∫ s in β..t, Whbf β s) = (∫ s in β..t, β/s) := by
        apply intervalIntegral.integral_congr_uIoo
        intro x hx
        rw [Set.uIoo_of_le (le_of_lt h')] at hx
        exact helse x ⟨hx.1, le_of_lt hx.2⟩
      rw [hcongr]
      simp only [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
      have hder : ∀ x ∈ Set.uIcc β t, HasDerivAt Real.log x⁻¹ x := by
        intro x hx
        rw [Set.uIcc_of_le (le_of_lt h')] at hx
        exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hB hx.1))
      have hint : IntervalIntegrable (fun s : ℝ => s⁻¹) volume β t := by
        apply ContinuousOn.intervalIntegrable
        exact ContinuousOn.inv₀ continuousOn_id (fun x hx => by
          rw [Set.uIcc_of_le (le_of_lt h')] at hx
          exact ne_of_gt (lt_of_lt_of_le hB hx.1))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
      rw [show t * β⁻¹ = t/β by rw [div_eq_mul_inv], Real.log_div (ne_of_gt ht0) hBne]
    rw [hfirst, hsecond]

lemma integral_Wg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht56 : t ≤ 5/6) :
    (∫ s in (0:ℝ)..t, Wg β s) = WJ β t := by
  have hA : (0:ℝ) < 2-β := by linarith
  have hB : (0:ℝ) < β := hβ0
  have ha1 : (0:ℝ) < 3/2-β := by linarith
  have hc1 : (0:ℝ) < 1+β := by linarith
  have heq : Wg β = fun s : ℝ => WTT β s - WhBf β s - Whbf β s := rfl
  have hWTTi : IntervalIntegrable (fun s : ℝ => WTT β s) volume (0:ℝ) t := by
    apply Continuous.intervalIntegrable
    have h1 : Continuous (fun s : ℝ => (3/2-β)/((3/2-β)^2+s^2)) :=
      Continuous.div continuous_const (by fun_prop) (fun s => by
        have := sq_nonneg (3/2-β); have := sq_nonneg s; nlinarith)
    have h2 : Continuous (fun s : ℝ => (1+β)/((1+β)^2+s^2)) :=
      Continuous.div continuous_const (by fun_prop) (fun s => by
        have := sq_nonneg (1+β); have := sq_nonneg s; nlinarith)
    have h3 : Continuous (fun s : ℝ => ((2-β)^2-β^2)/(2*((2-β)^2+s^2))) :=
      Continuous.div continuous_const (by fun_prop) (fun s => by
        have := sq_nonneg (2-β); have := sq_nonneg s; nlinarith)
    have h4 : Continuous (fun s : ℝ => ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)) :=
      Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
    have h5 : Continuous (fun s : ℝ => ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) :=
      Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
    have hsum : Continuous (fun s : ℝ => ((13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3))) :=
      (((h1.add h2).const_mul (13/5)).add h3).add h4 |>.add h5
    convert hsum using 1
    funext s; simp only [WTT, Pi.add_apply]
  have hBfi : IntervalIntegrable (fun s : ℝ => WhBf β s) volume (0:ℝ) t := by
    have he : (fun s : ℝ => WhBf β s)
        = fun s : ℝ => Real.log (2*(2-β)) - Real.log s + s^2/(4*(2-β)^2) := by
      funext s; simp only [WhBf]
    rw [he]
    exact (intervalIntegrable_const.sub intervalIntegrable_log').add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hbfi : IntervalIntegrable (fun s : ℝ => Whbf β s) volume (0:ℝ) t := by
    have hmeas : AEStronglyMeasurable (fun s : ℝ => Whbf β s) (volume.restrict (Set.uIoc (0:ℝ) t)) := by
      apply Measurable.aestronglyMeasurable
      show Measurable (fun s : ℝ => if s ≤ β then
        Real.log (2*β) - Real.log s + s^2/(4*β^2) else β/s)
      apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
    by_cases h : t ≤ β
    · refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => Whbf β s)
        (g := fun s : ℝ => Real.log (2*β) - Real.log s + s^2/(4*β^2))
        ((intervalIntegrable_const.sub intervalIntegrable_log').add
          (Continuous.intervalIntegrable (by fun_prop) _ _)) hmeas ?_
      rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro x hx
      rw [Set.uIoc_of_le ht0.le] at hx
      have hxβ : x ≤ β := le_trans hx.2 h
      have hxpos : 0 < x := hx.1
      have he : Whbf β x = Real.log (2*β) - Real.log x + x^2/(4*β^2) := by
        simp only [Whbf]; rw [if_pos hxβ]
      rw [he, Real.norm_eq_abs, abs_of_nonneg]
      have h1 : 0 ≤ Real.log (2*β) - Real.log x := by
        rw [sub_nonneg, Real.log_le_log_iff hxpos (by positivity : (0:ℝ) < 2*β)]
        linarith [hxβ]
      positivity
    · have ht' : β < t := not_le.mp h
      refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => Whbf β s)
        (g := fun s : ℝ => 9 - Real.log s)
        (intervalIntegrable_const.sub intervalIntegrable_log') hmeas ?_
      rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro x hx
      rw [Set.uIoc_of_le ht0.le] at hx
      have hxpos : 0 < x := hx.1
      have hxlog : Real.log x ≤ 0 := Real.log_nonpos hxpos.le (by linarith [hx.2, ht56])
      by_cases hxβ : x ≤ β
      · have he : Whbf β x = Real.log (2*β) - Real.log x + x^2/(4*β^2) := by
          simp only [Whbf]; rw [if_pos hxβ]
        rw [he, Real.norm_eq_abs, abs_of_nonneg]
        · have h1 : Real.log (2*β) ≤ 1 := by
            have h2 : Real.log (2*β) ≤ Real.log 2 := by
              rw [Real.log_le_log_iff (by positivity) (by norm_num)]; linarith
            linarith [Real.log_two_lt_d9]
          have h3 : x^2/(4*β^2) ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          linarith
        · have h1 : 0 ≤ Real.log (2*β) - Real.log x := by
            rw [sub_nonneg, Real.log_le_log_iff hxpos (by positivity : (0:ℝ) < 2*β)]
            linarith [hxβ]
          positivity
      · have he : Whbf β x = β/x := by
          simp only [Whbf]; rw [if_neg hxβ]
        rw [he, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hβ0.le hxpos.le)]
        have hxx : β ≤ x := le_of_lt (not_le.mp hxβ)
        have h4 : β/x ≤ 1 := by rw [div_le_one hxpos]; exact hxx
        linarith
  rw [heq, WJ]
  rw [intervalIntegral.integral_sub (hWTTi.sub hBfi) hbfi,
      intervalIntegral.integral_sub hWTTi hBfi,
      integral_WTT hβ0 hβ1 ht0, integral_WhBf hβ0 hβ1 ht0, integral_Whbf hβ0 hβ1 ht0]

/-! ## Integrability of the integrand -/

lemma WTT_nonneg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ WTT β t := by
  have ha1 : (0:ℝ) < 3/2-β := by linarith
  have hc1 : (0:ℝ) < 1+β := by linarith
  have hC0 : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  simp only [WTT]
  have h1 : (0:ℝ) ≤ (3/2-β)/((3/2-β)^2+t^2) := div_nonneg ha1.le (by positivity)
  have h2 : (0:ℝ) ≤ (1+β)/((1+β)^2+t^2) := div_nonneg hc1.le (by positivity)
  have h3 : (0:ℝ) ≤ ((2-β)^2-β^2)/(2*((2-β)^2+t^2)) := div_nonneg hC0 (by positivity)
  have h4 : (0:ℝ) ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2+t^2)^2) := div_nonneg (by positivity) (by positivity)
  have h5 : (0:ℝ) ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2+t^2)^3) := div_nonneg (by positivity) (by positivity)
  have h6 : (0:ℝ) ≤ (13/5)*((3/2-β)/((3/2-β)^2+t^2)+(1+β)/((1+β)^2+t^2)) := by positivity
  linarith

lemma WTT_le {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : WTT β t ≤ 16 := by
  have ha1 : (0:ℝ) < 3/2-β := by linarith
  have hc1 : (0:ℝ) < 1+β := by linarith
  have hA : (0:ℝ) < 2-β := by linarith
  have hd1 : (0:ℝ) < (3/2-β)^2+t^2 := by nlinarith [ha1, sq_nonneg t]
  have hd2 : (0:ℝ) < (1+β)^2+t^2 := by nlinarith [hc1, sq_nonneg t]
  have hd3 : (0:ℝ) < (2-β)^2+t^2 := by nlinarith [hA, sq_nonneg t]
  have h1 : (3/2-β)/((3/2-β)^2+t^2) ≤ 1/(3/2-β) := by
    rw [div_le_div_iff₀ hd1 ha1]
    nlinarith [sq_nonneg t, ha1]
  have h2 : (1+β)/((1+β)^2+t^2) ≤ 1/(1+β) := by
    rw [div_le_div_iff₀ hd2 hc1]
    nlinarith [sq_nonneg t, hc1]
  have hC0 : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  have hC4 : (2-β)^2-β^2 ≤ 4 := by nlinarith
  have h3 : ((2-β)^2-β^2)/(2*((2-β)^2+t^2)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : ((2-β)^2-β^2)^2/(8*((2-β)^2+t^2)^2) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h5 : ((2-β)^2-β^2)^3/(16*((2-β)^2+t^2)^3) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have ha1i : 1/(3/2-β) ≤ 2 := by rw [div_le_iff₀ ha1]; linarith
  have hc1i : 1/(1+β) ≤ 1 := by rw [div_le_iff₀ hc1]; linarith
  have hT : (13/5)*((3/2-β)/((3/2-β)^2+t^2)+(1+β)/((1+β)^2+t^2)) ≤ (13/5)*(2+1) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    linarith
  simp only [WTT]
  linarith

lemma WMBbig_nonneg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    0 ≤ WMBbig β t := by
  have hA : (0:ℝ) < 2-β := by linarith
  rw [WMBbig]
  by_cases h : t ≤ 2-β
  · rw [if_pos h]
    apply mul_nonneg
    · apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  · rw [if_neg h]
    positivity

lemma WMb_nonneg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    0 ≤ WMb β t := by
  have hA : (0:ℝ) < 2-β := by linarith
  rw [WMb]
  by_cases h : t ≤ β
  · rw [if_pos h]
    apply mul_nonneg
    · apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith [ht0, hβ0, hβ1, sq_nonneg β]
  · rw [if_neg h]
    positivity

/-- Domination of the integrand near `0`. -/
lemma norm_WKcore_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 5/6) :
    |WKcore β s| ≤ 23 - 2*Real.log s := by
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs0.le (by linarith)
  have hlog2 : Real.log 2 ≤ 0.6931471808 := by linarith [Real.log_two_lt_d9]
  have hlog4 : Real.log 4 ≤ 2 := by
    have h : Real.log 4 = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    linarith [Real.log_two_lt_d9]
  have hB' := WMBbig_le_WhBf hβ1 hs0 hs
  have hb' := WMb_le_Whbf hβ0 hβ1 hs0
  have hA : (0:ℝ) < 2-β := by linarith
  have hB : WMBbig β s ≤ Real.log 4 - Real.log s + 1 := by
    have h2 : Real.log (2*(2-β)) ≤ Real.log 4 := by
      rw [Real.log_le_log_iff (by positivity) (by norm_num)]; linarith
    have h3 : s^2/(4*(2-β)^2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have h4 : WhBf β s ≤ Real.log 4 - Real.log s + 1 := by
      simp only [WhBf]; linarith
    linarith
  have hb : WMb β s ≤ Real.log 2 - Real.log s + 1 := by
    rw [Whbf] at hb'
    by_cases h : s ≤ β
    · rw [if_pos h] at hb'
      have h2 : Real.log (2*β) ≤ Real.log 2 := by
        rw [Real.log_le_log_iff (by positivity) (by norm_num)]; linarith
      have h3 : s^2/(4*β^2) ≤ 1/4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    · rw [if_neg h] at hb'
      have hsβ : β ≤ s := le_of_lt (not_le.mp h)
      have h1 : β/s ≤ 1 := by rw [div_le_one hs0]; exact hsβ
      have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
  rw [abs_le]
  constructor
  · have h4 : 0 ≤ WTT β s := WTT_nonneg hβ0 hβ1
    simp only [WKcore]
    linarith
  · have hTT16 : WTT β s ≤ 16 := WTT_le hβ0 hβ1
    have hlogs' : 0 ≤ -Real.log s := by linarith
    have hB0 : 0 ≤ WMBbig β s := WMBbig_nonneg hβ0 hβ1 hs0
    have hb0 : 0 ≤ WMb β s := WMb_nonneg hβ0 hβ1 hs0
    simp only [WKcore]
    linarith

lemma measurable_WTT (β : ℝ) : Measurable (WTT β) := by unfold WTT; fun_prop
lemma measurable_WMBbig (β : ℝ) : Measurable (WMBbig β) := by
  unfold WMBbig
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
lemma measurable_WMb (β : ℝ) : Measurable (WMb β) := by
  unfold WMb
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
lemma measurable_WK (β : ℝ) : Measurable (WK β) := by
  have h : WK β = fun s : ℝ => WTT β |s| - WMBbig β |s| - WMb β |s| := rfl
  rw [h]
  have h2 : Measurable (fun s : ℝ => WTT β |s|) := (measurable_WTT β).comp measurable_abs
  have h3 : Measurable (fun s : ℝ => WMBbig β |s|) := (measurable_WMBbig β).comp measurable_abs
  have h4 : Measurable (fun s : ℝ => WMb β |s|) := (measurable_WMb β).comp measurable_abs
  exact (h2.sub h3).sub h4

lemma intervalIntegrable_WK {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t)
    (ht : t ≤ 5/6) : IntervalIntegrable (WK β) volume (0:ℝ) t := by
  refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => WK β s)
    (g := fun s : ℝ => 23 - 2*Real.log s) ?_ ?_ ?_
  · have h1 : IntervalIntegrable (fun s : ℝ => 23 + (-2) * Real.log s) volume (0:ℝ) t :=
      intervalIntegrable_const.add (intervalIntegrable_log'.const_mul (-2))
    convert h1 using 1
    funext s; ring
  · exact (measurable_WK β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le ht0.le] at hx
    have hx0 : 0 < x := hx.1
    have hxabs : |x| = x := abs_of_pos hx0
    rw [show WK β x = WKcore β x from by rw [WK, WKcore, hxabs]]
    exact norm_WKcore_le hβ0 hβ1 hx0 (le_trans hx.2 ht)

lemma intervalIntegrable_WK_neg {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a)
    (ha : a ≤ 5/6) : IntervalIntegrable (WK β) volume (-a) 0 := by
  refine (IntervalIntegrable.iff_comp_neg (f := WK β) (a := -a) (b := (0:ℝ))).2 ?_
  have h2 : IntervalIntegrable (fun x => WK β (-x)) volume a 0 := by
    convert (intervalIntegrable_WK hβ0 hβ1 ha0 ha).symm using 1
    funext x
    exact WK_neg β x
  simpa using h2

lemma measurable_Wg (β : ℝ) : Measurable (Wg β) := by
  unfold Wg
  exact ((measurable_WTT β).sub (measurable_WhBf β)).sub (measurable_Whbf β)
where
  measurable_WhBf : ∀ β : ℝ, Measurable (WhBf β) := by
    intro β; unfold WhBf; fun_prop
  measurable_Whbf : ∀ β : ℝ, Measurable (Whbf β) := by
    intro β; unfold Whbf
    apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop

lemma norm_Wg_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 5/6) :
    |Wg β s| ≤ 21 - 2*Real.log s := by
  have hA : (0:ℝ) < 2-β := by linarith
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs0.le (by linarith)
  have hlog2 : Real.log 2 ≤ 0.6931471808 := by linarith [Real.log_two_lt_d9]
  have hlog2p : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : Real.log 4 ≤ 2 := by
    have h : Real.log 4 = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    linarith [Real.log_two_lt_d9]
  have hlog4p : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hTT : WTT β s ≤ 16 := WTT_le hβ0 hβ1
  have hBf : |WhBf β s| ≤ Real.log 4 - Real.log s + 1 := by
    have h3 : Real.log (2*(2-β)) ≤ Real.log 4 := by
      rw [Real.log_le_log_iff (by positivity) (by norm_num)]; linarith
    have h5 : s^2/(4*(2-β)^2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h30 : (0:ℝ) ≤ Real.log (2*(2-β)) := Real.log_nonneg (by linarith)
    have h50 : (0:ℝ) ≤ s^2/(4*(2-β)^2) := by positivity
    rw [abs_le]
    simp only [WhBf]
    constructor <;> linarith
  have hbf : |Whbf β s| ≤ Real.log 2 - Real.log s + 1 := by
    by_cases h : s ≤ β
    · have he : Whbf β s = Real.log (2*β) - Real.log s + s^2/(4*β^2) := by
        simp only [Whbf]; rw [if_pos h]
      have h0 : 0 ≤ Real.log (2*β) - Real.log s + s^2/(4*β^2) := by
        have h1 : 0 ≤ Real.log (2*β) - Real.log s := by
          rw [sub_nonneg, Real.log_le_log_iff hs0 (by positivity : (0:ℝ) < 2*β)]
          linarith
        have h2 : (0:ℝ) ≤ s^2/(4*β^2) := by positivity
        linarith
      rw [he, abs_of_nonneg h0]
      have h3 : Real.log (2*β) ≤ Real.log 2 := by
        rw [Real.log_le_log_iff (by positivity) (by norm_num)]; linarith
      have h5 : s^2/(4*β^2) ≤ 1/4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    · have he : Whbf β s = β/s := by
        simp only [Whbf]; rw [if_neg h]
      have h0 : 0 ≤ β/s := div_nonneg hβ0.le hs0.le
      rw [he, abs_of_nonneg h0]
      have hsβ : β ≤ s := le_of_lt (not_le.mp h)
      have h1 : β/s ≤ 1 := by rw [div_le_one hs0]; exact hsβ
      have h6 : 0 ≤ -Real.log s := by linarith
      linarith
  simp only [Wg]
  rw [abs_le]
  have hTT0 : 0 ≤ WTT β s := WTT_nonneg hβ0 hβ1
  constructor
  · have e1 : WhBf β s ≤ Real.log 4 - Real.log s + 1 := le_trans (le_abs_self _) hBf
    have e2 : Whbf β s ≤ Real.log 2 - Real.log s + 1 := le_trans (le_abs_self _) hbf
    linarith
  · have e1 : -WhBf β s ≤ Real.log 4 - Real.log s + 1 := le_trans (neg_le_abs _) hBf
    have e2 : -Whbf β s ≤ Real.log 2 - Real.log s + 1 := le_trans (neg_le_abs _) hbf
    linarith

lemma intervalIntegrable_Wg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t)
    (ht : t ≤ 5/6) : IntervalIntegrable (Wg β) volume (0:ℝ) t := by
  refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => Wg β s)
    (g := fun s : ℝ => 21 - 2*Real.log s) ?_ ?_ ?_
  · have h1 : IntervalIntegrable (fun s : ℝ => 21 + (-2) * Real.log s) volume (0:ℝ) t :=
      intervalIntegrable_const.add (intervalIntegrable_log'.const_mul (-2))
    convert h1 using 1
    funext s; ring
  · exact (measurable_Wg β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le ht0.le] at hx
    exact norm_Wg_le hβ0 hβ1 hx.1 (le_trans hx.2 ht)

lemma Wg_le_WK {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 5/6) :
    Wg β s ≤ WK β s := by
  have h1 : WK β s = WKcore β s := by rw [WK, WKcore, abs_of_pos hs0]
  rw [h1]
  exact WK_core_ge_Wg hβ0 hβ1 hs0 hs

lemma integral_Wg_le_WK {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a) (ha : a ≤ 5/6) :
    (∫ s in (0:ℝ)..a, Wg β s) ≤ (∫ s in (0:ℝ)..a, WK β s) := by
  refine intervalIntegral.integral_mono_ae_restrict ha0.le
    (intervalIntegrable_Wg hβ0 hβ1 ha0 ha) (intervalIntegrable_WK hβ0 hβ1 ha0 ha) ?_
  rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
  have hmeas : MeasurableSet {x : ℝ | ¬ (Wg β x ≤ WK β x)} :=
    (measurableSet_le (measurable_Wg β) (measurable_WK β)).compl
  rw [Measure.restrict_apply hmeas]
  refine measure_mono_null ?_ (measure_singleton (0:ℝ))
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc] at hx
  obtain ⟨hbad, hx0, hx1⟩ := hx
  by_contra hne
  exact hbad (Wg_le_WK hβ0 hβ1 (lt_of_le_of_ne hx0 (Ne.symm hne)) (le_trans hx1 ha))

lemma intervalIntegrable_Wg' {β p q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hp : 0 < p)
    (hpq : p ≤ q) (hq : q ≤ 5/6) : IntervalIntegrable (Wg β) volume p q := by
  refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => Wg β s)
    (g := fun s : ℝ => 21 - 2*Real.log s) ?_ ?_ ?_
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.const_mul
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [Set.uIcc_of_le hpq] at hx
    exact ne_of_gt (lt_of_lt_of_le hp hx.1)
  · exact (measurable_Wg β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le hpq] at hx
    exact norm_Wg_le hβ0 hβ1 (lt_of_lt_of_le hp hx.1.le) (le_trans hx.2 hq)

lemma WJ_shift {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha1 : 1/6 ≤ a) (ha2 : a ≤ 1/2) :
    WJ β a + WJ β (1-a) = 2*(WJ β (1/2))
      + ∫ u in a..(1/2), (Wg β (1-u) - Wg β u) := by
  have ha0 : 0 < a := by linarith
  have ha5 : a ≤ 5/6 := by linarith
  have h1a0 : 0 < 1-a := by linarith
  have h1a5 : 1-a ≤ 5/6 := by linarith
  have hh0 : (0:ℝ) < 1/2 := by norm_num
  have hh5 : (1/2:ℝ) ≤ 5/6 := by norm_num
  have hi_a : IntervalIntegrable (Wg β) volume (0:ℝ) a := intervalIntegrable_Wg hβ0 hβ1 ha0 ha5
  have hi_h : IntervalIntegrable (Wg β) volume (0:ℝ) (1/2) := intervalIntegrable_Wg hβ0 hβ1 hh0 hh5
  have hi_1a : IntervalIntegrable (Wg β) volume (0:ℝ) (1-a) := intervalIntegrable_Wg hβ0 hβ1 h1a0 h1a5
  have hi_ah : IntervalIntegrable (Wg β) volume a (1/2) :=
    intervalIntegrable_Wg' hβ0 hβ1 (by linarith) (by linarith) (by linarith)
  have hi_h1a : IntervalIntegrable (Wg β) volume (1/2) (1-a) :=
    intervalIntegrable_Wg' hβ0 hβ1 (by norm_num) (by linarith) (by linarith)
  rw [← integral_Wg hβ0 hβ1 ha0 ha5, ← integral_Wg hβ0 hβ1 hh0 hh5,
      ← integral_Wg hβ0 hβ1 h1a0 h1a5]
  have hA : (∫ u in (0:ℝ)..(1/2), Wg β u)
      = (∫ u in (0:ℝ)..a, Wg β u) + (∫ u in a..(1/2), Wg β u) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi_a hi_ah]
  have hB : (∫ u in (0:ℝ)..(1-a), Wg β u)
      = (∫ u in (0:ℝ)..(1/2), Wg β u) + (∫ u in (1/2)..(1-a), Wg β u) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi_h hi_h1a]
  have hC : (∫ u in a..(1/2), Wg β (1-u)) = (∫ u in (1/2)..(1-a), Wg β u) := by
    rw [intervalIntegral.integral_comp_sub_left (Wg β) 1]
    norm_num
  have hCii : IntervalIntegrable (fun u : ℝ => Wg β (1-u)) volume a (1/2) := by
    have hh := (hi_h1a.comp_sub_left (1:ℝ)).symm
    convert hh using 1
    · ring
    · norm_num
  have hD : (∫ u in a..(1/2), (Wg β (1-u) - Wg β u))
      = (∫ u in a..(1/2), Wg β (1-u)) - (∫ u in a..(1/2), Wg β u) :=
    intervalIntegral.integral_sub hCii hi_ah
  linarith [hA, hB, hC, hD]

/-! ## The `λ` bound -/

/-- General denominator bound. -/
lemma denom_ge {k u : ℝ} (hk : 1/2 ≤ k) :
    (k^2+1/4)^2 ≤ (k^2+u^2)*(k^2+(1-u)^2) := by
  have h : (k^2+u^2)*(k^2+(1-u)^2) - (k^2+1/4)^2
      = (u-1/2)^2 * (2*k^2 + (u-1/2)^2 - 1/2) := by ring
  have hw : (0:ℝ) ≤ (u-1/2)^2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ 2*k^2 + (u-1/2)^2 - 1/2 := by nlinarith [sq_nonneg (u-1/2), sq_nonneg k, hk]
  nlinarith [mul_nonneg hw h2]

noncomputable def WQ1 (β t : ℝ) : ℝ := (3/2-β)/((3/2-β)^2+t^2)
noncomputable def WQ2 (β t : ℝ) : ℝ := (1+β)/((1+β)^2+t^2)
noncomputable def WQ3 (β t : ℝ) : ℝ := 1/(2*((2-β)^2+t^2))
noncomputable def WQ4 (β t : ℝ) : ℝ := 1/(8*((2-β)^2+t^2)^2)
noncomputable def WQ5 (β t : ℝ) : ℝ := 1/(16*((2-β)^2+t^2)^3)

/-- Bound for the logarithmic derivative of `WTT`. -/
noncomputable def WTSt (β : ℝ) : ℝ :=
  (13/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2))
    + ((2-β)^2-β^2) * (1/(2*(((2-β)^2+1/4)^2)))
    + ((2-β)^2-β^2)^2 * (1/(2*((2-β)^5)))
    + ((2-β)^2-β^2)^3 * (3/(8*((2-β)^7)))

lemma WTT_eq (β t : ℝ) : WTT β t
    = (13/5)*(WQ1 β t + WQ2 β t) + ((2-β)^2-β^2) * WQ3 β t
      + ((2-β)^2-β^2)^2 * WQ4 β t + ((2-β)^2-β^2)^3 * WQ5 β t := by
  simp only [WTT, WQ1, WQ2, WQ3, WQ4, WQ5, div_eq_mul_inv, one_mul]

/-- Bound for the `WQ1`/`WQ2` differences. -/
lemma WQ12_diff_le {k u : ℝ} (hk : 0 < k) (hk2 : 1/2 ≤ k) (hu : u ≤ 1/2) :
    k/(k^2+u^2) - k/(k^2+(1-u)^2) ≤ (1-2*u) * (k/((k^2+1/4)^2)) := by
  have h0 : 0 ≤ 1-2*u := by linarith
  have he : k/(k^2+u^2) - k/(k^2+(1-u)^2) = (1-2*u)*(k/((k^2+u^2)*(k^2+(1-u)^2))) := by
    field_simp; ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hk.le (by positivity) (denom_ge hk2)) h0

/-- Bound for the `WQ3` difference. -/
lemma WQ3_diff_le {A u : ℝ} (hA : 0 < A) (hA2 : 1/2 ≤ A) (hu : u ≤ 1/2) :
    1/(2*(A^2+u^2)) - 1/(2*(A^2+(1-u)^2)) ≤ (1-2*u) * (1/(2*((A^2+1/4)^2))) := by
  have h0 : 0 ≤ 1-2*u := by linarith
  have he : 1/(2*(A^2+u^2)) - 1/(2*(A^2+(1-u)^2))
      = (1-2*u)*(1/(2*((A^2+u^2)*(A^2+(1-u)^2)))) := by
    field_simp; ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ h0
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := denom_ge (k := A) (u := u) hA2
  have h2 : 0 ≤ (A^2+u^2)*(A^2+(1-u)^2) := le_trans (by positivity) h
  nlinarith [h, h2]

/-- Bound for the `WQ4` difference. -/
lemma WQ4_diff_le {A u : ℝ} (hA : 0 < A) (hA1 : 1 ≤ A) (hu0 : 0 ≤ u) (hu : u ≤ 1/2) :
    1/(8*(A^2+u^2)^2) - 1/(8*(A^2+(1-u)^2)^2) ≤ (1-2*u) * (1/(2*A^5)) := by
  have h0 : 0 ≤ 1-2*u := by linarith
  have he : 1/(8*(A^2+u^2)^2) - 1/(8*(A^2+(1-u)^2)^2)
      = (1-2*u)*((2*A^2+u^2+(1-u)^2)/(8*((A^2+u^2)^2*(A^2+(1-u)^2)^2))) := by
    field_simp; ring
  rw [he]
  have hnum : 2*A^2+u^2+(1-u)^2 ≤ 2*A^2+1 := by nlinarith [sq_nonneg (2*u-1), hu0, hu]
  have hden : (A^2+1/4)^4 ≤ (A^2+u^2)^2*(A^2+(1-u)^2)^2 := by
    have h := denom_ge (k := A) (u := u) (by linarith)
    have h2 : 0 ≤ (A^2+u^2)*(A^2+(1-u)^2) := le_trans (by positivity) h
    nlinarith [h, h2]
  apply mul_le_mul_of_nonneg_left _ h0
  have h1 : (2*A^2+u^2+(1-u)^2)/(8*((A^2+u^2)^2*(A^2+(1-u)^2)^2)) ≤ (2*A^2+1)/(8*(A^2+1/4)^4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hs1 : (2*A^2+u^2+(1-u)^2)*(A^2+1/4)^4 ≤ (2*A^2+1)*(A^2+1/4)^4 :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    have hs2 : (2*A^2+1)*((A^2+1/4)^4) ≤ (2*A^2+1)*((A^2+u^2)^2*(A^2+(1-u)^2)^2) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    nlinarith [hs1, hs2]
  have h2 : (2*A^2+1)/(8*(A^2+1/4)^4) ≤ 1/(2*A^5) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hid : 4*(A^2+1/4)^4 - (2*A^2+1)*A^5
        = 2*A^7*(2*A-1) + A^5*(4*A-1) + (3/2)*A^4 + (1/4)*A^2 + 1/64 := by ring
    have e1 : 0 ≤ 2*A^7*(2*A-1) := mul_nonneg (by positivity) (by linarith)
    have e2 : 0 ≤ A^5*(4*A-1) := mul_nonneg (by positivity) (by linarith)
    have e3 : 0 ≤ (3/2)*A^4 := by positivity
    have e4 : 0 ≤ (1/4)*A^2 := by positivity
    linarith [hid, e1, e2, e3, e4]
  linarith

/-- Bound for the `WQ5` difference. -/
lemma WQ5_diff_le {A u : ℝ} (hA : 0 < A) (hA1 : 1 ≤ A) (hu0 : 0 ≤ u) (hu : u ≤ 1/2) :
    1/(16*(A^2+u^2)^3) - 1/(16*(A^2+(1-u)^2)^3) ≤ (1-2*u) * (3/(8*A^7)) := by
  have h0 : 0 ≤ 1-2*u := by linarith
  have he : 1/(16*(A^2+u^2)^3) - 1/(16*(A^2+(1-u)^2)^3)
      = (1-2*u)*(((A^2+(1-u)^2)^2 + (A^2+(1-u)^2)*(A^2+u^2) + (A^2+u^2)^2)
          /(16*((A^2+u^2)^3*(A^2+(1-u)^2)^3))) := by
    field_simp; ring
  rw [he]
  have hxy : (A^2+1/4)^2 ≤ (A^2+(1-u)^2)*(A^2+u^2) := by
    have h := denom_ge (k := A) (u := u) (by linarith)
    linarith [h, mul_comm (A^2+u^2) (A^2+(1-u)^2)]
  have hb1 : A^2+(1-u)^2 ≤ A^2+1 := by nlinarith [sq_nonneg u]
  have hb2 : A^2+u^2 ≤ A^2+1 := by nlinarith [sq_nonneg (1-u), hu0, hu]
  have hnum : (A^2+(1-u)^2)^2 + (A^2+(1-u)^2)*(A^2+u^2) + (A^2+u^2)^2 ≤ 3*(A^2+1)^2 := by
    have h1 : (A^2+(1-u)^2)^2 ≤ (A^2+1)^2 := by nlinarith [hb1, sq_nonneg (A^2+(1-u)^2), sq_nonneg (A^2+1)]
    have h2 : (A^2+(1-u)^2)*(A^2+u^2) ≤ (A^2+1)^2 :=
      by nlinarith [mul_le_mul hb1 hb2 (by positivity) (by positivity), sq_nonneg (A^2+1)]
    have h3 : (A^2+u^2)^2 ≤ (A^2+1)^2 := by nlinarith [hb2, sq_nonneg (A^2+u^2), sq_nonneg (A^2+1)]
    linarith
  have hden : (A^2+1/4)^6 ≤ (A^2+u^2)^3*(A^2+(1-u)^2)^3 := by
    have h : ((A^2+1/4)^2)^3 ≤ ((A^2+(1-u)^2)*(A^2+u^2))^3 :=
      pow_le_pow_left₀ (by positivity) hxy 3
    nlinarith [h]
  apply mul_le_mul_of_nonneg_left _ h0
  have h1 : ((A^2+(1-u)^2)^2 + (A^2+(1-u)^2)*(A^2+u^2) + (A^2+u^2)^2)
      /(16*((A^2+u^2)^3*(A^2+(1-u)^2)^3)) ≤ 3*(A^2+1)^2/(16*(A^2+1/4)^6) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hs1 : ((A^2+(1-u)^2)^2 + (A^2+(1-u)^2)*(A^2+u^2) + (A^2+u^2)^2)*((A^2+1/4)^6)
        ≤ 3*(A^2+1)^2*((A^2+1/4)^6) := mul_le_mul_of_nonneg_right hnum (by positivity)
    have hs2 : 3*(A^2+1)^2*((A^2+1/4)^6) ≤ 3*(A^2+1)^2*((A^2+u^2)^3*(A^2+(1-u)^2)^3) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    nlinarith [hs1, hs2]
  have h2 : 3*(A^2+1)^2/(16*(A^2+1/4)^6) ≤ 3/(8*A^7) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hid : 2*(A^2+1/4)^6 - (A^2+1)^2*A^7
        = A^11*(2*A-1) + A^9*(3*A-2) + A^7*((15/8)*A-1) + (5/8)*A^6 + (15/128)*A^4 + (3/256)*A^2 + 1/2048 := by ring
    have e1 : 0 ≤ A^11*(2*A-1) := mul_nonneg (by positivity) (by linarith)
    have e2 : 0 ≤ A^9*(3*A-2) := mul_nonneg (by positivity) (by linarith)
    have e3 : 0 ≤ A^7*((15/8)*A-1) := mul_nonneg (by positivity) (by linarith)
    have e4 : 0 ≤ (5/8)*A^6 := by positivity
    have e5 : 0 ≤ (15/128)*A^4 := by positivity
    have e6 : 0 ≤ (3/256)*A^2 := by positivity
    linarith [hid, e1, e2, e3, e4, e5, e6]
  linarith

lemma TT_diff_le {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) :
    WTT β u - WTT β (1-u) ≤ (1-2*u) * WTSt β := by
  have h0 : 0 ≤ 1-2*u := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hk1 : (0:ℝ) < 3/2-β := by linarith
  have hk1b : (1:ℝ)/2 ≤ 3/2-β := by linarith
  have hk2 : (0:ℝ) < 1+β := by linarith
  have hk2b : (1:ℝ)/2 ≤ 1+β := by linarith
  have hA : (1:ℝ) ≤ 2-β := by linarith
  have hA0 : (0:ℝ) < 2-β := by linarith
  have hc : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith [hβ0, hβ1]
  have hT : WTT β u - WTT β (1-u)
      = (13/5)*(WQ1 β u - WQ1 β (1-u)) + (13/5)*(WQ2 β u - WQ2 β (1-u))
        + ((2-β)^2-β^2)*(WQ3 β u - WQ3 β (1-u))
        + ((2-β)^2-β^2)^2*(WQ4 β u - WQ4 β (1-u))
        + ((2-β)^2-β^2)^3*(WQ5 β u - WQ5 β (1-u)) := by
    rw [WTT_eq, WTT_eq]; ring
  have b1 : WQ1 β u - WQ1 β (1-u) ≤ (1-2*u) * ((3/2-β)/(((3/2-β)^2+1/4)^2)) := by
    simp only [WQ1]; exact WQ12_diff_le hk1 hk1b hu2
  have b2 : WQ2 β u - WQ2 β (1-u) ≤ (1-2*u) * ((1+β)/(((1+β)^2+1/4)^2)) := by
    simp only [WQ2]; exact WQ12_diff_le hk2 hk2b hu2
  have b3 : WQ3 β u - WQ3 β (1-u) ≤ (1-2*u) * (1/(2*(((2-β)^2+1/4)^2))) := by
    simp only [WQ3]; exact WQ3_diff_le hA0 (by linarith) hu2
  have b4 : WQ4 β u - WQ4 β (1-u) ≤ (1-2*u) * (1/(2*((2-β)^5))) := by
    simp only [WQ4]; exact WQ4_diff_le hA0 hA hu0 hu2
  have b5 : WQ5 β u - WQ5 β (1-u) ≤ (1-2*u) * (3/(8*((2-β)^7))) := by
    simp only [WQ5]; exact WQ5_diff_le hA0 hA hu0 hu2
  have e1 := mul_le_mul_of_nonneg_left b1 (by norm_num : (0:ℝ) ≤ 13/5)
  have e2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0:ℝ) ≤ 13/5)
  have e3 := mul_le_mul_of_nonneg_left b3 hc
  have e4 := mul_le_mul_of_nonneg_left b4 (sq_nonneg ((2-β)^2-β^2))
  have e5 := mul_le_mul_of_nonneg_left b5 (by positivity : (0:ℝ) ≤ ((2-β)^2-β^2)^3)
  rw [hT, WTSt]
  linarith [e1, e2, e3, e4, e5]

open Set

/-- `arctan y ≤ y` for `y ≥ 0`. -/
lemma arctan_le_self {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  rcases lt_or_ge y (Real.pi/2) with h | h
  · calc Real.arctan y ≤ Real.arctan (Real.tan y) :=
          Real.arctan_le_arctan_iff.mpr (Real.le_tan hy h)
      _ = y := Real.arctan_tan (by linarith [Real.pi_pos]) h
  · exact le_trans (le_of_lt (Real.arctan_lt_pi_div_two y)) h

/-- `π/4 - (1-x)/(1+x) ≤ arctan x` for `0 ≤ x ≤ 1`. -/
lemma arctan_ge_pi_div_four_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.pi/4 - (1-x)/(1+x) ≤ Real.arctan x := by
  have hxp : (0:ℝ) < 1 + x := by linarith
  set z : ℝ := (1-x)/(1+x) with hz
  have hxz : x * z < 1 := by
    have hkey : 1 - x*z = (1+x^2)/(1+x) := by rw [hz]; field_simp; ring
    have : 0 < 1 - x*z := by rw [hkey]; positivity
    linarith
  have hsum : (x + z)/(1 - x*z) = 1 := by
    have hden : (1:ℝ) - x*z ≠ 0 := by linarith
    rw [div_eq_iff hden, one_mul]
    rw [hz]
    field_simp
    ring
  have hadd := Real.arctan_add (x := x) (y := z) hxz
  rw [hsum, Real.arctan_one] at hadd
  have h2 : Real.arctan z ≤ z := arctan_le_self (by rw [hz]; apply div_nonneg <;> linarith)
  linarith

lemma hasDerivAt_S5 {x : ℝ} :
    HasDerivAt (fun z : ℝ => z + z^3/3 + z^5/5 + z^7/7 + z^9/9 + z^11/11)
      (1 + x^2 + x^4 + x^6 + x^8 + x^10) x := by
  have h3 : HasDerivAt (fun z : ℝ => z^3) (3*x^2) x := by simpa using (hasDerivAt_pow 3 x)
  have h5 : HasDerivAt (fun z : ℝ => z^5) (5*x^4) x := by simpa using (hasDerivAt_pow 5 x)
  have h7 : HasDerivAt (fun z : ℝ => z^7) (7*x^6) x := by simpa using (hasDerivAt_pow 7 x)
  have h9 : HasDerivAt (fun z : ℝ => z^9) (9*x^8) x := by simpa using (hasDerivAt_pow 9 x)
  have h11 : HasDerivAt (fun z : ℝ => z^11) (11*x^10) x := by simpa using (hasDerivAt_pow 11 x)
  have h := (((((hasDerivAt_id x).add (h3.div_const 3)).add (h5.div_const 5)).add
    (h7.div_const 7)).add (h9.div_const 9)).add (h11.div_const 11)
  apply h.congr_deriv
  ring

lemma hasDerivAt_S3 {x : ℝ} :
    HasDerivAt (fun z : ℝ => z + z^3/3 + z^5/5) (1 + x^2 + x^4) x := by
  have h3 : HasDerivAt (fun z : ℝ => z^3) (3*x^2) x := by simpa using (hasDerivAt_pow 3 x)
  have h5 : HasDerivAt (fun z : ℝ => z^5) (5*x^4) x := by simpa using (hasDerivAt_pow 5 x)
  have h := ((hasDerivAt_id x).add (h3.div_const 3)).add (h5.div_const 5)
  apply h.congr_deriv
  ring

lemma continuousOn_S5 (a b : ℝ) :
    ContinuousOn (fun z : ℝ => z + z^3/3 + z^5/5 + z^7/7 + z^9/9 + z^11/11) (Icc a b) := by
  fun_prop

lemma hasDerivAt_atanh {u : ℝ} (hu0 : -1 < u) (hu : u < 1) :
    HasDerivAt (fun z : ℝ => (1/2)*Real.log ((1+z)/(1-z))) (1/(1-u^2)) u := by
  have h1 : (1:ℝ) - u ≠ 0 := by linarith
  have h1p : (1:ℝ) + u ≠ 0 := by linarith
  have hq : (1:ℝ) - u^2 ≠ 0 := by nlinarith
  have hinner : HasDerivAt (fun z : ℝ => (1+z)/(1-z)) (2/(1-u)^2) u := by
    have h := ((hasDerivAt_const u 1).add (hasDerivAt_id u)).div
      ((hasDerivAt_const u 1).sub (hasDerivAt_id u)) h1
    apply h.congr_deriv
    simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    ring
  have hlog : HasDerivAt (fun z : ℝ => Real.log ((1+z)/(1-z)))
      ((2/(1-u)^2) / ((1+u)/(1-u))) u :=
    hinner.log (by apply div_ne_zero <;> linarith)
  have hlog' : HasDerivAt (fun z : ℝ => Real.log ((1+z)/(1-z))) (1/(1+u) + 1/(1-u)) u := by
    rw [show (2 / (1 - u) ^ 2) / ((1 + u) / (1 - u)) = 1 / (1 + u) + 1 / (1 - u) by
      field_simp; ring] at hlog
    exact hlog
  have h2 : HasDerivAt (fun z : ℝ => (1/2)*Real.log ((1+z)/(1-z)))
      ((1/2)*(1/(1+u) + 1/(1-u))) u := hlog'.const_mul (1/2)
  apply h2.congr_deriv
  field_simp
  ring

lemma continuousOn_atanh_Icc {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    ContinuousOn (fun z : ℝ => (1/2)*Real.log ((1+z)/(1-z))) (Icc a b) := by
  apply ContinuousOn.const_mul
  apply ContinuousOn.log
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro z hz; linarith [hz.2]
  · intro z hz
    have h1 : (0:ℝ) < 1 - z := by linarith [hz.2]
    have h2 : (0:ℝ) < 1 + z := by linarith [hz.1]
    positivity

/-- `atanh u ≤ u + u^3/3 + ... + u^11/11` for `u ≤ 0`. -/
lemma atanh_le_series_neg {u : ℝ} (hu0 : -1 < u) (hu : u ≤ 0) :
    (1/2)*Real.log ((1+u)/(1-u))
      ≤ u + u^3/3 + u^5/5 + u^7/7 + u^9/9 + u^11/11 := by
  have h1 : (1:ℝ) - u ≠ 0 := by linarith
  have hq : (1:ℝ) - u^2 ≠ 0 := by nlinarith
  set F : ℝ → ℝ := fun z => z + z^3/3 + z^5/5 + z^7/7 + z^9/9 + z^11/11
    - (1/2)*Real.log ((1+z)/(1-z)) with hF
  have hderiv : ∀ x ∈ interior (Icc u 0), deriv F x = -(x^12/(1-x^2)) := by
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : x < 1 := by linarith [hx.2]
    have hxq : (1:ℝ) - x^2 ≠ 0 := by nlinarith [hx.1, hx.2]
    have hd : HasDerivAt F (-(x^12/(1-x^2))) x := by
      rw [hF]
      have h := (hasDerivAt_S5 (x := x)).sub (hasDerivAt_atanh (by linarith [hx.1]) hx1)
      apply h.congr_deriv
      field_simp
      ring
    exact hd.deriv
  have hmono : AntitoneOn F (Icc u 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc u 0)
    · rw [hF]
      exact (continuousOn_S5 u 0).sub (continuousOn_atanh_Icc hu0 (by norm_num))
    · intro x hx
      rw [hF]
      exact ((hasDerivAt_S5 (x := x)).sub
        (hasDerivAt_atanh (by rw [interior_Icc] at hx; linarith [hx.1])
          (by rw [interior_Icc] at hx; linarith [hx.2]))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [hderiv x hx]
      rw [interior_Icc] at hx
      have hxq : (0:ℝ) < 1 - x^2 := by nlinarith [hx.1, hx.2]
      exact neg_nonpos.mpr (div_nonneg (by positivity) (le_of_lt hxq))
  have hF0 : F 0 = 0 := by simp [hF]
  have hfu := hmono (left_mem_Icc.mpr hu) (right_mem_Icc.mpr hu) hu
  rw [hF0] at hfu
  rw [hF] at hfu
  simp only at hfu
  linarith [hfu]

end

section
open Set

/-- `atanh u ≤ u + u^3/3 + ... + u^11/11 + u^13/(13(1-u^2))` for `u ≥ 0`. -/
lemma atanh_le_series_pos {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1/3) :
    (1/2)*Real.log ((1+u)/(1-u))
      ≤ u + u^3/3 + u^5/5 + u^7/7 + u^9/9 + u^11/11 + u^13/(13*(1-u^2)) := by
  have hm1 : (-1:ℝ) < u := by linarith
  have h1 : (1:ℝ) - u ≠ 0 := by linarith
  have hq : (1:ℝ) - u^2 ≠ 0 := by nlinarith
  set F : ℝ → ℝ := fun z => z + z^3/3 + z^5/5 + z^7/7 + z^9/9 + z^11/11 + z^13/(13*(1-z^2))
    - (1/2)*Real.log ((1+z)/(1-z)) with hF
  have hderiv : ∀ x ∈ interior (Icc 0 u), deriv F x = 2*x^14/(13*(1-x^2)^2) := by
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : x < 1 := by linarith [hx.2, hu]
    have hxq : (1:ℝ) - x^2 ≠ 0 := by nlinarith [hx.1, hx.2, hu]
    have hd : HasDerivAt F (2*x^14/(13*(1-x^2)^2)) x := by
      rw [hF]
      have hS := hasDerivAt_S5 (x := x)
      have h13 : HasDerivAt (fun z : ℝ => z^13/(13*(1-z^2)))
          ((13*x^12*(13*(1-x^2)) - x^13*(13*(-2*x)))/(13*(1-x^2))^2) x := by
        have ha : HasDerivAt (fun z : ℝ => z^13) (13*x^12) x := by simpa using (hasDerivAt_pow 13 x)
        have hb : HasDerivAt (fun z : ℝ => 13*(1-z^2)) (13*(-2*x)) x := by
          have h2 : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by simpa using (hasDerivAt_pow 2 x)
          have := ((hasDerivAt_const x 13).mul ((hasDerivAt_const x 1).sub h2))
          apply this.congr_deriv
          ring
        exact ha.div hb (by positivity)
      have h := (hS.add h13).sub (hasDerivAt_atanh (by linarith [hx.1]) hx1)
      apply h.congr_deriv
      field_simp
      ring
    exact hd.deriv
  have hmono : MonotoneOn F (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · rw [hF]
      apply ContinuousOn.sub
      · apply ContinuousOn.add
        · exact continuousOn_S5 0 u
        · apply ContinuousOn.div
          · fun_prop
          · fun_prop
          · intro x hx
            have hx1 : (0:ℝ) < 1 - x^2 := by nlinarith [hx.1, hx.2, hu]
            positivity
      · exact continuousOn_atanh_Icc (by norm_num : (-1:ℝ) < 0) (by linarith : u < 1)
    · intro x hx
      rw [hF]
      have hx' : x ∈ Ioo (0:ℝ) u := by rw [interior_Icc] at hx; exact hx
      have hx1 : x < 1 := by linarith [hx'.2, hu]
      have hxq : (1:ℝ) - x^2 ≠ 0 := by nlinarith [hx'.1, hx'.2, hu]
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.sub
      · apply DifferentiableAt.add
        · fun_prop
        · apply DifferentiableAt.div
          · fun_prop
          · fun_prop
          · exact mul_ne_zero (by norm_num) hxq
      · exact (hasDerivAt_atanh (by linarith [hx'.1]) hx1).differentiableAt
    · intro x hx
      rw [hderiv x hx]
      rw [interior_Icc] at hx
      have hxq : (0:ℝ) < 1 - x^2 := by nlinarith [hx.1, hx.2, hu]
      positivity
  have hF0 : F 0 = 0 := by simp [hF]
  have hfu := hmono (left_mem_Icc.mpr hu0) (right_mem_Icc.mpr hu0) hu0
  rw [hF0] at hfu
  rw [hF] at hfu
  simp only at hfu
  linarith [hfu]

/-- `u + u^3/3 + u^5/5 ≤ atanh u` for `0 ≤ u ≤ 2/3`. -/
lemma series3_le_atanh {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2/3) :
    u + u^3/3 + u^5/5 ≤ (1/2)*Real.log ((1+u)/(1-u)) := by
  have hm1 : (-1:ℝ) < u := by linarith
  have h1 : (1:ℝ) - u ≠ 0 := by linarith
  have hq : (1:ℝ) - u^2 ≠ 0 := by nlinarith
  set F : ℝ → ℝ := fun z => (1/2)*Real.log ((1+z)/(1-z)) - (z + z^3/3 + z^5/5) with hF
  have hderiv : ∀ x ∈ interior (Icc 0 u), deriv F x = x^6/(1-x^2) := by
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : x < 1 := by linarith [hx.2, hu]
    have hxq : (1:ℝ) - x^2 ≠ 0 := by nlinarith [hx.1, hx.2, hu]
    have hd : HasDerivAt F (x^6/(1-x^2)) x := by
      rw [hF]
      have h := (hasDerivAt_atanh (by linarith [hx.1]) hx1).sub (hasDerivAt_S3 (x := x))
      apply h.congr_deriv
      field_simp
      ring
    exact hd.deriv
  have hmono : MonotoneOn F (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · rw [hF]
      exact (continuousOn_atanh_Icc (by norm_num : (-1:ℝ) < 0) (by linarith : u < 1)).sub
        (by fun_prop)
    · intro x hx
      rw [hF]
      have hx' : x ∈ Ioo (0:ℝ) u := by rw [interior_Icc] at hx; exact hx
      have hx1 : x < 1 := by linarith [hx'.2, hu]
      apply DifferentiableAt.differentiableWithinAt
      exact ((hasDerivAt_atanh (by linarith [hx'.1]) hx1).sub (hasDerivAt_S3 (x := x))).differentiableAt
    · intro x hx
      rw [hderiv x hx]
      rw [interior_Icc] at hx
      have hxq : (0:ℝ) < 1 - x^2 := by nlinarith [hx.1, hx.2, hu]
      positivity
  have hF0 : F 0 = 0 := by simp [hF]
  have hfu := hmono (left_mem_Icc.mpr hu0) (right_mem_Icc.mpr hu0) hu0
  rw [hF0] at hfu
  rw [hF] at hfu
  simp only at hfu
  linarith [hfu]

end

section
open Set

/-- Upper bound for `log (1+y)` when `y ≤ 0`. -/
lemma log_one_add_le_neg {y : ℝ} (h1 : -(5:ℝ)/6 ≤ y) (h2 : y ≤ 0) :
    Real.log (1 + y) ≤ 2 * ((y/(2+y)) + (y/(2+y))^3/3 + (y/(2+y))^5/5 + (y/(2+y))^7/7
      + (y/(2+y))^9/9 + (y/(2+y))^11/11) := by
  have hy : (0:ℝ) < 2 + y := by linarith
  have hnum : 0 ≤ -y := by linarith
  have hu0 : y/(2+y) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hy)
  have hu1 : -1 < y/(2+y) := by
    rw [lt_div_iff₀ hy]; linarith
  have hkey : (1 + y/(2+y))/(1 - y/(2+y)) = 1 + y := by
    field_simp
    ring
  have h := atanh_le_series_neg hu1 hu0
  rw [hkey] at h
  linarith [h]

/-- Upper bound for `log (1+y)` when `y ≥ 0`. -/
lemma log_one_add_le_pos {y : ℝ} (h1 : 0 ≤ y) (h2 : y ≤ 1) :
    Real.log (1 + y) ≤ 2 * ((y/(2+y)) + (y/(2+y))^3/3 + (y/(2+y))^5/5 + (y/(2+y))^7/7
      + (y/(2+y))^9/9 + (y/(2+y))^11/11 + (y/(2+y))^13/(13*(1-(y/(2+y))^2))) := by
  have hy : (0:ℝ) < 2 + y := by linarith
  have hu0 : 0 ≤ y/(2+y) := div_nonneg h1 (le_of_lt hy)
  have hu1 : y/(2+y) ≤ 1/3 := by
    rw [div_le_iff₀ hy]; linarith
  have hkey : (1 + y/(2+y))/(1 - y/(2+y)) = 1 + y := by
    field_simp
    ring
  have h := atanh_le_series_pos hu0 hu1
  rw [hkey] at h
  linarith [h]

lemma WK_split {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha1 : 1/6 ≤ a) (ha2 : a ≤ 1/2) :
    (∫ s in (-a)..(1-a), WK β s)
      = (∫ s in (0:ℝ)..a, WK β s) + (∫ s in (0:ℝ)..(1-a), WK β s) := by
  have ha0 : 0 < a := by linarith
  have h1a0 : 0 < 1-a := by linarith
  have h1a5 : 1-a ≤ 5/6 := by linarith
  have ha5 : a ≤ 5/6 := by linarith
  have hi1 : IntervalIntegrable (WK β) volume (-a) 0 := intervalIntegrable_WK_neg hβ0 hβ1 ha0 ha5
  have hi2 : IntervalIntegrable (WK β) volume (0:ℝ) (1-a) := intervalIntegrable_WK hβ0 hβ1 h1a0 h1a5
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  congr 1
  have hcomp := intervalIntegral.integral_comp_neg (f := WK β) (a := (0:ℝ)) (b := a)
  simp only [neg_zero] at hcomp
  rw [← hcomp]
  apply intervalIntegral.integral_congr
  intro x _
  exact WK_neg β x


/-! ## Pointwise bounds for the difference `Wg u - Wg (1-u)` -/

noncomputable def C1 (β : ℝ) : ℝ := WTSt β + 1/(4*(2-β)^2)

noncomputable def FI (β u : ℝ) : ℝ :=
  (1-2*u)*(C1 β + 1/(4*β^2)) + 2*Real.log u - 2*Real.log (1-u)

noncomputable def FIII (β u : ℝ) : ℝ :=
  (1-2*u)*(C1 β) + 2*Real.log u - Real.log (1-u) - Real.log (2*β) + β/(1-u) - u^2/(4*β^2)

noncomputable def FIV (β u : ℝ) : ℝ :=
  (1-2*u)*(C1 β) + Real.log u - Real.log (1-u) + (β/(1-u) - β/u)

/-- Case I: `u ≤ β` and `1-u ≤ β`. -/
lemma Wg_diff_le_I {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) (huβ : u ≤ β) (h1uβ : 1-u ≤ β) :
    Wg β u - Wg β (1-u) ≤ FI β u := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u0 : (0:ℝ) < 1-u := by linarith
  have h0 : 0 ≤ 1-2*u := by linarith
  have hA : (0:ℝ) < 2-β := by linarith
  have hmain : Wg β u - Wg β (1-u)
      = (WTT β u - WTT β (1-u)) + (Real.log u - Real.log (1-u) + ((1-u)^2-u^2)/(4*(2-β)^2))
        + (Real.log u - Real.log (1-u) + ((1-u)^2-u^2)/(4*β^2)) := by
    simp only [Wg, WhBf, Whbf]
    rw [if_pos huβ, if_pos h1uβ]
    ring
  have hTT := TT_diff_le hβ0 hβ1 hu1 hu2
  have e1 : (1-u)^2 - u^2 = (1-2*u) := by ring
  rw [hmain, e1]
  simp only [FI]
  have hC : (1-2*u)*(C1 β + 1/(4*β^2)) = (1-2*u)*C1 β + (1-2*u)/(4*β^2) := by ring
  have hC2 : (1-2*u)*(WTSt β + 1/(4*(2-β)^2)) = (1-2*u)*WTSt β + (1-2*u)/(4*(2-β)^2) := by ring
  rw [hC, show C1 β = WTSt β + 1/(4*(2-β)^2) from rfl, hC2]
  linarith [hTT]

/-- Case III: `u ≤ β` and `β < 1-u`. -/
lemma Wg_diff_le_III {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) (huβ : u ≤ β) (h1uβ : β < 1-u) :
    Wg β u - Wg β (1-u) ≤ FIII β u := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u0 : (0:ℝ) < 1-u := by linarith
  have h0 : 0 ≤ 1-2*u := by linarith
  have hA : (0:ℝ) < 2-β := by linarith
  have hnb : ¬ (1-u ≤ β) := by linarith
  have hmain : Wg β u - Wg β (1-u)
      = (WTT β u - WTT β (1-u)) + (Real.log u - Real.log (1-u) + ((1-u)^2-u^2)/(4*(2-β)^2))
        + (Real.log u + β/(1-u) - Real.log (2*β) - u^2/(4*β^2)) := by
    simp only [Wg, WhBf, Whbf]
    rw [if_pos huβ, if_neg hnb]
    ring
  have hTT := TT_diff_le hβ0 hβ1 hu1 hu2
  have e1 : (1-u)^2 - u^2 = (1-2*u) := by ring
  rw [hmain, e1]
  simp only [FIII]
  have hC2 : (1-2*u)*(WTSt β + 1/(4*(2-β)^2)) = (1-2*u)*WTSt β + (1-2*u)/(4*(2-β)^2) := by ring
  rw [show C1 β = WTSt β + 1/(4*(2-β)^2) from rfl, hC2]
  linarith [hTT]

/-- Case IV: `β < u` and `β < 1-u`. -/
lemma Wg_diff_le_IV {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) (huβ : β < u) (h1uβ : β < 1-u) :
    Wg β u - Wg β (1-u) ≤ FIV β u := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u0 : (0:ℝ) < 1-u := by linarith
  have h0 : 0 ≤ 1-2*u := by linarith
  have hA : (0:ℝ) < 2-β := by linarith
  have hnb : ¬ (u ≤ β) := by linarith
  have hnb' : ¬ (1-u ≤ β) := by linarith
  have hmain : Wg β u - Wg β (1-u)
      = (WTT β u - WTT β (1-u)) + (Real.log u - Real.log (1-u) + ((1-u)^2-u^2)/(4*(2-β)^2))
        + (β/(1-u) - β/u) := by
    simp only [Wg, WhBf, Whbf]
    rw [if_neg hnb, if_neg hnb']
    ring
  have hTT := TT_diff_le hβ0 hβ1 hu1 hu2
  have e1 : (1-u)^2 - u^2 = (1-2*u) := by ring
  rw [hmain, e1]
  simp only [FIV]
  have hC2 : (1-2*u)*(WTSt β + 1/(4*(2-β)^2)) = (1-2*u)*WTSt β + (1-2*u)/(4*(2-β)^2) := by ring
  rw [show C1 β = WTSt β + 1/(4*(2-β)^2) from rfl, hC2]
  linarith [hTT]

/-! ## A uniform lower bound for `C1` -/

/-- Elementary rational bound: `g` is decreasing on `[1,3/2]` (specific instances). -/
lemma g_antitone {k k' : ℝ} (hk' : 2/3 ≤ k') (hkk' : k' ≤ k) (hk : k ≤ 3/2) :
    k/(k^2+1/4)^2 ≤ k'/(k'^2+1/4)^2 := by
  have h1 : (0:ℝ) < k'^2+1/4 := by nlinarith [sq_nonneg k']
  have h2 : (0:ℝ) < k^2+1/4 := by nlinarith [sq_nonneg k]
  have h1s : (0:ℝ) < (k'^2+1/4)^2 := pow_pos h1 2
  have h2s : (0:ℝ) < (k^2+1/4)^2 := pow_pos h2 2
  rw [div_le_div_iff₀ h2s h1s]
  have key : k'*(k^2+1/4)^2 - k*(k'^2+1/4)^2
      = (k-k')*(k*k'*(k^2+k*k'+k'^2) + k*k'/2 - 1/16) := by ring
  have h3 : 0 ≤ k - k' := by linarith
  have hkk : 4/9 ≤ k*k' := by nlinarith
  have hsum : 4/3 ≤ k^2+k*k'+k'^2 := by nlinarith
  have h4 : 0 ≤ k*k'*(k^2+k*k'+k'^2) + k*k'/2 - 1/16 := by
    have h5 : (4/9)*(4/3) ≤ (k*k')*(k^2+k*k'+k'^2) := by
      apply mul_le_mul hkk hsum ; norm_num ; linarith
    have h6 : (0:ℝ) ≤ k*k'/2 := by positivity
    linarith
  have := mul_nonneg h3 h4
  linarith [key, this]

/-- `3/2 ≤ C1 β` for `β ∈ [1/6,5/6]`. -/
lemma C1_ge {β : ℝ} (h1 : 1/6 ≤ β) (h2 : β ≤ 5/6) : 3/2 ≤ C1 β := by
  have hA : (0:ℝ) < 2-β := by linarith
  have hk1 : (0:ℝ) < 3/2-β := by linarith
  have hk2 : (0:ℝ) < 1+β := by linarith
  have hCpos : (0:ℝ) < (2-β)^2-β^2 := by
    rw [show (2-β)^2-β^2 = 4*(1-β) by ring]; linarith
  have hterm : 0 ≤ ((2-β)^2-β^2) * (1/(2*(((2-β)^2+1/4)^2))) := by
    apply mul_nonneg hCpos.le; positivity
  have hterm2 : 0 ≤ ((2-β)^2-β^2)^2 * (1/(2*((2-β)^5))) := by
    apply mul_nonneg (sq_nonneg _); positivity
  have hterm3 : 0 ≤ ((2-β)^2-β^2)^3 * (3/(8*((2-β)^7))) := by
    apply mul_nonneg (pow_nonneg hCpos.le 3); positivity
  have hbase : (13/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)) ≤ WTSt β := by
    simp only [WTSt]
    linarith [hterm, hterm2, hterm3]
  by_cases hb : β ≤ 1/3
  · -- β ∈ [1/6,1/3]: both k1, k2 ∈ [7/6,4/3]
    have hk1' : 1 ≤ 3/2-β := by linarith
    have hk1'' : 3/2-β ≤ 4/3 := by linarith
    have hk2' : 1 ≤ 1+β := by linarith
    have hk2'' : 1+β ≤ 4/3 := by linarith
    have hk1a : (2:ℝ)/3 ≤ 3/2-β := by linarith
    have hk1b : 3/2-β ≤ 4/3 := by linarith
    have hk2a : (2:ℝ)/3 ≤ 1+β := by linarith
    have hk2b : 1+β ≤ 4/3 := by linarith
    have e1 : (4/3)/((4/3)^2+1/4)^2 ≤ (3/2-β)/(((3/2-β)^2+1/4)^2) :=
      g_antitone (k := 4/3) (k' := 3/2-β) hk1a hk1b (by norm_num)
    have e2 : (4/3)/((4/3)^2+1/4)^2 ≤ (1+β)/(((1+β)^2+1/4)^2) :=
      g_antitone (k := 4/3) (k' := 1+β) hk2a hk2b (by norm_num)
    have hnum : (3:ℝ)/2 ≤ (13/5)*((4/3)/((4/3)^2+1/4)^2 + (4/3)/((4/3)^2+1/4)^2) := by norm_num
    have hsum : (4/3)/((4/3)^2+1/4)^2 + (4/3)/((4/3)^2+1/4)^2
        ≤ (3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2) := by linarith [e1, e2]
    have := le_trans hnum (by nlinarith [hsum] : (13/5)*((4/3)/((4/3)^2+1/4)^2 + (4/3)/((4/3)^2+1/4)^2)
      ≤ (13/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)))
    have hC1 : C1 β = WTSt β + 1/(4*(2-β)^2) := rfl
    rw [hC1]
    have : (0:ℝ) < 1/(4*(2-β)^2) := by positivity
    linarith [hbase, this]
  · -- β ∈ (1/3,5/6]
    by_cases hb2 : β ≤ 1/2
    · -- k1 ∈ [1,7/6], k2 ∈ [4/3,3/2]
      have hk1' : 1 ≤ 3/2-β := by linarith
      have hk1'' : 3/2-β ≤ 7/6 := by linarith
      have hk2' : 4/3 ≤ 1+β := by linarith
      have hk2'' : 1+β ≤ 3/2 := by linarith
      have hk1a : (2:ℝ)/3 ≤ 3/2-β := by linarith
      have hk1b : 3/2-β ≤ 7/6 := by linarith
      have hk2a : (2:ℝ)/3 ≤ 1+β := by linarith
      have hk2b : 1+β ≤ 3/2 := by linarith
      have e1 : (7/6)/((7/6)^2+1/4)^2 ≤ (3/2-β)/(((3/2-β)^2+1/4)^2) :=
        g_antitone (k := 7/6) (k' := 3/2-β) hk1a hk1b (by norm_num)
      have e2 : (3/2)/((3/2)^2+1/4)^2 ≤ (1+β)/(((1+β)^2+1/4)^2) :=
        g_antitone (k := 3/2) (k' := 1+β) hk2a hk2b (by norm_num)
      have hnum : (3:ℝ)/2 ≤ (13/5)*((7/6)/((7/6)^2+1/4)^2 + (3/2)/((3/2)^2+1/4)^2) := by norm_num
      have hsum : (7/6)/((7/6)^2+1/4)^2 + (3/2)/((3/2)^2+1/4)^2
          ≤ (3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2) := by linarith [e1, e2]
      have hC1 : C1 β = WTSt β + 1/(4*(2-β)^2) := rfl
      rw [hC1]
      have : (0:ℝ) < 1/(4*(2-β)^2) := by positivity
      linarith [hbase, e1, e2, this]
    · -- β ∈ (1/2,5/6]: k1 ∈ [2/3,1]
      have hb2' : 1/2 < β := not_le.mp hb2
      have hk1a : (2:ℝ)/3 ≤ 3/2-β := by linarith
      have hk1b : 3/2-β ≤ 1 := by linarith
      have e1 : (1:ℝ)/((1:ℝ)^2+1/4)^2 ≤ (3/2-β)/(((3/2-β)^2+1/4)^2) :=
        g_antitone (k := (1:ℝ)) (k' := 3/2-β) hk1a hk1b (by norm_num)
      have hbase2 : (13/5)*((3/2-β)/(((3/2-β)^2+1/4)^2)) ≤ WTSt β := by
        have h2' : (0:ℝ) ≤ (13/5)*((1+β)/(((1+β)^2+1/4)^2)) := by positivity
        linarith [hbase]
      have hnum : (3:ℝ)/2 ≤ (13/5)*(1/((1:ℝ)^2+1/4)^2) := by norm_num
      have hC1 : C1 β = WTSt β + 1/(4*(2-β)^2) := rfl
      rw [hC1]
      have : (0:ℝ) < 1/(4*(2-β)^2) := by positivity
      linarith [hbase2, e1, this]


/-! ## An explicit upper bound for `C1` and consequences -/

noncomputable def C1ub (β : ℝ) : ℝ :=
  (13/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2))
    + 2*(1-β)/(2-β)^4 + 8*(1-β)^2/(2-β)^5 + 24*(1-β)^3/(2-β)^7 + 1/(4*(2-β)^2)

lemma C1_le_C1ub {β : ℝ} (h0 : 0 < β) (hβ : β ≤ 1) : C1 β ≤ C1ub β := by
  have hC : (2-β)^2-β^2 = 4*(1-β) := by ring
  have hA2 : (2-β)^2 ≤ (2-β)^2+1/4 := by linarith
  have hle : (2-β)^4 ≤ ((2-β)^2+1/4)^2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2-β)^2) hA2 2
    calc (2-β)^4 = ((2-β)^2)^2 := by ring
      _ ≤ ((2-β)^2+1/4)^2 := h
  have h3 : ((2-β)^2-β^2)/(2*(((2-β)^2+1/4)^2)) ≤ 2*(1-β)/(2-β)^4 := by
    have hA : (0:ℝ) < 2-β := by linarith
    rw [hC, div_le_div_iff₀ (by positivity) (pow_pos hA 4)]
    nlinarith [hle, hβ]
  have key : C1ub β - C1 β
      = 2*(1-β)/(2-β)^4 - ((2-β)^2-β^2)/(2*(((2-β)^2+1/4)^2)) := by
    rw [C1, C1ub, WTSt]; field_simp; ring
  linarith [key, h3]

lemma Pbound_a {A : ℝ} (h1 : 1 ≤ A) (h2 : A ≤ 3/2) :
    0 ≤ 2*(151/100:ℝ)*A^7 - A^5 - 8*A^3*(A-1) - 32*A^2*(A-1)^2 - 96*(A-1)^3 := by
  have e : 2*(151/100:ℝ)*A^7 - A^5 - 8*A^3*(A-1) - 32*A^2*(A-1)^2 - 96*(A-1)^3
      = ((6464:ℝ)/25)*(A-1)^0*(3/2-A)^7 + ((58272:ℝ)/25)*(A-1)^1*(3/2-A)^6
        + ((211824:ℝ)/25)*(A-1)^2*(3/2-A)^5 + ((75192:ℝ)/5)*(A-1)^3*(3/2-A)^4
        + ((67388:ℝ)/5)*(A-1)^4*(3/2-A)^3 + ((141206:ℝ)/25)*(A-1)^5*(3/2-A)^2
        + ((21753:ℝ)/25)*(A-1)^6*(3/2-A)^1 + ((3237:ℝ)/50)*(A-1)^7*(3/2-A)^0 := by ring
  rw [e]
  have hA1 : (0:ℝ) ≤ A-1 := by linarith
  have hA2 : (0:ℝ) ≤ 3/2-A := by linarith
  positivity

lemma Pbound_b {A : ℝ} (h1 : 3/2 ≤ A) (h2 : A ≤ 2) :
    0 ≤ 2*(151/100:ℝ)*A^7 - A^5 - 8*A^3*(A-1) - 32*A^2*(A-1)^2 - 96*(A-1)^3 := by
  have e : 2*(151/100:ℝ)*A^7 - A^5 - 8*A^3*(A-1) - 32*A^2*(A-1)^2 - 96*(A-1)^3
      = ((3237:ℝ)/50)*(A-3/2)^0*(2-A)^7 + ((906:ℝ)/25)*(A-3/2)^1*(2-A)^6
        + ((16124:ℝ)/25)*(A-3/2)^2*(2-A)^5 + ((44624:ℝ)/5)*(A-3/2)^3*(2-A)^4
        + ((150912:ℝ)/5)*(A-3/2)^4*(2-A)^3 + ((1120768:ℝ)/25)*(A-3/2)^5*(2-A)^2
        + ((785408:ℝ)/25)*(A-3/2)^6*(2-A)^1 + ((212992:ℝ)/25)*(A-3/2)^7*(2-A)^0 := by ring
  rw [e]
  have hA1 : (0:ℝ) ≤ A-3/2 := by linarith
  have hA2 : (0:ℝ) ≤ 2-A := by linarith
  positivity

lemma Pbound {A : ℝ} (h1 : 1 ≤ A) (h2 : A ≤ 2) :
    0 ≤ (151/50:ℝ)*A^7 - A^5 - 8*(A-1)*A^3 - 32*(A-1)^2*A^2 - 96*(A-1)^3 := by
  by_cases hc : A ≤ 3/2
  · have h := Pbound_a h1 hc; ring_nf at h ⊢; linarith
  · push_neg at hc
    have h := Pbound_b hc.le h2; ring_nf at h ⊢; linarith

lemma twoP_le {A : ℝ} (h1 : 1 ≤ A) (h2 : A ≤ 2) :
    2*(2*(A-1)/A^4 + 8*(A-1)^2/A^5 + 24*(A-1)^3/A^7 + 1/(4*A^2)) ≤ 151/100 := by
  have hA : (0:ℝ) < A := by linarith
  have hP := Pbound h1 h2
  have key : A^7 * (2*(2*(A-1)/A^4 + 8*(A-1)^2/A^5 + 24*(A-1)^3/A^7 + 1/(4*A^2)))
      = 4*(A-1)*A^3 + 16*(A-1)^2*A^2 + 48*(A-1)^3 + A^5/2 := by
    field_simp; ring
  have key2 : A^7 * (151/100) - (4*(A-1)*A^3 + 16*(A-1)^2*A^2 + 48*(A-1)^3 + A^5/2)
      = (1/2)*((151/50)*A^7 - A^5 - 8*(A-1)*A^3 - 32*(A-1)^2*A^2 - 96*(A-1)^3) := by ring
  have h : A^7 * (2*(2*(A-1)/A^4 + 8*(A-1)^2/A^5 + 24*(A-1)^3/A^7 + 1/(4*A^2))) ≤ A^7 * (151/100) := by
    linarith [hP, key, key2]
  exact le_of_mul_le_mul_left h (pow_pos hA 7)

lemma C1ub_le_bound {β : ℝ} (h1 : 1/4 ≤ β) (h2 : β ≤ 3/4) :
    2*C1ub β ≤ (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)) + 151/100 := by
  have key : 2*C1ub β = (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2))
      + 2*(2*((2-β)-1)/(2-β)^4 + 8*((2-β)-1)^2/(2-β)^5 + 24*((2-β)-1)^3/(2-β)^7 + 1/(4*(2-β)^2)) := by
    unfold C1ub; ring
  rw [key]
  have h := twoP_le (A := 2-β) (by linarith) (by linarith)
  linarith

lemma K0bound {β : ℝ} (h1 : 1/4 ≤ β) (h2 : β ≤ 1/2) :
    0 ≤ 5/(4*β^2) - 1/(2*(1-β)^2) - β/(1-β)^3 + 1 := by
  have hb : β ≠ 0 := by linarith
  have h1b : (1:ℝ) - β ≠ 0 := by linarith
  have hden : (0:ℝ) < -4*β^2*(β-1)^3 := by
    have hb' : (0:ℝ) < β := by linarith
    have h1' : (0:ℝ) < 1-β := by linarith
    have e : -4*β^2*(β-1)^3 = 4*β^2*(1-β)^3 := by ring
    rw [e]; exact mul_pos (mul_pos (by norm_num) (pow_pos hb' 2)) (pow_pos h1' 3)
  rw [← mul_nonneg_iff_of_pos_left hden]
  have e : -4*β^2*(β-1)^3 * (5/(4*β^2) - 1/(2*(1-β)^2) - β/(1-β)^3 + 1)
      = (2108:ℝ)*(β-1/4)^0*(1/2-β)^5 + (8136:ℝ)*(β-1/4)^1*(1/2-β)^4
        + (11888:ℝ)*(β-1/4)^2*(1/2-β)^3 + (7776:ℝ)*(β-1/4)^3*(1/2-β)^2
        + (1920:ℝ)*(β-1/4)^4*(1/2-β)^1 := by field_simp; ring
  rw [e]
  have hb1 : (0:ℝ) ≤ β-1/4 := by linarith
  have hb2 : (0:ℝ) ≤ 1/2-β := by linarith
  positivity

lemma J3 {β : ℝ} (h1 : 1/4 ≤ β) (h2 : β ≤ 1/2) :
    0 ≤ 3/(2*β) + 1/(1-β)^2 - 1/4
      - (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2))
      - 151/100 := by
  have hb : β ≠ 0 := by linarith
  have h1b : (1:ℝ) - β ≠ 0 := by linarith
  have hk1 : (3/2:ℝ) - β ≠ 0 := by linarith
  have hk2 : (1:ℝ) + β ≠ 0 := by linarith
  have hden : (0:ℝ) < 200*β*(β-1)^2*(2*β^2-6*β+5)^2*(4*β^2+8*β+5)^2 := by
    have hb' : (0:ℝ) < β := by linarith
    have hq1 : (0:ℝ) < 2*β^2-6*β+5 := by nlinarith [sq_nonneg (β-3/2)]
    have hq2 : (0:ℝ) < 4*β^2+8*β+5 := by nlinarith [sq_nonneg (β+1)]
    have h3 : (0:ℝ) < (β-1)^2 := sq_pos_of_ne_zero (by linarith : β-1 ≠ 0)
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hb') h3) (pow_pos hq1 2)) (pow_pos hq2 2)
  rw [← mul_nonneg_iff_of_pos_left hden]
  have e : 200*β*(β-1)^2*(2*β^2-6*β+5)^2*(4*β^2+8*β+5)^2 *
      (3/(2*β) + 1/(1-β)^2 - 1/4
        - (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2))
        - 151/100)
      = (167893849088:ℝ)*(β-1/4)^0*(1/2-β)^11 + (1510491761664:ℝ)*(β-1/4)^1*(1/2-β)^10
        + (6118793494528:ℝ)*(β-1/4)^2*(1/2-β)^9 + (14765230264320:ℝ)*(β-1/4)^3*(1/2-β)^8
        + (23698419466240:ℝ)*(β-1/4)^4*(1/2-β)^7 + (26803901382656:ℝ)*(β-1/4)^5*(1/2-β)^6
        + (22118435258368:ℝ)*(β-1/4)^6*(1/2-β)^5 + (13581976272896:ℝ)*(β-1/4)^7*(1/2-β)^4
        + (6207651184640:ℝ)*(β-1/4)^8*(1/2-β)^3 + (2035888947200:ℝ)*(β-1/4)^9*(1/2-β)^2
        + (429811302400:ℝ)*(β-1/4)^10*(1/2-β)^1 + (43515904000:ℝ)*(β-1/4)^11*(1/2-β)^0 := by
    field_simp; ring_nf
  rw [e]
  have hb1 : (0:ℝ) ≤ β-1/4 := by linarith
  have hb2 : (0:ℝ) ≤ 1/2-β := by linarith
  positivity

lemma J4 {β : ℝ} (h1 : 1/2 ≤ β) (h2 : β ≤ 3/4) :
    0 ≤ 9/(2-β) + 2/(3/4+β) - (1-β)/(2*β^2)
      - (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2))
      - 151/100 := by
  have hb : β ≠ 0 := by linarith
  have hA : (2:ℝ) - β ≠ 0 := by linarith
  have hq : (3/4:ℝ) + β ≠ 0 := by positivity
  have hk1 : (3/2:ℝ) - β ≠ 0 := by linarith
  have hk2 : (1:ℝ) + β ≠ 0 := by linarith
  have hden : (0:ℝ) < -400*β^2*(β-2)*(4*β+3)*(2*β^2-6*β+5)^2*(4*β^2+8*β+5)^2 := by
    have hb' : (0:ℝ) < β := by linarith
    have h2' : (0:ℝ) < 2-β := by linarith
    have h4' : (0:ℝ) < 4*β+3 := by linarith
    have hq1 : (0:ℝ) < 2*β^2-6*β+5 := by nlinarith [sq_nonneg (β-3/2)]
    have hq2 : (0:ℝ) < 4*β^2+8*β+5 := by nlinarith [sq_nonneg (β+1)]
    have e : -400*β^2*(β-2)*(4*β+3)*(2*β^2-6*β+5)^2*(4*β^2+8*β+5)^2
        = 400*β^2*(2-β)*(4*β+3)*(2*β^2-6*β+5)^2*(4*β^2+8*β+5)^2 := by ring
    rw [e]
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hb' 2)) h2') h4') (pow_pos hq1 2)) (pow_pos hq2 2)
  rw [← mul_nonneg_iff_of_pos_left hden]
  have e : -400*β^2*(β-2)*(4*β+3)*(2*β^2-6*β+5)^2*(4*β^2+8*β+5)^2 *
      (9/(2-β) + 2/(3/4+β) - (1-β)/(2*β^2)
        - (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2))
        - 151/100)
      = (4042260480000:ℝ)*(β-1/2)^0*(3/4-β)^12 + (58878066688000:ℝ)*(β-1/2)^1*(3/4-β)^11
        + (372651484774400:ℝ)*(β-1/2)^2*(3/4-β)^10 + (1371298018099200:ℝ)*(β-1/2)^3*(3/4-β)^9
        + (3286460341288960:ℝ)*(β-1/2)^4*(3/4-β)^8 + (5415511864049664:ℝ)*(β-1/2)^5*(3/4-β)^7
        + (6286615024336896:ℝ)*(β-1/2)^6*(3/4-β)^6 + (5160130848931840:ℝ)*(β-1/2)^7*(3/4-β)^5
        + (2947698773893120:ℝ)*(β-1/2)^8*(3/4-β)^4 + (1124212011520000:ℝ)*(β-1/2)^9*(3/4-β)^3
        + (262302464444416:ℝ)*(β-1/2)^10*(3/4-β)^2 + (30580654633984:ℝ)*(β-1/2)^11*(3/4-β)^1
        + (841114859520:ℝ)*(β-1/2)^12*(3/4-β)^0 := by
    field_simp; ring_nf
  rw [e]
  have hb1 : (0:ℝ) ≤ β-1/2 := by linarith
  have hb2 : (0:ℝ) ≤ 3/4-β := by linarith
  positivity



/-- Case I bracket bound, in the variable `w = β + u`. -/
lemma bracket_I {β w : ℝ} (h1 : 1/4 ≤ β) (h2 : β ≤ 1/2) (hw0 : β + 1/4 ≤ w) (hw : w ≤ 2*β) :
    2*C1 β ≤ β/((1-β)*(1+β-w)) + 4/w + 2/(2-w) - w/(4*β^2) := by
  have hβ0 : (0:ℝ) < β := by linarith
  have h1m : (1:ℝ) - β ≠ 0 := by linarith
  have hw0' : (0:ℝ) < w := by linarith
  have h2w : 2 - w ≠ 0 := by linarith
  have h1bw : 1 + β - w ≠ 0 := by linarith
  have hC1 := C1_le_C1ub hβ0 (by linarith : β ≤ 1)
  have hb := C1ub_le_bound h1 (by linarith : β ≤ 3/4)
  have hJ3 := J3 h1 h2
  have hv0 : (0:ℝ) ≤ 2*β - w := by linarith
  have hv1 : 2*β - w ≤ β - 1/4 := by linarith
  have hK0 : -1 ≤ 5/(4*β^2) - 1/(2*(1-β)^2) - β/(1-β)^3 := by linarith [K0bound h1 h2]
  have u1 : 4/w - 2/β = 2*(2*β-w)/(β*w) := by field_simp; ring
  have u2 : 2/(2-w) - 1/(1-β) = -(2*β-w)/((1-β)*(2-w)) := by field_simp; ring
  have u3 : β/((1-β)*(1+β-w)) - β/(1-β)^2 = -(2*β-w)*β/((1-β)^2*(1+β-w)) := by field_simp; ring
  have u4 : 1/(2*β) - w/(4*β^2) = (2*β-w)/(4*β^2) := by field_simp; ring
  have hcast : 2/β + 1/(1-β) + β/(1-β)^2 - 1/(2*β) - 3/(2*β) - 1/(1-β)^2 = 0 := by field_simp; ring
  have hA : β/((1-β)*(1+β-w)) + 4/w + 2/(2-w) - w/(4*β^2) - (3/(2*β) + 1/(1-β)^2)
      = (4/w - 2/β) + (2/(2-w) - 1/(1-β)) + (β/((1-β)*(1+β-w)) - β/(1-β)^2)
        + (1/(2*β) - w/(4*β^2)) + (2/β + 1/(1-β) + β/(1-β)^2 - 1/(2*β) - 3/(2*β) - 1/(1-β)^2) := by
    field_simp; ring
  have hmono : 5/(4*β^2) - 1/(2*(1-β)^2) - β/(1-β)^3
      ≤ 2/(β*w) - 1/((1-β)*(2-w)) + 1/(4*β^2) - β/((1-β)^2*(1+β-w)) := by
    have ha : 2/(β*w) - 1/β^2 = (2*β-w)*(1/(β^2*w)) := by field_simp <;> ring
    have hb2 : 1/(2*(1-β)^2) - 1/((1-β)*(2-w)) = (2*β-w)*(1/(2*(1-β)^2*(2-w))) := by
      field_simp <;> ring
    have hc : 1/(4*β^2) - 5/(4*β^2) + 1/β^2 = 0 := by field_simp <;> ring
    have hd2 : β/(1-β)^3 - β/((1-β)^2*(1+β-w)) = (2*β-w)*(β/((1-β)^3*(1+β-w))) := by
      field_simp <;> ring
    have hp1 : (0:ℝ) < β^2*w := mul_pos (pow_pos hβ0 2) hw0'
    have hp2 : (0:ℝ) < 2*(1-β)^2*(2-w) := by
      have haa : (0:ℝ) < 1-β := by linarith
      exact mul_pos (mul_pos (by norm_num) (pow_pos haa 2)) (by linarith)
    have hp3 : (0:ℝ) < (1-β)^3*(1+β-w) := by
      have haa : (0:ℝ) < 1-β := by linarith
      exact mul_pos (pow_pos haa 3) (by linarith)
    have hterm : 0 ≤ 1/(β^2*w) + 1/(2*(1-β)^2*(2-w)) + β/((1-β)^3*(1+β-w)) := by
      have hA1 : 0 ≤ 1/(β^2*w) := (one_div_pos.mpr hp1).le
      have hA2 : 0 ≤ 1/(2*(1-β)^2*(2-w)) := (one_div_pos.mpr hp2).le
      have hA3 : 0 ≤ β/((1-β)^3*(1+β-w)) := div_nonneg hβ0.le hp3.le
      linarith
    have := mul_nonneg hv0 hterm
    linarith [ha, hb2, hc, hd2, this]
  have hK' : -1/4 ≤ (2*β-w) * (2/(β*w) - 1/((1-β)*(2-w)) + 1/(4*β^2) - β/((1-β)^2*(1+β-w))) := by
    have hA' := mul_le_mul_of_nonneg_left hmono hv0
    have hB' := mul_le_mul_of_nonneg_left hK0 hv0
    have hC' : -1/4 ≤ (2*β-w)*(-1) := by nlinarith [hw0, h2]
    linarith [hA', hB', hC']
  have hB1 : 3/(2*β) + 1/(1-β)^2 - 1/4
      ≤ β/((1-β)*(1+β-w)) + 4/w + 2/(2-w) - w/(4*β^2) := by
    have hcomb : (4/w - 2/β) + (2/(2-w) - 1/(1-β)) + (β/((1-β)*(1+β-w)) - β/(1-β)^2)
        + (1/(2*β) - w/(4*β^2))
        = (2*β-w) * (2/(β*w) - 1/((1-β)*(2-w)) + 1/(4*β^2) - β/((1-β)^2*(1+β-w))) := by
      rw [u1, u2, u3, u4]; ring
    linarith [hA, hcomb, hK', hcast]
  have h2C1 : 2*C1 β ≤ (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)) + 151/100 := by
    linarith [hC1, hb]
  have hstep : (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)) + 151/100
      ≤ 3/(2*β) + 1/(1-β)^2 - 1/4 := by linarith [hJ3]
  linarith [h2C1, hstep, hB1]

/-- Case II bracket bound. -/
lemma bracket_II {β v : ℝ} (h1 : 1/2 ≤ β) (h2 : β ≤ 3/4) (hv0 : 0 ≤ v) (hv : v ≤ 3/4 - β) :
    2*C1 β ≤ 1/(β+v) + 4/(2-2*β-v) + 2/(2*β+v) - (2-2*β-v)/(4*β^2) := by
  have hβ0 : (0:ℝ) < β := by linarith
  have hC1 := C1_le_C1ub hβ0 (by linarith : β ≤ 1)
  have hb := C1ub_le_bound (by linarith : 1/4 ≤ β) h2
  have hJ4 := J4 h1 h2
  have hp1 : (0:ℝ) < β+v := by linarith
  have hp2 : (0:ℝ) < 2-2*β-v := by linarith
  have hp3 : (0:ℝ) < 2-β := by linarith
  have hn1 : β+v ≠ 0 := ne_of_gt hp1
  have hn2 : 2-β-(β+v) ≠ 0 := by linarith
  have hn3 : 2-β ≠ 0 := ne_of_gt hp3
  have hcs : 9/(2-β) ≤ 1/(β+v) + 4/(2-2*β-v) := by
    have e : 1/(β+v) + 4/(2-β-(β+v)) - 9/(2-β) = (2-β-3*(β+v))^2/((β+v)*(2-β-(β+v))*(2-β)) := by
      field_simp; ring
    have hd : (0:ℝ) < (β+v)*(2-β-(β+v))*(2-β) := by
      have h : (0:ℝ) < 2-β-(β+v) := by linarith
      exact mul_pos (mul_pos hp1 h) hp3
    have h2' : 2-2*β-v = 2-β-(β+v) := by ring
    have hnon : 0 ≤ (2-β-3*(β+v))^2/((β+v)*(2-β-(β+v))*(2-β)) := div_nonneg (sq_nonneg _) hd.le
    rw [← h2'] at e hnon
    linarith [e, hnon]
  have hq1 : (0:ℝ) < 2*β+v := by linarith
  have hq2 : (0:ℝ) < 3/4+β := by linarith
  have hlast : 2/(3/4+β) ≤ 2/(2*β+v) :=
    div_le_div_of_nonneg_left (by norm_num) hq1 (by linarith)
  have hneg : (2-2*β-v)/(4*β^2) ≤ (1-β)/(2*β^2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hv0]
  have h2C1 : 2*C1 β ≤ (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)) + 151/100 := by
    linarith [hC1, hb]
  have hstep : (26/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)) + 151/100
      ≤ 9/(2-β) + 2/(3/4+β) - (1-β)/(2*β^2) := by linarith [hJ4]
  have hfin : 9/(2-β) + 2/(3/4+β) - (1-β)/(2*β^2)
      ≤ 1/(β+v) + 4/(2-2*β-v) + 2/(2*β+v) - (2-2*β-v)/(4*β^2) := by linarith [hcs, hlast, hneg]
  linarith [h2C1, hstep, hfin]


/-! ## Exact difference formula for `FIII` and lower bounds for the log terms -/

lemma FIII_diff {β U u : ℝ} (hβ0 : 0 < β) (hU1 : U < 1) (hu1 : u < 1) :
    FIII β U - FIII β u
      = (U-u)*(-2*C1 β + β/((1-U)*(1-u)) - (U+u)/(4*β^2))
        + (2*(Real.log U - Real.log u) + (Real.log (1-u) - Real.log (1-U))) := by
  have hU : (1:ℝ) - U ≠ 0 := by linarith
  have hu : (1:ℝ) - u ≠ 0 := by linarith
  have hb : β ≠ 0 := ne_of_gt hβ0
  unfold FIII
  field_simp
  ring

/-- Lower bound for the logarithmic part of `FIII U - FIII u`. -/
lemma FIII_log_lb {U u : ℝ} (hU0 : 0 < U) (hu0 : 0 < u) (hU1 : U < 1) (hu1 : u < 1)
    (huU : u ≤ U) :
    4*(U-u)/(U+u) + 2*(U-u)/(2-U-u)
      ≤ 2*(Real.log U - Real.log u) + (Real.log (1-u) - Real.log (1-U)) := by
  have hu : u ≠ 0 := ne_of_gt hu0
  have h1u : (0:ℝ) < 1-u := by linarith
  have h1U : (0:ℝ) < 1-U := by linarith
  have hz1 : (0:ℝ) ≤ (U-u)/u := div_nonneg (by linarith) hu0.le
  have hb1 := Commons.Analysis.Real.log_one_add_ge_two_mul_div hz1
  have hz2 : (0:ℝ) ≤ (U-u)/(1-U) := div_nonneg (by linarith) h1U.le
  have hb2 := Commons.Analysis.Real.log_one_add_ge_two_mul_div hz2
  have e1 : Real.log U - Real.log u = Real.log (1 + (U-u)/u) := by
    rw [← Real.log_div (ne_of_gt hU0) hu]
    congr 1
    have hR : (u + (U-u))/u = 1 + (U-u)/u := by rw [add_div, div_self hu]
    rw [← hR, div_eq_div_iff hu hu]
    ring
  have e2 : Real.log (1-u) - Real.log (1-U) = Real.log (1 + (U-u)/(1-U)) := by
    rw [← Real.log_div (ne_of_gt h1u) (ne_of_gt h1U)]
    congr 1
    have hR : ((1-U) + (U-u))/(1-U) = 1 + (U-u)/(1-U) := by rw [add_div, div_self (ne_of_gt h1U)]
    rw [← hR, div_eq_div_iff (ne_of_gt h1U) (ne_of_gt h1U)]
    ring
  have ha : 2*((U-u)/u)/(2+(U-u)/u) = 2*(U-u)/(U+u) := by
    have h2 : (2:ℝ)*u + (U-u) ≠ 0 := by linarith
    have hUu : U + u ≠ 0 := by linarith
    field_simp
    ring
  have hb : 2*((U-u)/(1-U))/(2+(U-u)/(1-U)) = 2*(U-u)/(2-U-u) := by
    have h2 : (2:ℝ)*(1-U) + (U-u) ≠ 0 := by linarith
    have hUu : 2 - U - u ≠ 0 := by linarith
    field_simp
    ring
  have h1' : 4*(U-u)/(U+u) ≤ 2*(Real.log U - Real.log u) := by
    have hm := mul_le_mul_of_nonneg_left hb1 (show (0:ℝ) ≤ 2 by norm_num)
    have h4 : 2*(2*(U-u)/(U+u)) = 4*(U-u)/(U+u) := by ring
    rw [e1]; linarith [hm, ha, h4]
  have h2' : 2*(U-u)/(2-U-u) ≤ Real.log (1-u) - Real.log (1-U) := by
    rw [e2]; linarith [hb2, hb]
  linarith [h1', h2']

/-- Case I: `U = β`, `β ∈ [1/4,1/2]`, `u ∈ [1/4,β]`. -/
lemma FIII_endpoint_I {β u : ℝ} (hβ0 : 0 < β) (hβ1 : 1/4 ≤ β) (hβ2 : β ≤ 1/2)
    (hu1 : 1/4 ≤ u) (hu2 : u ≤ β) : FIII β u ≤ FIII β β := by
  have hu0 : (0:ℝ) < u := by linarith
  have hdiff := FIII_diff (β:=β) (U:=β) (u:=u) hβ0 (by linarith) (by linarith)
  have hlog := FIII_log_lb (U:=β) (u:=u) hβ0 hu0 (by linarith) (by linarith) hu2
  have hbr := bracket_I (β:=β) (w:=β+u) hβ1 hβ2 (by linarith) (by linarith)
  have hdu : (0:ℝ) ≤ β-u := by linarith
  have hcomb : (β-u)*(-2*C1 β + β/((1-β)*(1-u)) - (β+u)/(4*β^2))
      + (4*(β-u)/(β+u) + 2*(β-u)/(2-β-u))
      = (β-u) * (-2*C1 β + β/((1-β)*(1+β-(β+u))) + 4/(β+u) + 2/(2-(β+u)) - (β+u)/(4*β^2)) := by
    field_simp <;> ring
  have hstep : 0 ≤ (β-u)*(-2*C1 β + β/((1-β)*(1-u)) - (β+u)/(4*β^2))
      + (4*(β-u)/(β+u) + 2*(β-u)/(2-β-u)) := by
    rw [hcomb]
    exact mul_nonneg hdu (by linarith [hbr])
  rw [← sub_nonneg, hdiff]
  have hgoal : (β-u)*(-2*C1 β + β/((1-β)*(1-u)) - (β+u)/(4*β^2))
      + (2*(Real.log β - Real.log u) + (Real.log (1-u) - Real.log (1-β))) ≥ 0 := by
    linarith [hlog, hstep]
  linarith [hgoal]

/-- Case II: `U = 1-β`, `β ∈ [1/2,3/4]`, `u = 1-β-v` with `v ∈ [0,3/4-β]`. -/
lemma FIII_endpoint_II {β v : ℝ} (hβ0 : 0 < β) (hβ1 : 1/2 ≤ β) (hβ2 : β ≤ 3/4)
    (hv0 : 0 ≤ v) (hv : v ≤ 3/4 - β) : FIII β (1-β-v) ≤ FIII β (1-β) := by
  have hu0 : (0:ℝ) < 1-β-v := by linarith
  have hU0 : (0:ℝ) < 1-β := by linarith
  have hdiff := FIII_diff (β:=β) (U:=1-β) (u:=1-β-v) hβ0 (by linarith) (by linarith)
  have hlog := FIII_log_lb (U:=1-β) (u:=1-β-v) hU0 hu0 (by linarith) (by linarith) (by linarith)
  have hbr := bracket_II (β:=β) (v:=v) hβ1 hβ2 hv0 hv
  have hcomb : v*(-2*C1 β + β/((1-(1-β))*(1-(1-β-v))) - ((1-β)+(1-β-v))/(4*β^2))
      + (4*v/((1-β)+(1-β-v)) + 2*v/(2-(1-β)-(1-β-v)))
      = v * (-2*C1 β + 1/(β+v) + 4/(2-2*β-v) + 2/(2*β+v) - (2-2*β-v)/(4*β^2)) := by
    have h1 : (1:ℝ) - (1-β) = β := by ring
    have h2 : (1:ℝ) - (1-β-v) = β+v := by ring
    have h3 : (1-β)+(1-β-v) = 2-2*β-v := by ring
    have h4 : 2-(1-β)-(1-β-v) = 2*β+v := by ring
    rw [h1, h2, h3, h4]
    field_simp
    ring
  have hstep : 0 ≤ v*(-2*C1 β + β/((1-(1-β))*(1-(1-β-v))) - ((1-β)+(1-β-v))/(4*β^2))
      + (4*v/((1-β)+(1-β-v)) + 2*v/(2-(1-β)-(1-β-v))) := by
    rw [hcomb]
    exact mul_nonneg hv0 (by linarith [hbr])
  rw [← sub_nonneg, hdiff]
  have he : (1:ℝ)-β-(1-β-v) = v := by ring
  rw [he] at hlog
  have hgoal : v*(-2*C1 β + β/((1-(1-β))*(1-(1-β-v))) - ((1-β)+(1-β-v))/(4*β^2))
      + (2*(Real.log (1-β) - Real.log (1-β-v)) + (Real.log (1-(1-β-v)) - Real.log (1-(1-β)))) ≥ 0 := by
    linarith [hlog, hstep]
  linarith [hgoal]

end

end BWL



open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

/-- The target integrand (verbatim from the goal) equals the ported `WK`. -/
lemma WK_winI (β s : ℝ) :
    ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - (if (|s|:ℝ) ≤ 2-β then Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
        - (if (|s|:ℝ) ≤ β then Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )
      = BWL.WK β s := by
  rw [BWL.WK_eq]; ring

/-- Integral of the target integrand is the same as `∫ WK`. -/
lemma integral_WK_winI (β δ : ℝ) :
    (∫ s in δ..(δ+1),
        ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - (if (|s|:ℝ) ≤ 2-β then Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
        - (if (|s|:ℝ) ≤ β then Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) ))
      = ∫ s in δ..(δ+1), BWL.WK β s := by
  apply intervalIntegral.integral_congr; intro s _
  exact WK_winI β s

/-! ## Auxiliary definitions and the assembly skeleton -/

/-- The antiderivative of the integrand starting at `0`. -/
def Fint (β : ℝ) (x : ℝ) : ℝ := ∫ s in (0:ℝ)..x, BWL.WK β s

/-- The pointwise upper bound for `Wg u - Wg (1-u)` (obtained from `TT_diff_le`). -/
def BB (β u : ℝ) : ℝ :=
  (1-2*u)*BWL.C1 β + Real.log (u/(1-u)) + (BWL.Whbf β (1-u) - BWL.Whbf β u)

/-- `WK` is nonnegative for `s ≥ 1/6`. -/
lemma WK_nonneg_of_ge_sixth {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs : 1/6 ≤ s) :
    0 ≤ BWL.WK β s := by
  have hs0 : (0:ℝ) ≤ s := by linarith
  have h := boxMaj_le_target_kernel_ge_sixth hβ0 hβ1 hs
  rw [BWL.WK_eq]
  simp only [abs_of_nonneg hs0]
  linarith [h]

/-- `WK` is even, so its integral over `[-a,0]` equals that over `[0,a]`. -/
lemma integral_neg_WK (β a : ℝ) :
    (∫ s in (-a)..0, BWL.WK β s) = ∫ s in (0:ℝ)..a, BWL.WK β s := by
  have h := intervalIntegral.integral_comp_neg (f := BWL.WK β) (a := (-a)) (b := (0:ℝ))
  simp only [neg_zero, neg_neg] at h
  rw [show (∫ s in (-a)..0, BWL.WK β s) = ∫ s in (-a)..0, BWL.WK β (-s) by
    apply intervalIntegral.integral_congr; intro x _
    exact (BWL.WK_neg β x).symm]
  exact h


lemma Wg_diff_le_BB {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) :
    BWL.Wg β u - BWL.Wg β (1-u) ≤ BB β u := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u0 : (0:ℝ) < 1-u := by linarith
  have hTT := BWL.TT_diff_le hβ0 hβ1 hu1 hu2
  have hmain : BWL.Wg β u - BWL.Wg β (1-u)
      = (BWL.WTT β u - BWL.WTT β (1-u)) + Real.log (u/(1-u)) + (1-2*u)/(4*(2-β)^2)
        + (BWL.Whbf β (1-u) - BWL.Whbf β u) := by
    simp only [BWL.Wg, BWL.WhBf]
    rw [Real.log_div (ne_of_gt hu0) (ne_of_gt h1u0)]
    ring
  have hc : BWL.C1 β = BWL.WTSt β + 1/(4*(2-β)^2) := rfl
  have h1 : BB β u = (1-2*u)*BWL.WTSt β + (1-2*u)/(4*(2-β)^2)
      + Real.log (u/(1-u)) + (BWL.Whbf β (1-u) - BWL.Whbf β u) := by
    rw [BB, hc]; ring
  rw [hmain, h1]
  linarith [hTT]

/-- The `u`-th pointwise bound `V` used for the integral estimate. -/
def VV (β u : ℝ) : ℝ := (1-2*u)*(BWL.C1 β + 1/(2*β)) + 2*Real.log (u/(1-u)) + (3/4 - Real.log 2)

lemma polyP_nonneg {u β : ℝ} (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) (hβu : u ≤ β) (hβ1u : β ≤ 1-u) :
    0 ≤ 2*β^3 - 2*β^2*(1-u) + u^2*(1-u) + β*(1-u)*(1-2*u) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hu0le : (0:ℝ) ≤ u := le_of_lt hu0
  have h1 : (0:ℝ) < 5*u^2-4*u+1 := by nlinarith [sq_nonneg (u-2/5)]
  have h2 : (0:ℝ) < 9*u^2-5*u+1 := by nlinarith [sq_nonneg (3*u-5/6)]
  have h4 : (0:ℝ) < 3*u^2-3*u+1 := by nlinarith [sq_nonneg (u-1/2)]
  have h1u : (0:ℝ) ≤ 1-u := by linarith
  have hs : (0:ℝ) ≤ β-u := by linarith
  have ht : (0:ℝ) ≤ 1-u-β := by linarith
  have h3 : (0:ℝ) ≤ u*(1-u^2) := by nlinarith [hu0, hu1, hu2, mul_nonneg hu0le h1u]
  have e : (1-2*u)^3 * (2*β^3 - 2*β^2*(1-u) + u^2*(1-u) + β*(1-u)*(1-2*u))
      = (u*(5*u^2-4*u+1)) * (1-u-β)^3
      + ((1-u)*(9*u^2-5*u+1)) * (β-u)*(1-u-β)^2
      + (u*(1-u^2)) * (β-u)^2*(1-u-β)
      + ((1-u)*(3*u^2-3*u+1)) * (β-u)^3 := by ring
  have a1 : 0 ≤ (u*(5*u^2-4*u+1)) * (1-u-β)^3 :=
    mul_nonneg (mul_nonneg hu0le (le_of_lt h1)) (pow_nonneg ht 3)
  have a2 : 0 ≤ ((1-u)*(9*u^2-5*u+1)) * (β-u)*(1-u-β)^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg h1u (le_of_lt h2)) hs) (pow_nonneg ht 2)
  have a3 : 0 ≤ (u*(1-u^2)) * (β-u)^2*(1-u-β) :=
    mul_nonneg (mul_nonneg h3 (sq_nonneg (β-u))) ht
  have a4 : 0 ≤ ((1-u)*(3*u^2-3*u+1)) * (β-u)^3 :=
    mul_nonneg (mul_nonneg h1u (le_of_lt h4)) (pow_nonneg hs 3)
  have hsum : 0 ≤ (u*(5*u^2-4*u+1)) * (1-u-β)^3
      + ((1-u)*(9*u^2-5*u+1)) * (β-u)*(1-u-β)^2
      + (u*(1-u^2)) * (β-u)^2*(1-u-β)
      + ((1-u)*(3*u^2-3*u+1)) * (β-u)^3 := by linarith [a1,a2,a3,a4]
  have hp : (0:ℝ) ≤ (1-2*u)^3 * (2*β^3 - 2*β^2*(1-u) + u^2*(1-u) + β*(1-u)*(1-2*u)) := by
    rw [e]; exact hsum
  rcases lt_or_eq_of_le hu2 with h | h
  · exact nonneg_of_mul_nonneg_right hp (pow_pos (by linarith : (0:ℝ) < 1-2*u) 3)
  · subst h
    nlinarith [hβu, hβ1u]

lemma log_le_half_sub {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ (y - 1/y)/2 := by
  have hy0 : 0 < y := by linarith
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hy)
  rwa [Real.sinh_log hy0, inv_eq_one_div] at h

lemma log_ratio_lb {u β : ℝ} (hu0 : 0 < u) (hu2 : u ≤ 1/2) (hβ0 : 0 < β) (hβu : u ≤ β)
    (hβ1u : β ≤ 1-u) :
    -((1-u-β)*(1-u+β)/(2*β*(1-u))) ≤ Real.log (β/(1-u)) := by
  have h1u : (0:ℝ) < 1-u := by linarith
  have hy : 1 ≤ (1-u)/β := by rw [le_div_iff₀ hβ0]; linarith
  have hthis := log_le_half_sub hy
  have e3 : 1/((1-u)/β) = β/(1-u) := by field_simp
  rw [e3] at hthis
  have e2 : ((1-u)/β - β/(1-u))/2 = (1-u-β)*(1-u+β)/(2*β*(1-u)) := by
    field_simp; ring
  rw [e2] at hthis
  have e : Real.log (β/(1-u)) = - Real.log ((1-u)/β) := by
    rw [← Real.log_inv]; congr 1; field_simp
  rw [e]; exact neg_le_neg hthis

lemma E2_le {u β : ℝ} (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) (hβu : u ≤ β) (hβ1u : β ≤ 1-u) :
    β/(1-u)+Real.log (1-u)-Real.log (2*β)-u^2/(4*β^2)-(1-2*u)/(2*β) ≤ 3/4 - Real.log 2 := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u : (0:ℝ) < 1-u := by linarith
  have hβ0 : (0:ℝ) < β := lt_of_lt_of_le hu0 hβu
  have h1une : (1:ℝ)-u ≠ 0 := ne_of_gt h1u
  have hβ0ne : β ≠ 0 := ne_of_gt hβ0
  have hlog := log_ratio_lb hu0 hu2 hβ0 hβu hβ1u
  have hlim : (1-u)/(1-u)+Real.log (1-u)-Real.log (2*(1-u))-u^2/(4*(1-u)^2)-(1-2*u)/(2*(1-u)) ≤ 3/4 - Real.log 2 := by
    rw [div_self h1une, Real.log_mul (by norm_num) (ne_of_gt h1u)]
    field_simp
    nlinarith [sq_nonneg (2*u-1)]
  have hdiff : 0 ≤ (1-u)/(1-u)+Real.log (1-u)-Real.log (2*(1-u))-u^2/(4*(1-u)^2)-(1-2*u)/(2*(1-u))
      - (β/(1-u)+Real.log (1-u)-Real.log (2*β)-u^2/(4*β^2)-(1-2*u)/(2*β)) := by
    have hlog2 : Real.log (2*β) - Real.log (2*(1-u)) = Real.log (β/(1-u)) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hβ0), Real.log_mul (by norm_num) (ne_of_gt h1u),
          Real.log_div (ne_of_gt hβ0) (ne_of_gt h1u)]
      ring
    have e : (1-u)/(1-u)+Real.log (1-u)-Real.log (2*(1-u))-u^2/(4*(1-u)^2)-(1-2*u)/(2*(1-u))
        - (β/(1-u)+Real.log (1-u)-Real.log (2*β)-u^2/(4*β^2)-(1-2*u)/(2*β))
        = (1-u-β)/(1-u) + (Real.log (2*β)-Real.log (2*(1-u))) + u^2/(4*β^2) - u^2/(4*(1-u)^2)
          + (1-2*u)/(2*β) - (1-2*u)/(2*(1-u)) := by
      field_simp
      ring
    rw [e, hlog2]
    have key : 0 ≤ (1-u-β)/(1-u) - ((1-u-β)*(1-u+β)/(2*β*(1-u))) + u^2/(4*β^2)-u^2/(4*(1-u)^2)
        + (1-2*u)/(2*β)-(1-2*u)/(2*(1-u)) := by
      rw [show (1-u-β)/(1-u) - ((1-u-β)*(1-u+β)/(2*β*(1-u))) + u^2/(4*β^2)-u^2/(4*(1-u)^2)
        + (1-2*u)/(2*β)-(1-2*u)/(2*(1-u))
        = ((1-u-β)*(u^2*(1-u+β)+2*β*(1-u)*(β-u)))/(4*β^2*(1-u)^2) by
        field_simp; ring]
      positivity
    linarith [hlog, key]
  linarith [hdiff, hlim]

lemma XYZ_nonneg {u β : ℝ} (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) (hβ0 : 0 < β)
    (hβu : β < u) (hβ1u : β < 1-u) :
    0 ≤ (1-2*u)/(2*β) + β*(1-2*u)/(u*(1-u)) + Real.log (u/(1-u)) := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u : (0:ℝ) < 1-u := by linarith
  have h1u2 : (0:ℝ) ≤ 1-2*u := by linarith
  have hspos : (0:ℝ) < u*(1-u) := mul_pos hu0 h1u
  have hs : β*(1-β) ≤ u*(1-u) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u-β) (by linarith : (0:ℝ) ≤ 1-β-u)]
  have hZ : Real.log (u/(1-u)) ≥ -((1-2*u)/(2*(u*(1-u)))) := by
    have hy : 1 ≤ (1-u)/u := by rw [le_div_iff₀ hu0]; linarith
    have h := log_le_half_sub hy
    have e : (((1-u)/u) - 1/((1-u)/u))/2 = (1-2*u)/(2*(u*(1-u))) := by field_simp; ring
    rw [e] at h
    rw [show Real.log (u/(1-u)) = -Real.log ((1-u)/u) by
      rw [← Real.log_inv]; congr 1; field_simp]
    linarith [h]
  have hcoef : 0 ≤ 1/(2*β) + β/(u*(1-u)) - 1/(2*(u*(1-u))) := by
    have h2 : β*(1-2*β) ≤ β*(1-β) := by nlinarith [hβ0]
    have h3 : 0 ≤ u*(1-u) - β*(1-2*β) := by linarith [hs, h2]
    rw [show 1/(2*β) + β/(u*(1-u)) - 1/(2*(u*(1-u)))
        = (u*(1-u) - β*(1-2*β))/(2*β*(u*(1-u))) by field_simp; ring]
    exact div_nonneg h3 (by positivity)
  have e : (1-2*u)/(2*β) + β*(1-2*u)/(u*(1-u)) + Real.log (u/(1-u))
      = (1-2*u)*(1/(2*β) + β/(u*(1-u)) - 1/(2*(u*(1-u))))
        + ((1-2*u)/(2*(u*(1-u))) + Real.log (u/(1-u))) := by ring
  rw [e]
  have h1 : 0 ≤ (1-2*u)/(2*(u*(1-u))) + Real.log (u/(1-u)) := by linarith [hZ]
  have h2 : 0 ≤ (1-2*u)*(1/(2*β) + β/(u*(1-u)) - 1/(2*(u*(1-u)))) := mul_nonneg h1u2 hcoef
  linarith [h1, h2]

lemma BB_le_VV {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ6 : 1/6 ≤ β)
    (hu1 : 1/6 ≤ u) (hu2 : u ≤ 1/2) : BB β u ≤ VV β u := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u0 : (0:ℝ) < 1-u := by linarith
  have h1une : (1:ℝ)-u ≠ 0 := ne_of_gt h1u0
  have hβ0ne : β ≠ 0 := ne_of_gt hβ0
  have hj : 0 ≤ 3/4 - Real.log 2 := by have := Real.log_two_lt_d9; linarith
  by_cases huβ : u ≤ β
  · by_cases h1uβ : 1-u ≤ β
    · -- case A
      have hA : BB β u = (1-2*u)*BWL.C1 β + 2*Real.log (u/(1-u)) + (1-2*u)/(4*β^2) := by
        simp only [BB, BWL.Whbf, if_pos huβ, if_pos h1uβ]
        rw [Real.log_div (ne_of_gt hu0) (ne_of_gt h1u0)]
        ring
      have hle : (1-2*u)/(4*β^2) ≤ (1-2*u)/(2*β) + (3/4 - Real.log 2) := by
        have hb12 : (1:ℝ)/2 ≤ β := by linarith
        have h5 : (1-2*u)/(4*β^2) ≤ (1-2*u)/(2*β) := by
          have h6 : 1/(4*β^2) ≤ 1/(2*β) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hb12]
          calc (1-2*u)/(4*β^2) = (1-2*u)*(1/(4*β^2)) := by ring
            _ ≤ (1-2*u)*(1/(2*β)) := mul_le_mul_of_nonneg_left h6 (by linarith)
            _ = (1-2*u)/(2*β) := by ring
        linarith
      rw [hA, VV]; ring_nf at hle ⊢; linarith [hle]
    · -- case B
      have hE2 := E2_le hu1 hu2 huβ (le_of_lt (lt_of_not_ge h1uβ))
      have hB : BB β u = (1-2*u)*BWL.C1 β + (1-2*u)/(2*β) + 2*Real.log (u/(1-u))
          + (β/(1-u)+Real.log (1-u)-Real.log (2*β)-u^2/(4*β^2)-(1-2*u)/(2*β)) := by
        simp only [BB, BWL.Whbf, if_pos huβ, if_neg h1uβ]
        rw [Real.log_div (ne_of_gt hu0) (ne_of_gt h1u0)]
        ring
      rw [hB, VV]; ring_nf at hE2 ⊢; linarith [hE2]
  · push_neg at huβ
    by_cases h1uβ : 1-u ≤ β
    · exfalso; linarith
    · -- case C
      have hXYZ := XYZ_nonneg hu1 hu2 hβ0 huβ (lt_of_not_ge h1uβ)
      have hC : BB β u = ((1-2*u)*(BWL.C1 β + 1/(2*β)) + 2*Real.log (u/(1-u)) + (3/4 - Real.log 2))
          - ((1-2*u)/(2*β)+β*(1-2*u)/(u*(1-u))+Real.log (u/(1-u))) - (3/4 - Real.log 2) := by
        simp only [BB, BWL.Whbf, if_neg h1uβ, if_neg (not_le.mpr huβ)]
        field_simp
        ring
      rw [hC, VV]; linarith [hXYZ, hj]

lemma log_ratio_le {u : ℝ} (hu0 : 0 < u) (hu2 : u ≤ 1/2) :
    Real.log (u/(1-u)) ≤ -2*(1-2*u) := by
  have h1u : (0:ℝ) < 1-u := by linarith
  have hune : u ≠ 0 := ne_of_gt hu0
  have hz : 0 ≤ (1-2*u)/u := div_nonneg (by linarith) hu0.le
  have h := Commons.Analysis.Real.log_one_add_ge_two_mul_div hz
  have e1 : 1 + (1-2*u)/u = (1-u)/u := by field_simp; ring
  have hz1 : (2:ℝ) + (1-2*u)/u = 1/u := by field_simp; ring
  have e2 : 2*((1-2*u)/u)/(2+(1-2*u)/u) = 2*(1-2*u) := by
    rw [hz1]; field_simp
  rw [e1, e2] at h
  have e3 : Real.log (u/(1-u)) = -Real.log ((1-u)/u) := by
    rw [← Real.log_inv]; congr 1; field_simp
  rw [e3]; linarith

lemma VV_le_W {β u : ℝ} (hu0 : 0 < u) (hu2 : u ≤ 1/2) :
    VV β u ≤ (1-2*u)*(BWL.C1 β + 1/(2*β) - 4) + (3/4 - Real.log 2) := by
  rw [VV]
  have h := log_ratio_le hu0 hu2
  linarith

lemma VV_cont {β : ℝ} : ContinuousOn (fun u : ℝ => VV β u) (Set.uIcc (1/6:ℝ) (1/2)) := by
  have hd : ∀ x ∈ Set.uIcc (1/6:ℝ) (1/2), (1:ℝ) - x ≠ 0 := fun x hx => by
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/6 ≤ 1/2)] at hx
    exact ne_of_gt (by linarith [hx.2] : (0:ℝ) < 1-x)
  have hu : ∀ x ∈ Set.uIcc (1/6:ℝ) (1/2), x/(1-x) ≠ 0 := fun x hx => by
    have hx' := hx
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/6 ≤ 1/2)] at hx
    exact div_ne_zero (ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)) (hd x hx')
  have hl : ContinuousOn (fun u : ℝ => Real.log (u/(1-u))) (Set.uIcc (1/6:ℝ) (1/2)) :=
    ContinuousOn.log (continuousOn_id.div (continuousOn_const.sub continuousOn_id) hd) hu
  unfold VV
  exact (((continuousOn_const.sub (continuousOn_id.const_mul 2)).mul continuousOn_const).add
    (hl.const_mul 2)).add continuousOn_const

lemma int_max_VV_le {β : ℝ} (hβ0 : 0 < β) :
    (∫ u in (1/6:ℝ)..(1/2), max 0 (VV β u))
      ≤ max 0 (BWL.C1 β + 1/(2*β) - 4)/9 + (3/4 - Real.log 2)/3 := by
  set K := BWL.C1 β + 1/(2*β) - 4 with hK
  set J := (3:ℝ)/4 - Real.log 2 with hJ
  have hJ0 : 0 ≤ J := by rw [hJ]; have := Real.log_two_lt_d9; linarith
  have hKp : 0 ≤ max 0 K := le_max_left _ _
  have hpt : ∀ u ∈ Set.Icc (1/6:ℝ) (1/2), max 0 (VV β u) ≤ (1-2*u)*max 0 K + J := by
    intro u hu
    have h5 : (0:ℝ) ≤ 1-2*u := by linarith [hu.2]
    have h2 : VV β u ≤ (1-2*u)*K + J := by
      rw [hK, hJ]
      exact VV_le_W (β:=β) (u:=u) (by linarith [hu.1]) (by linarith [hu.2])
    have h4 : (1-2*u)*K + J ≤ (1-2*u)*max 0 K + J := by
      linarith [mul_le_mul_of_nonneg_left (le_max_right (0:ℝ) K) h5]
    exact max_le (add_nonneg (mul_nonneg h5 hKp) hJ0) (le_trans h2 h4)
  have hf : IntervalIntegrable (fun u : ℝ => max 0 (VV β u)) volume (1/6:ℝ) (1/2) := by
    have hcont : ContinuousOn (fun u : ℝ => max 0 (VV β u)) (Set.uIcc (1/6:ℝ) (1/2)) := by
      have h := (continuousOn_const (c := (0:ℝ))).sup (VV_cont (β := β))
      exact h
    exact hcont.intervalIntegrable
  have hg : IntervalIntegrable (fun u : ℝ => (1-2*u)*max 0 K + J) volume (1/6:ℝ) (1/2) :=
    (((continuousOn_const.sub (continuousOn_id.const_mul 2)).mul continuousOn_const).add
      continuousOn_const).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ)/6 ≤ 1/2) hf hg hpt
  have hcalc : (∫ u in (1/6:ℝ)..(1/2), ((1-2*u)*max 0 K + J)) = max 0 K/9 + J/3 := by
    have hi1 : IntervalIntegrable (fun u : ℝ => (1-2*u)*max 0 K) volume (1/6:ℝ) (1/2) :=
      ((continuousOn_const.sub (continuousOn_id.const_mul 2)).mul continuousOn_const).intervalIntegrable
    have hi2 : IntervalIntegrable (fun _ : ℝ => J) volume (1/6:ℝ) (1/2) := intervalIntegrable_const
    have hsum : (∫ u in (1/6:ℝ)..(1/2), ((1-2*u)*max 0 K + J))
        = (∫ u in (1/6:ℝ)..(1/2), (1-2*u)*max 0 K) + (∫ u in (1/6:ℝ)..(1/2), J) :=
      intervalIntegral.integral_add hi1 hi2
    rw [hsum]
    rw [show (∫ u in (1/6:ℝ)..(1/2), (1-2*u)*max 0 K)
        = (∫ u in (1/6:ℝ)..(1/2), (max 0 K)*(1-2*u)) by
      apply intervalIntegral.integral_congr; intro u _; ring]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    have e : (∫ u in (1/6:ℝ)..(1/2), (1-2*u)) = 1/9 := by
      have hi3 : IntervalIntegrable (fun u : ℝ => (2:ℝ)*u) volume (1/6:ℝ) (1/2) :=
        intervalIntegrable_id.const_mul 2
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi3, intervalIntegral.integral_const_mul]
      rw [integral_id]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      norm_num
    rw [e]; ring
  rw [hcalc] at hmono
  exact hmono

/-- Degree-15 Taylor truncation of `arctan` (a lower bound on `[0,∞)`). -/
def at8 (y : ℝ) : ℝ := y - y^3/3 + y^5/5 - y^7/7 + y^9/9 - y^11/11 + y^13/13 - y^15/15

lemma at8_le_arctan {y : ℝ} (hy : 0 ≤ y) : at8 y ≤ Real.arctan y := by
  unfold at8
  exact Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 y hy

/-- Lower bound for `WPT β (1/2)` using the Taylor bound for `arctan`. -/
def WPTlb (β : ℝ) : ℝ :=
  (13/5)*(at8 ((1/2)/(3/2-β)) + at8 ((1/2)/(1+β)))
    + ((2-β)^2-β^2)/(2*(2-β)) * at8 ((1/2)/(2-β))
    + ((2-β)^2-β^2)^2/8 * ((at8 ((1/2)/(2-β)) + (2-β)*(1/2)/((2-β)^2+(1/2)^2))/(2*(2-β)^3))
    + ((2-β)^2-β^2)^3/16 *
        (3*at8 ((1/2)/(2-β))/(8*(2-β)^5)
          + (1/2)*(5*(2-β)^2+3*(1/2)^2)/(8*(2-β)^4*((2-β)^2+(1/2)^2)^2))

lemma WPTlb_le_WPT {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : WPTlb β ≤ BWL.WPT β (1/2) := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hb : (0:ℝ) < 2-β := by linarith
  have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith [hβ0, hβ1]
  have h1 := at8_le_arctan (show (0:ℝ) ≤ (1/2)/(3/2-β) by positivity)
  have h2 := at8_le_arctan (show (0:ℝ) ≤ (1/2)/(1+β) by positivity)
  have h3 := at8_le_arctan (show (0:ℝ) ≤ (1/2)/(2-β) by positivity)
  unfold WPTlb BWL.WPT
  gcongr

lemma log_one_sub_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Real.log (1-y) ≤ -y - y^2/2 := by
  have hy1' : (0:ℝ) < 1-y := by linarith
  have hz : 0 ≤ y/(1-y) := div_nonneg hy0 hy1'.le
  have h := Commons.Analysis.Real.log_one_add_ge_two_mul_div hz
  have e1 : 1 + y/(1-y) = 1/(1-y) := by field_simp; ring
  rw [e1] at h
  have h2y : (2:ℝ) - y ≠ 0 := by linarith
  have h2 : 2*(y/(1-y))/(2+y/(1-y)) = 2*y/(2-y) := by
    rw [div_eq_div_iff (by positivity : (2 + y/(1-y)) ≠ 0) h2y]
    field_simp
    ring
  rw [h2] at h
  have hlog : Real.log (1/(1-y)) = -Real.log (1-y) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hy1'), Real.log_one, zero_sub]
  rw [hlog] at h
  have hyy : y + y^2/2 ≤ 2*y/(2-y) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hy0]
  linarith

def log2UB : ℝ := 6931471808/10^10

/-- Lower bound for `2 * WJ β (1/2)`. -/
def Lb (β : ℝ) : ℝ :=
  if 1/2 ≤ β then
    2*WPTlb β - (3*log2UB - (1-β)^2 - (1-β)^4/2) - log2UB - 2 - 1/(48*(2-β)^2) - 1/(48*β^2)
  else
    2*WPTlb β - (2*log2UB - β/2) - log2UB - 1 - 1/(48*(2-β)^2) - 2*β*(log2UB+13/12) - (1-2*β)

lemma two_WJ_ge_Lb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : Lb β ≤ 2*BWL.WJ β (1/2) := by
  have hlog2 : Real.log 2 ≤ log2UB := by unfold log2UB; have := Real.log_two_lt_d9; linarith
  have hWPT := WPTlb_le_WPT hβ0 hβ1
  rcases le_or_gt (1/2) β with hb | hb
  · have hy0 : 0 ≤ (1-β)^2 := sq_nonneg _
    have hy1 : (1-β)^2 < 1 := by nlinarith
    have hlogy := log_one_sub_le hy0 hy1
    have hy4 : ((1-β)^2)^2 = (1-β)^4 := by ring
    rw [hy4] at hlogy
    have hident : 2*BWL.WJ β (1/2) = 2*BWL.WPT β (1/2) - Real.log (1-(1-β)^2) - 4*Real.log 2
        - 2 - 1/(48*(2-β)^2) - 1/(48*β^2) := by
      have hlog2half : Real.log (1/2) = -Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num : (2:ℝ) ≠ 0), Real.log_one, zero_sub]
      have hA : (0:ℝ) < 2 - β := by linarith
      have hmul2 : Real.log (2*(2-β)) + Real.log (2*β) = Real.log (1-(1-β)^2) + 2*Real.log 2 := by
        rw [← Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hA))
            (mul_ne_zero (by norm_num) (ne_of_gt hβ0))]
        rw [show (2*(2-β))*(2*β) = 4*(1-(1-β)^2) by ring]
        rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by nlinarith : (1:ℝ)-(1-β)^2 ≠ 0),
            show Real.log (4:ℝ) = 2*Real.log 2 by
              rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num]
        ring
      unfold BWL.WJ BWL.Whbfint
      rw [if_pos hb, hlog2half]
      rw [show Real.log (1-(1-β)^2) = Real.log (2*(2-β)) + Real.log (2*β) - 2*Real.log 2 from by
            linarith [hmul2]]
      field_simp
      ring
    rw [hident]
    unfold Lb; rw [if_pos hb]
    linarith [hWPT, hlogy, hlog2]
  · have h4b : Real.log (4-2*β) ≤ 2*log2UB - β/2 := by
      rw [show (4:ℝ)-2*β = 2*(2-β) by ring, Real.log_mul (by norm_num) (by linarith : (2:ℝ)-β ≠ 0)]
      have h1 : Real.log (2-β) = Real.log 2 + Real.log (1-β/2) := by
        rw [show (2:ℝ)-β = 2*(1-β/2) by ring, Real.log_mul (by norm_num) (by linarith : (1:ℝ)-β/2 ≠ 0)]
      have h2 : Real.log (1-β/2) ≤ -(β/2) := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1-β/2)
        linarith
      rw [h1]; linarith
    have hlogb : 2*β*Real.log (1/(2*β)) ≤ 1-2*β := by
      have h1 : Real.log (1/(2*β)) = Real.log (1 + (1-2*β)/(2*β)) := by
        congr 1; field_simp; ring
      have heq : 1 + (1-2*β)/(2*β) = 1/(2*β) := by field_simp; ring
      have h2 : Real.log (1 + (1-2*β)/(2*β)) ≤ (1-2*β)/(2*β) := by
        have h := Real.log_le_sub_one_of_pos (by rw [heq]; positivity : (0:ℝ) < 1 + (1-2*β)/(2*β))
        have e : 1 + (1-2*β)/(2*β) - 1 = (1-2*β)/(2*β) := by ring
        rw [e] at h; exact h
      have h3 : 2*β*((1-2*β)/(2*β)) = 1-2*β := by field_simp
      rw [h1]
      calc 2*β*Real.log (1 + (1-2*β)/(2*β)) ≤ 2*β*((1-2*β)/(2*β)) :=
              mul_le_mul_of_nonneg_left h2 (by linarith)
           _ = 1-2*β := h3
    have hident : 2*BWL.WJ β (1/2) = 2*BWL.WPT β (1/2) - Real.log (4-2*β) - Real.log 2 - 1
        - 1/(48*(2-β)^2) - 2*β*(Real.log 2+13/12) - 2*β*Real.log (1/(2*β)) := by
      have hlog2half : Real.log (1/2) = -Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num : (2:ℝ) ≠ 0), Real.log_one, zero_sub]
      unfold BWL.WJ BWL.Whbfint
      rw [if_neg (not_le.mpr hb), hlog2half]
      rw [show Real.log (2*(2-β)) = Real.log (4-2*β) by congr 1; ring]
      rw [show Real.log ((1/2)/β) = Real.log (1/(2*β)) by congr 1; field_simp]
      field_simp
      ring
    rw [hident]
    unfold Lb; rw [if_neg (not_le.mpr hb)]
    have h2 : 2*β*Real.log 2 ≤ 2*β*log2UB := mul_le_mul_of_nonneg_left hlog2 (by linarith)
    nlinarith [hWPT, h4b, hlog2, hlogb, h2]
/-! ## Integrability of the integrand on `(0, 3/2]` -/

lemma WMBbig_le_four {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 5/6 ≤ s) (hs1 : s ≤ 3/2) :
    BWL.WMBbig β s ≤ 4 := by
  have hspos : (0:ℝ) < s := by linarith
  rw [BWL.WMBbig]
  by_cases h : s ≤ 2 - β
  · rw [if_pos h]
    have hb1 : (1:ℝ) ≤ 2 - β := by linarith
    have hb2 : (2:ℝ) - β ≤ 2 := by linarith
    have hsq : (2-β)^2 ≤ 4 := by nlinarith [hb1, hb2]
    have hs2 : s^2 ≤ 9/4 := by nlinarith [hs0, hs1]
    have hR : (4*(2-β)^2+s^2)/(2*(2-β)*s) ≤ 16 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hb1, hs0, hsq, hs2]
    have hlog : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) ≤ 4 := by
      have h1 : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) ≤ Real.log 16 :=
        Real.log_le_log (by positivity) hR
      have h2 : Real.log (16:ℝ) = 4*Real.log 2 := by
        rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
      rw [h2] at h1
      nlinarith [h1, Real.log_two_lt_d9]
    have hRpos : 0 ≤ Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hs0, hs1, hβ0, hβ1, sq_nonneg (2*(2-β)-s)]
    have hone : (1 - s^2/(4*(2-β)^2)) ≤ 1 := by
      have : (0:ℝ) ≤ s^2/(4*(2-β)^2) := by positivity
      linarith
    calc Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1 - s^2/(4*(2-β)^2))
        ≤ Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*1 := mul_le_mul_of_nonneg_left hone hRpos
      _ ≤ 4 := by rw [mul_one]; exact hlog
  · rw [if_neg h]
    have hb : (0:ℝ) < 2 - β := by linarith
    have hsqrt : (2-β) ≤ Real.sqrt ((2-β)^2+s^2) := by
      have hsq : (2-β)^2 ≤ (2-β)^2 + s^2 := by nlinarith [sq_nonneg s]
      have h2 := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ 2-β)] at h2
    have hnum : (2-β)^2 ≤ 4 := by
      have hb2 : (2:ℝ) - β ≤ 2 := by linarith
      have hb1 : (1:ℝ) ≤ 2 - β := by linarith
      nlinarith [hb1, hb2]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (2-β)^2 ≤ Real.sqrt ((2-β)^2+s^2)*s := by
      have := mul_le_mul_of_nonneg_right hsqrt (by linarith : (0:ℝ) ≤ s)
      nlinarith [this, hs0, hs1, hb, hnum]
    nlinarith [h1, hb, hnum, hs0]

lemma WMb_le_four {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 5/6 ≤ s) (hs1 : s ≤ 3/2) :
    BWL.WMb β s ≤ 4 := by
  have hspos : (0:ℝ) < s := by linarith
  rw [BWL.WMb]
  by_cases h : s ≤ β
  · rw [if_pos h]
    have hR : (4*β^2+s^2)/(2*β*s) ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      have hs2 : s^2 ≤ 9/4 := by nlinarith [hs0, hs1]
      nlinarith [hs0, hs1, hβ0, hβ1, h, hs2]
    have hlog : Real.log ((4*β^2+s^2)/(2*β*s)) ≤ 4 := by
      have h1 : Real.log ((4*β^2+s^2)/(2*β*s)) ≤ Real.log 4 := Real.log_le_log (by positivity) hR
      have h2 : Real.log (4:ℝ) = 2*Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      rw [h2] at h1
      nlinarith [h1, Real.log_two_lt_d9]
    have hRpos : 0 ≤ Real.log ((4*β^2+s^2)/(2*β*s)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2*β-s), hβ0, hs0]
    have hone : (1 - s^2/(2*((2-β)^2+β^2))) ≤ 1 := by
      have : (0:ℝ) ≤ s^2/(2*((2-β)^2+β^2)) := by positivity
      linarith
    calc Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))
        ≤ Real.log ((4*β^2+s^2)/(2*β*s))*1 := mul_le_mul_of_nonneg_left hone hRpos
      _ ≤ 4 := by rw [mul_one]; exact hlog
  · rw [if_neg h]
    have hβs : β ≤ s := le_of_lt (not_le.mp h)
    have hsqrt : (2-β) ≤ Real.sqrt ((2-β)^2+s^2) := by
      have hsq : (2-β)^2 ≤ (2-β)^2 + s^2 := by nlinarith [sq_nonneg s]
      have h2 := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ 2-β)] at h2
    have hb0 : (0:ℝ) ≤ β := le_of_lt hβ0
    have hle : (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2)) ≤ β/s := by
      rw [div_le_div_iff₀ (by positivity) hspos]
      have h1 : (2-β)*(β*s) ≤ Real.sqrt ((2-β)^2+s^2)*(β*s) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity : (0:ℝ) ≤ β*s)
      have h3 : Real.sqrt ((2-β)^2+s^2)*(β*s) = β*(s*Real.sqrt ((2-β)^2+s^2)) := by ring
      linarith [h1, h3]
    have hbs : β/s ≤ 4 := by
      rw [div_le_iff₀ hspos]
      nlinarith [hβs, hs0, hβ1]
    linarith

lemma norm_WKcore_le_24 {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 5/6 ≤ s)
    (hs1 : s ≤ 3/2) : |BWL.WKcore β s| ≤ 24 := by
  have hspos : (0:ℝ) < s := by linarith
  have hT0 := BWL.WTT_nonneg hβ0 hβ1 (t := s)
  have hT16 := BWL.WTT_le hβ0 hβ1 (t := s)
  have hB0 := BWL.WMBbig_nonneg hβ0 hβ1 hspos
  have hb0 := BWL.WMb_nonneg hβ0 hβ1 hspos
  have hB4 := WMBbig_le_four hβ0 hβ1 hs0 hs1
  have hb4 := WMb_le_four hβ0 hβ1 hs0 hs1
  rw [abs_le]
  constructor <;> simp only [BWL.WKcore] <;> linarith

lemma norm_WKcore_le_gen {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s)
    (hs : s ≤ 3/2) : |BWL.WKcore β s| ≤ 48 + 23*(1 - Real.log s) := by
  have hlog2 : Real.log ((3:ℝ)/2) ≤ 1 := by
    have h1 : Real.log ((3:ℝ)/2) ≤ (3:ℝ)/2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  rcases le_or_gt s (5/6) with h2 | h2
  · have h := BWL.norm_WKcore_le hβ0 hβ1 hs0 h2
    have hL : Real.log s ≤ 0 := Real.log_nonpos hs0.le (by linarith)
    have hc : (23:ℝ) - 2*Real.log s ≤ 48 + 23*(1 - Real.log s) := by linarith
    linarith
  · have h := norm_WKcore_le_24 hβ0 hβ1 (le_of_lt h2) hs
    have hc : (24:ℝ) ≤ 48 + 23*(1 - Real.log s) := by
      have hL : Real.log s ≤ 1 := le_trans (Real.log_le_log hs0 hs) hlog2
      nlinarith [hL]
    linarith

lemma intervalIntegrable_WK_Icc {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 3/2) :
    IntervalIntegrable (BWL.WK β) volume a b := by
  have hg : IntervalIntegrable (fun s : ℝ => 48 + 23*(1 - Real.log s)) volume a b := by
    have h1 : IntervalIntegrable (fun s : ℝ => (48:ℝ) + (23 - 23*Real.log s)) volume a b :=
      intervalIntegrable_const.add (intervalIntegrable_const.sub (intervalIntegrable_log'.const_mul 23))
    convert h1 using 1
    funext s; ring
  refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => BWL.WK β s)
    (g := fun s : ℝ => 48 + 23*(1 - Real.log s)) hg ?_ ?_
  · exact (BWL.measurable_WK β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hx0 : 0 < x := lt_trans ha hx.1
    have hx1 : x ≤ 3/2 := le_trans hx.2 hb
    rw [show BWL.WK β x = BWL.WKcore β x from by rw [BWL.WK, BWL.WKcore, abs_of_pos hx0]]
    exact norm_WKcore_le_gen hβ0 hβ1 hx0 hx1

/-! ## Nonnegativity of `Wg` and monotonicity of `WJ` -/

lemma Wg_nonneg_of {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht1 : 1/6 ≤ t) (ht2 : t ≤ 5/6) :
    0 ≤ BWL.Wg β t := by
  have h := wg_nonneg hβ0 hβ1 ht1 ht2
  simpa only [BWL.Wg, BWL.WTT, BWL.WhBf, BWL.Whbf] using h

lemma WJ_mono {β x y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 1/6 ≤ x) (hxy : x ≤ y) (hy : y ≤ 5/6) : BWL.WJ β x ≤ BWL.WJ β y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hx5 : x ≤ 5/6 := by linarith
  rw [← BWL.integral_Wg hβ0 hβ1 hx0 hx5, ← BWL.integral_Wg hβ0 hβ1 hy0 hy]
  have hi : IntervalIntegrable (BWL.Wg β) volume x y :=
    BWL.intervalIntegrable_Wg' hβ0 hβ1 hx0 hxy hy
  have h0 : (0:ℝ) ≤ ∫ s in x..y, BWL.Wg β s := by
    have h := intervalIntegral.integral_mono_on hxy (intervalIntegrable_const) hi
      (fun s hs => Wg_nonneg_of hβ0 hβ1 (le_trans hx hs.1) (le_trans hs.2 hy))
    simpa using h
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (BWL.intervalIntegrable_Wg hβ0 hβ1 hx0 hx5) hi
  linarith [h0, hadd]

lemma WJ_sixth_lb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : (-(31:ℝ)/100) ≤ BWL.WJ β (1/6) := by
  have h := Commons.Analysis.Real.WJ_sixth_lower hβ0 hβ1
  convert h using 1
  unfold BWL.WJ BWL.WPT BWL.Whbfint
  rfl

lemma WJ_threequarter_lb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (8:ℝ)/25 ≤ BWL.WJ β (3/4) := by
  have h := Commons.Analysis.Real.WJ_threequarter_lower hβ0 hβ1
  convert h using 1
  unfold BWL.WJ BWL.WPT BWL.Whbfint
  rfl

lemma WJ_five_sixths_lb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (8:ℝ)/25 ≤ BWL.WJ β (5/6) :=
  le_trans (WJ_threequarter_lb hβ0 hβ1)
    (WJ_mono hβ0 hβ1 (by norm_num) (by norm_num) (by norm_num))

/-! ## Low-range log machinery -/

set_option maxHeartbeats 1000000 in
/-- `WTT β ·` is nonincreasing on `[0,∞)`. -/
lemma WTT_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    BWL.WTT β t' ≤ BWL.WTT β t := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hb : (0:ℝ) < 2-β := by linarith
  have h0 : (2-β)^2 + t^2 ≤ (2-β)^2 + t'^2 := by nlinarith
  have h0' : (0:ℝ) ≤ (2-β)^2 + t^2 := by positivity
  have h4sq : ((2-β)^2+t^2)^2 ≤ ((2-β)^2+t'^2)^2 := by nlinarith [h0, h0']
  have h5sq : ((2-β)^2+t^2)^3 ≤ ((2-β)^2+t'^2)^3 := by nlinarith [h0, h0']
  have hD : (0:ℝ) ≤ ((2-β)^2-β^2)^2 := sq_nonneg _
  have hD' : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  have hp1 : (0:ℝ) < (3/2-β)^2 + t^2 := by positivity
  have hp1' : (0:ℝ) < (3/2-β)^2 + t'^2 := by positivity
  have hp2 : (0:ℝ) < (1+β)^2 + t^2 := by positivity
  have hp2' : (0:ℝ) < (1+β)^2 + t'^2 := by positivity
  have hp3 : (0:ℝ) < 2*((2-β)^2 + t^2) := by positivity
  have hp3' : (0:ℝ) < 2*((2-β)^2 + t'^2) := by positivity
  have hp4 : (0:ℝ) < 8*((2-β)^2 + t^2)^2 := by positivity
  have hp4' : (0:ℝ) < 8*((2-β)^2 + t'^2)^2 := by positivity
  have hp5 : (0:ℝ) < 16*((2-β)^2 + t^2)^3 := by positivity
  have hp5' : (0:ℝ) < 16*((2-β)^2 + t'^2)^3 := by positivity
  have h1 : (3/2-β)/((3/2-β)^2+t'^2) ≤ (3/2-β)/((3/2-β)^2+t^2) := by
    rw [div_le_div_iff₀ hp1' hp1]; nlinarith
  have h2 : (1+β)/((1+β)^2+t'^2) ≤ (1+β)/((1+β)^2+t^2) := by
    rw [div_le_div_iff₀ hp2' hp2]; nlinarith
  have h3 : ((2-β)^2-β^2)/(2*((2-β)^2+t'^2)) ≤ ((2-β)^2-β^2)/(2*((2-β)^2+t^2)) := by
    rw [div_le_div_iff₀ hp3' hp3]; nlinarith [sq_nonneg ((2-β)^2-β^2)]
  have h4 : ((2-β)^2-β^2)^2/(8*((2-β)^2+t'^2)^2) ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2+t^2)^2) := by
    rw [div_le_div_iff₀ hp4' hp4]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4sq (by norm_num)) hD
  have h5 : ((2-β)^2-β^2)^3/(16*((2-β)^2+t'^2)^3) ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2+t^2)^3) := by
    rw [div_le_div_iff₀ hp5' hp5]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5sq (by norm_num))
      (pow_nonneg hD' 3)
  have e1 : (13/5)*((3/2-β)/((3/2-β)^2+t'^2)+(1+β)/((1+β)^2+t'^2))
      ≤ (13/5)*((3/2-β)/((3/2-β)^2+t^2)+(1+β)/((1+β)^2+t^2)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
  simp only [BWL.WTT]
  linarith [e1, h1, h2, h3, h4, h5]

/-- `∫_0^a log (c/t) = a log (c/a) + a`. -/
lemma integral_log_div {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, Real.log (c/t)) = a*(Real.log (c/a)) + a := by
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0:ℝ) a → Real.log (c/t) = Real.log c - Real.log t := by
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le ha.le] at ht
    exact Real.log_div (ne_of_gt hc) (ne_of_gt ht.1)
  rw [intervalIntegral.integral_congr_ae hae,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_log',
      intervalIntegral.integral_const, integral_log,
      Real.log_div (ne_of_gt hc) (ne_of_gt ha)]
  simp only [sub_zero]
  ring

/-- Lower bound for the `2-β` majorant on `(0,1/6]`. -/
lemma WMBbig_lb {β t : ℝ} (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6) :
    (143/144)*Real.log (2*(2-β)/t) ≤ BWL.WMBbig β t := by
  have hb : (0:ℝ) < 2 - β := by linarith
  have hb1 : (1:ℝ) ≤ 2 - β := by linarith
  rw [BWL.WMBbig, if_pos (by linarith : t ≤ 2 - β)]
  have hlog : Real.log (2*(2-β)/t) ≤ Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [ht0]
  have hlog0 : 0 ≤ Real.log (2*(2-β)/t) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ ht0]
    nlinarith [ht, hb1]
  have ht2 : t^2 ≤ 1/36 := by nlinarith [ht0, ht]
  have hsq : t^2/(4*(2-β)^2) ≤ 1/144 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [ht2, hb1]
  calc (143/144)*Real.log (2*(2-β)/t)
      ≤ (1 - t^2/(4*(2-β)^2))*Real.log (2*(2-β)/t) := by
        have h143 : (143:ℝ)/144 ≤ 1 - t^2/(4*(2-β)^2) := by linarith
        exact mul_le_mul_of_nonneg_right h143 hlog0
    _ ≤ Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t))*(1 - t^2/(4*(2-β)^2)) := by
        have hge : (0:ℝ) ≤ 1 - t^2/(4*(2-β)^2) := by linarith
        have hmm := mul_le_mul_of_nonneg_left hlog hge
        linarith [hmm]

/-- Lower bound for the `β` majorant on `(0,β]`. -/
lemma WMb_lb {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ β)
    (ht6 : t ≤ 1/6) :
    (143/144)*Real.log (2*β/t) ≤ BWL.WMb β t := by
  have hD : (4:ℝ) ≤ 2*((2-β)^2+β^2) := by nlinarith [sq_nonneg (β-1)]
  rw [BWL.WMb, if_pos ht]
  have hlog : Real.log (2*β/t) ≤ Real.log ((4*β^2+t^2)/(2*β*t)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [ht0]
  have hlog0 : 0 ≤ Real.log (2*β/t) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ ht0]
    linarith
  have ht2 : t^2 ≤ 1/36 := by nlinarith [ht0, ht6]
  have hsq : t^2/(2*((2-β)^2+β^2)) ≤ 1/144 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [ht2, hD]
  calc (143/144)*Real.log (2*β/t)
      ≤ (1 - t^2/(2*((2-β)^2+β^2)))*Real.log (2*β/t) := by
        have h143 : (143:ℝ)/144 ≤ 1 - t^2/(2*((2-β)^2+β^2)) := by linarith
        exact mul_le_mul_of_nonneg_right h143 hlog0
    _ ≤ Real.log ((4*β^2+t^2)/(2*β*t))*(1 - t^2/(2*((2-β)^2+β^2))) := by
        have hge : (0:ℝ) ≤ 1 - t^2/(2*((2-β)^2+β^2)) := by linarith
        have hmm := mul_le_mul_of_nonneg_left hlog hge
        linarith [hmm]

set_option maxHeartbeats 1000000 in
/-- Integrability of `WK` on `[a,b] ⊂ [0,3/2]`. -/
lemma intervalIntegrable_WK_Icc' {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 3/2) :
    IntervalIntegrable (BWL.WK β) volume a b := by
  have hg : IntervalIntegrable (fun s : ℝ => 48 + 23*(1 - Real.log s)) volume a b := by
    have h1 : IntervalIntegrable (fun s : ℝ => (48:ℝ) + (23 - 23*Real.log s)) volume a b :=
      intervalIntegrable_const.add (intervalIntegrable_const.sub (intervalIntegrable_log'.const_mul 23))
    convert h1 using 1
    funext s; ring
  refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => BWL.WK β s)
    (g := fun s : ℝ => 48 + 23*(1 - Real.log s)) hg ?_ ?_
  · exact (BWL.measurable_WK β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
    have hx1 : x ≤ 3/2 := le_trans hx.2 hb
    rw [show BWL.WK β x = BWL.WKcore β x from by rw [BWL.WK, BWL.WKcore, abs_of_pos hx0]]
    exact norm_WKcore_le_gen hβ0 hβ1 hx0 hx1

/-- Pointwise upper bound for the integrand on `(0,1/6]`. -/
lemma WK_upper_bound {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6)
    (hW0 : BWL.WTT β 0 ≤ 6.5) :
    BWL.WK β s ≤ 6.5 - (143/144)*Real.log (2*(2-β)/s)
      - (if s ≤ β then (143/144)*Real.log (2*β/s) else 0) := by
  have hWTT : BWL.WTT β s ≤ BWL.WTT β 0 := WTT_mono hβ0 hβ1 (le_refl 0) hs0.le
  have hB := WMBbig_lb hβ1 hs0 hs
  have hbs : BWL.WK β s = BWL.WKcore β s := by
    rw [BWL.WK, BWL.WKcore, abs_of_pos hs0]
  rw [hbs]
  simp only [BWL.WKcore]
  by_cases h : s ≤ β
  · rw [if_pos h]
    have hb := WMb_lb hβ0 hβ1 hs0 h hs
    linarith
  · rw [if_neg h]
    have hb := BWL.WMb_nonneg hβ0 hβ1 hs0
    linarith

set_option maxHeartbeats 2000000 in
/-- Compensated inequality: the `D`-terms are dominated by the deficit of the leading term. -/
lemma wtt_D_compensated {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    2/(2-β)^2 + 2*(1-β)/(2-β)^4 + 4*(1-β)^2/(2-β)^6
      ≤ 3.25*(1+2*β)/((3:ℝ)/2+β/2-β^2) := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hQ : (0:ℝ) < (3:ℝ)/2+β/2-β^2 := by nlinarith [sq_nonneg (β-3/4)]
  have hu : (0:ℝ) ≤ 1-β := by linarith
  rw [le_div_iff₀ hQ]
  rw [show (2/(2-β)^2 + 2*(1-β)/(2-β)^4 + 4*(1-β)^2/(2-β)^6) * ((3:ℝ)/2+β/2-β^2)
      = (2*(2-β)^4 + 2*(1-β)*(2-β)^2 + 4*(1-β)^2) * ((3:ℝ)/2+β/2-β^2) / (2-β)^6 by
    field_simp]
  rw [div_le_iff₀ (pow_pos hb 6)]
  nlinarith [sq_nonneg β, sq_nonneg (1-β), sq_nonneg (2-β), hu,
    mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu,
    pow_nonneg (le_of_lt hβ0) 3, pow_nonneg (le_of_lt hβ0) 4,
    pow_nonneg (le_of_lt hβ0) 5]

set_option maxHeartbeats 4000000 in
/-- `WTT β 0 ≤ 6.5`. -/
lemma WTT_zero_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : BWL.WTT β 0 ≤ 6.5 := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hb : (0:ℝ) < 2-β := by linarith
  have hA' : (3:ℝ)/2-β ≠ 0 := ne_of_gt hA
  have hB' : (1:ℝ)+β ≠ 0 := ne_of_gt hB
  have hb' : (2:ℝ)-β ≠ 0 := ne_of_gt hb
  have hQ : (0:ℝ) < (3:ℝ)/2+β/2-β^2 := by nlinarith [sq_nonneg (β-3/4)]
  have hu : (0:ℝ) < 1-β := by linarith
  have hA2 : (3:ℝ) - 2*β ≠ 0 := by
    have e : (3:ℝ) - 2*β = 2*(3/2-β) := by ring
    rw [e]; exact mul_ne_zero (by norm_num) (ne_of_gt hA)
  have hB2 : (2:ℝ) + 2*β ≠ 0 := by
    have e : (2:ℝ) + 2*β = 2*(1+β) := by ring
    rw [e]; exact mul_ne_zero (by norm_num) (ne_of_gt hB)
  have hcomp := wtt_D_compensated hβ0 hβ1
  have hkey : BWL.WTT β 0
      = 6.5/((3/2-β)*(1+β)) + 2*(1-β)/(2-β)^2 + 2*(1-β)^2/(2-β)^4
        + 4*(1-β)^3/(2-β)^6 := by
    simp only [BWL.WTT, sq, mul_zero, add_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    field_simp [hA', hB', hb', hA2, hB2]
    ring_nf
  rw [hkey, show 6.5/((3/2-β)*(1+β)) = 6.5/((3:ℝ)/2+β/2-β^2) by
      rw [show ((3/2-β)*(1+β)) = (3:ℝ)/2+β/2-β^2 by ring]]
  have hmain : 2*(1-β)/(2-β)^2 + 2*(1-β)^2/(2-β)^4 + 4*(1-β)^3/(2-β)^6
      ≤ 6.5*((1:ℝ)/2+β/2-β^2)/((3:ℝ)/2+β/2-β^2) := by
    rw [show 2*(1-β)/(2-β)^2 + 2*(1-β)^2/(2-β)^4 + 4*(1-β)^3/(2-β)^6
        = (1-β)*(2/(2-β)^2 + 2*(1-β)/(2-β)^4 + 4*(1-β)^2/(2-β)^6) by ring]
    rw [show 6.5*((1:ℝ)/2+β/2-β^2)/((3:ℝ)/2+β/2-β^2)
        = (1-β)*(3.25*(1+2*β)/((3:ℝ)/2+β/2-β^2)) by
      rw [show ((1:ℝ)/2+β/2-β^2) = (1-β)*(1+2*β)/2 by ring]
      ring]
    exact mul_le_mul_of_nonneg_left hcomp hu.le
  have hcompl : 6.5/((3:ℝ)/2+β/2-β^2) + 6.5*((1:ℝ)/2+β/2-β^2)/((3:ℝ)/2+β/2-β^2) = 6.5 := by
    rw [show ((1:ℝ)/2+β/2-β^2) = (1-β)*(1+2*β)/2 by ring]
    rw [← add_div, div_eq_iff (ne_of_gt hQ)]
    ring
  linarith [hmain, hcompl]

end


/-! ## Region A: `a ∈ [1/6,1/4]` -/

/-- For `a ∈ [1/6,1/4]` the window integral `∫_{-a}^{1-a} WK` is positive (indeed `≥ 1/100`). -/
lemma regionA {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha1 : 1/6 ≤ a) (ha2 : a ≤ 1/4) :
    0 ≤ ∫ s in (-a)..(1-a), BWL.WK β s := by
  have ha5 : a ≤ 5/6 := by linarith
  have ha0 : 0 < a := by linarith
  have h1a0 : 0 < 1-a := by linarith
  have h1a5 : 1-a ≤ 5/6 := by linarith
  rw [BWL.WK_split hβ0 hβ1 ha1 (by linarith)]
  have h1 : (∫ s in (0:ℝ)..a, BWL.Wg β s) ≤ ∫ s in (0:ℝ)..a, BWL.WK β s :=
    BWL.integral_Wg_le_WK hβ0 hβ1 ha0 ha5
  have h2 : (∫ s in (0:ℝ)..(1-a), BWL.Wg β s) ≤ ∫ s in (0:ℝ)..(1-a), BWL.WK β s :=
    BWL.integral_Wg_le_WK hβ0 hβ1 h1a0 h1a5
  rw [BWL.integral_Wg hβ0 hβ1 ha0 ha5] at h1
  rw [BWL.integral_Wg hβ0 hβ1 h1a0 h1a5] at h2
  have hA : BWL.WJ β (1/6) ≤ BWL.WJ β a :=
    WJ_mono hβ0 hβ1 (le_refl _) ha1 ha5
  have hB : BWL.WJ β (3/4) ≤ BWL.WJ β (1-a) :=
    WJ_mono hβ0 hβ1 (by norm_num) (by linarith) h1a5
  have hs := WJ_sixth_lb hβ0 hβ1
  have ht := WJ_threequarter_lb hβ0 hβ1
  linarith


/-! ## Region B : pointwise case analysis for `BB` -/

/-- `M β = C1 β + 1/(4β²)`. -/
noncomputable def Mbd (β : ℝ) : ℝ := BWL.C1 β + 1/(4*β^2)

/-- The `u ≤ β < 1-u` branch value (`F2`). -/
noncomputable def F2f (β u : ℝ) : ℝ :=
  (1-2*u)*BWL.C1 β + Real.log (u/(1-u)) + β/(1-u) - Real.log (2*β) + Real.log u - u^2/(4*β^2)

/-- The `β < u` branch upper bound (`G3`). -/
noncomputable def G3f (β u : ℝ) : ℝ :=
  (1-2*u)*(BWL.C1 β - 4*β) + Real.log (u/(1-u))

/-- `BB` in the branch `1-u ≤ β`. -/
lemma BB_eq_A {β u : ℝ} (hβ1 : β < 1) (hu : 1-u ≤ β) (hu2 : u ≤ 1/2) :
    BB β u = (1-2*u)*Mbd β + 2*Real.log (u/(1-u)) := by
  have h1u : (1:ℝ)/2 ≤ 1-u := by linarith
  have huβ : u ≤ β := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  have h1 : BWL.Whbf β (1-u) = Real.log (2*β) - Real.log (1-u) + (1-u)^2/(4*β^2) := by
    unfold BWL.Whbf; rw [if_pos hu]
  have h2 : BWL.Whbf β u = Real.log (2*β) - Real.log u + u^2/(4*β^2) := by
    unfold BWL.Whbf; rw [if_pos huβ]
  rw [BB, h1, h2, Mbd]
  have hlog : Real.log (u/(1-u)) = Real.log u - Real.log (1-u) :=
    Real.log_div (ne_of_gt hu0) (by linarith)
  rw [hlog]; ring

/-- `BB` in the branch `u ≤ β < 1-u`. -/
lemma BB_eq_B {β u : ℝ} (hu : u ≤ β) (h1u : β < 1-u) :
    BB β u = F2f β u := by
  have h1 : BWL.Whbf β (1-u) = β/(1-u) := by
    unfold BWL.Whbf; rw [if_neg (by linarith)]
  have h2 : BWL.Whbf β u = Real.log (2*β) - Real.log u + u^2/(4*β^2) := by
    unfold BWL.Whbf; rw [if_pos hu]
  rw [BB, h1, h2, F2f]; ring

lemma Whbf_lt_u {β u : ℝ} (hβ0 : 0 < β) (hu : β < u) (hu2 : u ≤ 1/2) :
    BWL.Whbf β u = β/u := by
  unfold BWL.Whbf; rw [if_neg (not_le.mpr hu)]

/-- `BB` in the branch `β < u` is dominated by `G3f`. -/
lemma BB_le_C {β u : ℝ} (hβ0 : 0 < β) (hu : β < u) (hu1 : u ≤ 1/2)
    (hu0 : 1/4 ≤ u) : BB β u ≤ G3f β u := by
  have huβ : ¬ (u ≤ β) := not_le.mpr hu
  have hβhalf : β < 1/2 := by linarith
  have h1u : (1:ℝ)/2 ≤ 1-u := by linarith
  have h1uβ : ¬ (1-u ≤ β) := by intro hh; linarith
  have h1 : BWL.Whbf β (1-u) = β/(1-u) := by
    unfold BWL.Whbf; rw [if_neg h1uβ]
  have h2 : BWL.Whbf β u = β/u := by
    unfold BWL.Whbf; rw [if_neg huβ]
  have hpos : (0:ℝ) < u*(1-u) := by nlinarith
  have hu0' : (0:ℝ) < u := by linarith
  have hkey : β/(1-u) - β/u = β*(2*u-1)/(u*(1-u)) := by
    field_simp; ring
  have hlog : Real.log (u/(1-u)) = Real.log u - Real.log (1-u) :=
    Real.log_div (ne_of_gt hu0') (by linarith)
  rw [BB, h1, h2, G3f, hkey, hlog]
  have hfac : -4*β*(1-2*u) - β*(2*u-1)/(u*(1-u)) = β*(1-2*u)*(1/(u*(1-u)) - 4) := by
    field_simp; ring
  have h4 : (4:ℝ) ≤ 1/(u*(1-u)) := by
    rw [le_div_iff₀ hpos]; nlinarith
  have hnn : 0 ≤ β*(1-2*u)*(1/(u*(1-u)) - 4) :=
    mul_nonneg (mul_nonneg hβ0.le (by linarith)) (by linarith)
  linarith [hfac, hnn]

/-! ## Bridges to the fleet's numerical facts and `F2` monotonicity -/

/-- `BWL.C1` agrees with the commons' `boxC1`. -/
lemma C1_eq_boxC1 (β : ℝ) : BWL.C1 β = boxC1 β := by
  simp only [BWL.C1, BWL.WTSt, boxC1]

lemma le_three_of_mem {β : ℝ} (h : 1/4 ≤ β) (h2 : β ≤ 1/2) : BWL.C1 β ≤ 3 := by
  rw [C1_eq_boxC1]; exact boxC1_le_three h h2

lemma two_C1_le_RHS1 {β : ℝ} (h : 1/4 ≤ β) (h2 : β ≤ 1/2) :
    2*BWL.C1 β ≤ 3/(2*β) + 1/(1-β) + β/(1-β)^2 := by
  have h3 := le_three_of_mem h h2
  have h6 := RHS1_ge_six h h2
  linarith

lemma two_C1_le_RHS2 {β : ℝ} (h : 1/2 ≤ β) (h2 : β ≤ 3/4) :
    2*BWL.C1 β ≤ 2/(1-β) + 2/β - (1-β)/(2*β^2) := by
  rw [C1_eq_boxC1]; exact twoC1_le_RHS2 h h2



/-! ## Region B : pointwise bounds in the three branches -/

/-- `log (u/(1-u)) ≤ 0` for `u ∈ [1/4,1/2]`. -/
lemma log_ratio_nonpos {u : ℝ} (hu1 : 1/4 ≤ u) (hu2 : u ≤ 1/2) : Real.log (u/(1-u)) ≤ 0 := by
  apply Real.log_nonpos
  · apply div_nonneg <;> linarith
  · rw [div_le_one (by linarith : (0:ℝ) < 1-u)]; linarith



/-- `log (u/(1-u)) ≤ -2(1-2u)` for `u ∈ [1/4,1/2]`. -/
lemma log_ratio_le_neg_two {u : ℝ} (hu1 : 1/4 ≤ u) (hu2 : u ≤ 1/2) :
    Real.log (u/(1-u)) ≤ -2*(1-2*u) := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1u : (0:ℝ) < 1-u := by linarith
  have hy : (1:ℝ) ≤ (1-u)/u := by rw [le_div_iff₀ hu0]; linarith
  have h := two_mul_sub_div_le_log hy
  have hlog : Real.log ((1-u)/u) = - Real.log (u/(1-u)) := by
    rw [← Real.log_inv]; congr 1; field_simp
  have hsimp : 2*(((1-u)/u) - 1)/(((1-u)/u) + 1) = 2*(1-2*u) := by
    field_simp; ring
  rw [hlog, hsimp] at h
  linarith

/-- Branch `1-u ≤ β`: `BB ≤ (1-2u)(M-4)`. -/
lemma BB_le_A_log {β u : ℝ} (hβ1 : β < 1) (hu : 1-u ≤ β) (hu1 : 1/4 ≤ u) (hu2 : u ≤ 1/2) :
    BB β u ≤ (1-2*u)*(Mbd β - 4) := by
  rw [BB_eq_A hβ1 hu hu2]
  have h := log_ratio_le_neg_two hu1 hu2
  have h2 : 2*Real.log (u/(1-u)) ≤ -4*(1-2*u) := by linarith
  nlinarith [h2]

/-- Branch `β < u` with `β ∈ [1/4,1/2]`: `BB ≤ 0`. -/
lemma BB_le_C_nonpos {β u : ℝ} (hβ0 : 0 < β) (hu : β < u) (hu1 : 1/4 ≤ u) (hu2 : u ≤ 1/2)
    (hβ14 : 1/4 ≤ β) (hβ12 : β ≤ 1/2) : BB β u ≤ 0 := by
  have hC1 := le_three_of_mem hβ14 hβ12
  have h := BB_le_C hβ0 hu hu2 hu1
  have hu0 : (0:ℝ) < u := by linarith
  have h1u : (0:ℝ) < 1-u := by linarith
  have hy : (1:ℝ) ≤ (1-u)/u := by rw [le_div_iff₀ hu0]; linarith
  have hlog := two_mul_sub_div_le_log hy
  have hlog' : 2*(1-2*u) ≤ Real.log ((1-u)/u) := by
    have e : 2*(((1-u)/u) - 1)/(((1-u)/u) + 1) = 2*(1-2*u) := by field_simp; ring
    rwa [e] at hlog
  have hlu : Real.log (u/(1-u)) = -Real.log ((1-u)/u) := by
    rw [← Real.log_inv]; congr 1; field_simp
  have hc : BWL.C1 β - 4*β - 2 ≤ 0 := by linarith
  have h1m : (0:ℝ) ≤ 1-2*u := by linarith
  have hmul : (1-2*u)*(BWL.C1 β - 4*β - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1m hc
  unfold G3f at h
  rw [hlu] at h
  nlinarith [hmul, hlog', h1m, h]

/-- Branch `β < u` with `β ≤ 1/4`: `BB ≤ (1-2u) C1`. -/
lemma BB_le_C_quarter {β u : ℝ} (hβ0 : 0 < β) (hu : β < u) (hu1 : 1/4 ≤ u) (hu2 : u ≤ 1/2) :
    BB β u ≤ (1-2*u)*BWL.C1 β := by
  have h := BB_le_C hβ0 hu hu2 hu1
  unfold G3f at h
  have hlog : Real.log (u/(1-u)) ≤ 0 := log_ratio_nonpos (by linarith) (by linarith)
  have h1m : (0:ℝ) ≤ 1-2*u := by linarith
  have hmul : (1-2*u)*(BWL.C1 β - 4*β) ≤ (1-2*u)*BWL.C1 β :=
    mul_le_mul_of_nonneg_left (by linarith) h1m
  linarith

/-! ## Measurability and integrability of `BB` -/

lemma measurable_Whbf (β : ℝ) : Measurable (BWL.Whbf β) := by
  unfold BWL.Whbf
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) (by fun_prop)

lemma measurable_BB (β : ℝ) : Measurable (BB β) := by
  have h1 : Measurable (fun u : ℝ => (1-2*u)*BWL.C1 β) := by fun_prop
  have h2 : Measurable (fun u : ℝ => Real.log (u/(1-u))) := by fun_prop
  have h3 : Measurable (fun u : ℝ => BWL.Whbf β (1-u)) :=
    (measurable_Whbf β).comp (by fun_prop)
  have h4 : Measurable (fun u : ℝ => BWL.Whbf β u) := measurable_Whbf β
  have h := (h1.add h2).add (h3.sub h4)
  unfold BB
  exact h

lemma C1_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : (0:ℝ) < BWL.C1 β := by
  have hD : (0:ℝ) ≤ (2-β)^2-β^2 := by rw [show (2-β)^2-β^2 = 4*(1-β) by ring]; nlinarith
  have ha : (0:ℝ) < 3/2-β := by linarith
  have hb : (0:ℝ) < 1+β := by linarith
  have h2b : (0:ℝ) < 2-β := by linarith
  have hp1 : (0:ℝ) < ((3/2-β)^2+1/4)^2 := by positivity
  have hp2 : (0:ℝ) < ((1+β)^2+1/4)^2 := by positivity
  have hW1 : (0:ℝ) ≤ (3/2-β)/(((3/2-β)^2+1/4)^2) := div_nonneg ha.le hp1.le
  have hW2 : (0:ℝ) ≤ (1+β)/(((1+β)^2+1/4)^2) := div_nonneg hb.le hp2.le
  have hW : (0:ℝ) ≤ (13/5)*((3/2-β)/(((3/2-β)^2+1/4)^2) + (1+β)/(((1+β)^2+1/4)^2)) :=
    mul_nonneg (by norm_num) (add_nonneg hW1 hW2)
  have hq1 : (0:ℝ) < ((2-β)^2+1/4)^2 := by positivity
  have h1 : (0:ℝ) ≤ ((2-β)^2-β^2) * (1/(2*(((2-β)^2+1/4)^2))) :=
    mul_nonneg hD (by positivity)
  have h2 : (0:ℝ) ≤ ((2-β)^2-β^2)^2 * (1/(2*((2-β)^5))) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have h3 : (0:ℝ) ≤ ((2-β)^2-β^2)^3 * (3/(8*((2-β)^7))) :=
    mul_nonneg (pow_nonneg hD 3) (by positivity)
  have h5 : (0:ℝ) < 1/(4*(2-β)^2) := by positivity
  unfold BWL.C1 BWL.WTSt
  linarith

/-- A dominating constant for `BB` on `[1/4,1/2]`. -/
noncomputable def BBbnd (β : ℝ) : ℝ :=
  BWL.C1 β/2 + Real.log 3 + 2*(|Real.log (2*β)| + Real.log 4 + 9/(64*β^2) + 4*β)

lemma Whbf_abs_le {β t : ℝ} (hβ0 : 0 < β) (ht1 : 1/4 ≤ t) (ht2 : t ≤ 3/4) :
    |BWL.Whbf β t| ≤ |Real.log (2*β)| + Real.log 4 + 9/(64*β^2) + 4*β := by
  have ht0 : (0:ℝ) < t := by linarith
  have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have h9 : (0:ℝ) ≤ 9/(64*β^2) := by positivity
  have hb4 : (0:ℝ) ≤ 4*β := by linarith
  have hlogt_le : Real.log t ≤ Real.log 4 := Real.log_le_log ht0 (by linarith)
  have hlogt_nonpos : Real.log t ≤ 0 := Real.log_nonpos ht0.le (by linarith)
  have hlog4 : Real.log ((1:ℝ)/4) = -Real.log 4 := by
    rw [show ((1:ℝ)/4) = (4:ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlogt_ge : -Real.log 4 ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/4) ht1
    rw [hlog4] at h; linarith
  rw [BWL.Whbf]
  by_cases h : t ≤ β
  · rw [if_pos h]
    have ht2 : t^2 ≤ 9/16 := by nlinarith
    have hβ2 : (0:ℝ) < β^2 := by positivity
    have hsq : t^2/(4*β^2) ≤ 9/(64*β^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hsq0 : (0:ℝ) ≤ t^2/(4*β^2) := by positivity
    have hub : Real.log (2*β) - Real.log t + t^2/(4*β^2)
        ≤ |Real.log (2*β)| + Real.log 4 + 9/(64*β^2) + 4*β := by
      have h1 := le_abs_self (Real.log (2*β))
      have h2 : -Real.log t ≤ Real.log 4 := by linarith [hlogt_ge]
      linarith
    have hlb : -(|Real.log (2*β)| + Real.log 4 + 9/(64*β^2) + 4*β)
        ≤ Real.log (2*β) - Real.log t + t^2/(4*β^2) := by
      have h1 := neg_abs_le (Real.log (2*β))
      linarith
    rw [abs_le]; exact ⟨hlb, hub⟩
  · rw [if_neg h]
    have hβt : β < t := not_le.mp h
    have h3 : (0:ℝ) ≤ β/t := by positivity
    rw [abs_of_nonneg h3]
    have h1 : β/t ≤ 4*β := by rw [div_le_iff₀ ht0]; nlinarith
    linarith [abs_nonneg (Real.log (2*β)), h9, hb4]

lemma BBbnd_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ BBbnd β := by
  unfold BBbnd
  have ha := abs_nonneg (Real.log (2*β))
  have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have h9 : (0:ℝ) ≤ 9/(64*β^2) := by positivity
  have hb4 : (0:ℝ) ≤ 4*β := by linarith
  have hlog3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hC1 : (0:ℝ) ≤ BWL.C1 β/2 := by
    have := C1_pos hβ0 hβ1; linarith
  linarith

lemma BB_le_BBbnd {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hu1 : 1/4 ≤ u) (hu2 : u ≤ 1/2) :
    max 0 (BB β u) ≤ BBbnd β := by
  have hA := Whbf_abs_le hβ0 hu1 (by linarith : u ≤ 3/4)
  have hB := Whbf_abs_le hβ0 (by linarith : (1:ℝ)/4 ≤ 1-u) (by linarith : 1-u ≤ 3/4)
  have hlog : Real.log (u/(1-u)) ≤ 0 := log_ratio_nonpos (by linarith) (by linarith)
  have hC1 := C1_pos hβ0 hβ1
  have hm : (1-2*u)*BWL.C1 β ≤ (1/2)*BWL.C1 β :=
    mul_le_mul_of_nonneg_right (by linarith) hC1.le
  have hWa : BWL.Whbf β (1-u) ≤ |Real.log (2*β)| + Real.log 4 + 9/(64*β^2) + 4*β := by
    linarith [le_abs_self (BWL.Whbf β (1-u)), hA]
  have hWb : -BWL.Whbf β u ≤ |Real.log (2*β)| + Real.log 4 + 9/(64*β^2) + 4*β := by
    linarith [neg_abs_le (BWL.Whbf β u), hB]
  have hlog3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hBB : BB β u ≤ BBbnd β := by
    unfold BB BBbnd; linarith
  exact max_le (BBbnd_nonneg hβ0 hβ1) hBB

lemma intervalIntegrable_max_BB {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (fun u => max 0 (BB β u)) volume (1/4) (1/2) := by
  refine IntervalIntegrable.mono_fun' (f := fun u => max 0 (BB β u))
    (g := fun _ : ℝ => BBbnd β) intervalIntegrable_const ?_ ?_
  · exact (Measurable.max measurable_const (measurable_BB β)).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at hx
    have h := BB_le_BBbnd hβ0 hβ1 (le_of_lt hx.1) hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left (0:ℝ) (BB β x))]
    exact h


/-! ## Region B : auxiliary interval facts -/

lemma intervalIntegrable_max_BB' {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a b : ℝ}
    (ha : 1/4 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/2) :
    IntervalIntegrable (fun u => max 0 (BB β u)) volume a b :=
  (intervalIntegrable_max_BB hβ0 hβ1).mono_set (by
    intro x hx
    simp only [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2),
      Set.mem_Icc] at hx ⊢
    exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩)

lemma antideriv_one_sub_two {x : ℝ} : HasDerivAt (fun y : ℝ => y - y^2) (1-2*x) x := by
  have h2 := ((hasDerivAt_id x).sub ((hasDerivAt_id x).pow 2))
  refine h2.congr_deriv ?_
  simp only [Nat.reduceSub, pow_one, id_eq]; ring

/-- `F2f` is bounded by `3/4 - log 2 + 1/100` in its branch. -/
lemma F2f_le_bound {β u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hu : 1/4 ≤ u) (huβ : u ≤ β)
    (hu2 : u ≤ 1-β) : F2f β u ≤ 3/4 - Real.log 2 + 1/100 := by
  have h := boxWindow_F2f_bound hβ0 hβ1 hu huβ hu2
  have h' : (1-2*u)*boxC1 β + Real.log (u/(1-u)) + β/(1-u) - Real.log (2*β) + Real.log u
      - u^2/(4*β^2) ≤ 3/4 - Real.log 2 + 1/100 := by
    simpa only [boxC1] using h
  rw [F2f, C1_eq_boxC1]
  linarith [h']

/-- Case A on `[c,1/2]`. -/
lemma int_le_A {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {c : ℝ} (hc0 : 1-β ≤ c) (hc1 : 1/4 ≤ c) (hc2 : c ≤ 1/2) :
    (∫ u in c..(1/2), max 0 (BB β u)) ≤ (Mbd β - 4)⁺ * (1/2-c)^2 := by
  have hI := intervalIntegrable_max_BB' hβ0 hβ1 hc1 hc2 (by norm_num)
  have hg : IntervalIntegrable (fun u : ℝ => (1-2*u)*(Mbd β - 4)⁺) volume c (1/2) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hmono : (∫ u in c..(1/2), max 0 (BB β u))
      ≤ ∫ u in c..(1/2), (1-2*u)*(Mbd β - 4)⁺ := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hc2 hI hg
    intro x hx
    simp only [Set.uIoo_of_le hc2, Set.mem_Ioo] at hx
    have hxA := BB_le_A_log hβ1 (by linarith [hx.1] : 1-x ≤ β) (le_trans hc1 (le_of_lt hx.1))
      (le_of_lt hx.2)
    have hxle : (1-2*x)*(Mbd β - 4) ≤ (1-2*x)*(Mbd β - 4)⁺ :=
      mul_le_mul_of_nonneg_left (le_max_left (Mbd β - 4) (0:ℝ)) (by linarith)
    exact max_le (mul_nonneg (by linarith) (le_max_right (Mbd β - 4) (0:ℝ))) (le_trans hxA hxle)
  have hval : (∫ u in c..(1/2), (1-2*u)*(Mbd β - 4)⁺) = (Mbd β - 4)⁺ * (1/2-c)^2 := by
    rw [intervalIntegral.integral_mul_const]
    have hi : IntervalIntegrable (fun u : ℝ => (1-2*u)) volume c (1/2) := by
      apply Continuous.intervalIntegrable; fun_prop
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := c) (b := 1/2)
      (f := fun y : ℝ => y - y^2) (f' := fun w : ℝ => 1 - 2*w)
      (fun x _ => antideriv_one_sub_two) hi
    rw [hmain]; ring
  linarith [hmono, hval]

/-- Case B on `[c,d]`. -/
lemma int_le_B {β : ℝ} {c d : ℝ} (hc1 : 1/4 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1/2)
    (h : ∀ x ∈ Set.Ioo c d, max 0 (BB β x) ≤ 3/4 - Real.log 2 + 1/100)
    (hI : IntervalIntegrable (fun u => max 0 (BB β u)) volume c d) :
    (∫ u in c..d, max 0 (BB β u)) ≤ (d-c)*(3/4 - Real.log 2 + 1/100) := by
  have hg : IntervalIntegrable (fun _ : ℝ => 3/4 - Real.log 2 + 1/100) volume c d :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hcd hI hg h
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith [hmono]

/-- Case C on `[c,d]`. -/
lemma int_le_C {β : ℝ} {c d : ℝ} (hcd : c ≤ d)
    (h : ∀ x ∈ Set.Ioo c d, max 0 (BB β x) ≤ 0)
    (hI : IntervalIntegrable (fun u => max 0 (BB β u)) volume c d) :
    (∫ u in c..d, max 0 (BB β u)) ≤ 0 := by
  have hg : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume c d := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hcd hI hg h
  simpa using hmono



/-! ## Region B: the correction-integral bound and the numerical facts -/

/-- `C1f` agrees with `BWL.C1`. -/
lemma C1f_eq_C1 (β : ℝ) : C1f β = BWL.C1 β := by
  simp only [C1f, WTStf, BWL.C1, BWL.WTSt]

/-- The commons' `Lbf` agrees with `Lb`. -/
lemma Lbf_eq_Lb (β : ℝ) : Lbf β = BWLH.Lb β := by
  unfold Lbf BWLH.Lb Lbfif Lbfelse WPTf WPTlb log2UB at8f at8
  split_ifs <;> ring

/-! ### Region B: bounds for the correction integral `∫_{1/4}^{1/2} max 0 (BB β u)` -/

/-- `β ≤ 1/4`: on `(1/4,1/2)` the bound `BB ≤ (1-2u)(C1 - 4β - 2)` holds. -/
lemma int_le_C2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ4 : β ≤ 1/4) :
    (∫ u in (1/4)..(1/2), max 0 (BB β u)) ≤ (BWL.C1 β - 4*β - 2)⁺ / 16 := by
  have hI := intervalIntegrable_max_BB hβ0 hβ1
  have hg : IntervalIntegrable (fun u : ℝ => (1-2*u)*(BWL.C1 β - 4*β - 2)⁺) volume (1/4) (1/2) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hmono : (∫ u in (1/4)..(1/2), max 0 (BB β u))
      ≤ ∫ u in (1/4)..(1/2), (1-2*u)*(BWL.C1 β - 4*β - 2)⁺ := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (show (1:ℝ)/4 ≤ 1/2 by norm_num) hI hg ?_
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hx14 : (1:ℝ)/4 ≤ x := le_of_lt hx.1
    have hx12 : x ≤ 1/2 := le_of_lt hx.2
    have hβx : β < x := lt_of_le_of_lt hβ4 hx.1
    have hC := BB_le_C hβ0 hβx hx12 hx14
    have hlog := log_ratio_le_neg_two hx14 hx12
    have h1m : (0:ℝ) ≤ 1-2*x := by linarith
    have hkey : (1-2*x)*(BWL.C1 β - 4*β) + Real.log (x/(1-x))
        ≤ (1-2*x)*(BWL.C1 β - 4*β - 2) := by
      nlinarith [hlog]
    have hle : BB β x ≤ (1-2*x)*(BWL.C1 β - 4*β - 2) := by
      unfold G3f at hC; linarith
    have hle2 : (1-2*x)*(BWL.C1 β - 4*β - 2) ≤ (1-2*x)*(BWL.C1 β - 4*β - 2)⁺ :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) h1m
    exact max_le (mul_nonneg h1m (le_max_right _ _)) (le_trans hle hle2)
  have hval : (∫ u in (1/4)..(1/2), (1-2*u)*(BWL.C1 β - 4*β - 2)⁺)
      = (BWL.C1 β - 4*β - 2)⁺ / 16 := by
    rw [intervalIntegral.integral_mul_const]
    have hi : IntervalIntegrable (fun u : ℝ => (1-2*u)) volume (1/4) (1/2) := by
      apply Continuous.intervalIntegrable; fun_prop
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (1:ℝ)/4) (b := (1:ℝ)/2)
      (f := fun y : ℝ => y - y^2) (f' := fun w : ℝ => 1 - 2*w)
      (fun x _ => antideriv_one_sub_two) hi
    rw [hmain]; ring
  linarith [hmono, hval]

/-- The `β ≤ 1/4` case of the region-B bound. -/
lemma regionB_low {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ4 : β ≤ 1/4) :
    (∫ u in (1/4)..(1/2), max 0 (BB β u)) ≤ BWLH.Lb β := by
  have h := int_le_C2 hβ0 hβ1 hβ4
  have hcert := certC hβ0 hβ4
  have hS := LbfSelse_le_Lbfelse hβ0 hβ1
  have hLbf : Lbf β = Lbfelse β := by rw [Lbf, if_neg (by linarith : ¬ ((1:ℝ)/2 ≤ β))]
  rw [← Lbf_eq_Lb β, hLbf] at *
  have hK1 : BWL.C1 β - 4*β - 2 ≤ 8 * Lbfelse β := by
    have e : BWL.C1 β - 4*β - 2 = 2*((C1f β - 4*β)/2 - 1) := by
      rw [C1f_eq_C1]; ring
    rw [e]; linarith
  have hA := certA hβ0 (by linarith : β ≤ 1/2)
  have h0 : (0:ℝ) ≤ 8 * Lbfelse β := by linarith
  have hmax : (BWL.C1 β - 4*β - 2)⁺ ≤ 8 * Lbfelse β := by
    have e : (BWL.C1 β - 4*β - 2)⁺ = max (BWL.C1 β - 4*β - 2) 0 := rfl
    rw [e]; exact max_le hK1 h0
  linarith

/-- The `1/4 ≤ β ≤ 1/2` case of the region-B bound. -/
lemma regionB_mid_low {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ14 : 1/4 ≤ β) (hβ12 : β ≤ 1/2) :
    (∫ u in (1/4)..(1/2), max 0 (BB β u)) ≤ 1/30 := by
  have hI1 : IntervalIntegrable (fun u => max 0 (BB β u)) volume (1/4) β :=
    intervalIntegrable_max_BB' hβ0 hβ1 (a := (1:ℝ)/4) (b := β) (le_refl _) hβ14 hβ12
  have hI2 : IntervalIntegrable (fun u => max 0 (BB β u)) volume β (1/2) :=
    intervalIntegrable_max_BB' hβ0 hβ1 (a := β) (b := (1:ℝ)/2) hβ14 hβ12 (by norm_num)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hK0 : (0:ℝ) ≤ 3/4 - Real.log 2 + 1/100 := by
    have := Real.log_two_lt_d9; linarith
  have hA : (∫ u in (1/4)..β, max 0 (BB β u)) ≤ (β-1/4)*(3/4 - Real.log 2 + 1/100) := by
    refine int_le_B (by norm_num) hβ14 hβ12 ?_ hI1
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hx14 : (1:ℝ)/4 ≤ x := le_of_lt hx.1
    have hxβ : x ≤ β := le_of_lt hx.2
    have hx1β : x ≤ 1-β := by linarith [hx.2]
    have hxF := F2f_le_bound hβ0 hβ1 hx14 hxβ hx1β
    have hBBx : BB β x = F2f β x := BB_eq_B hxβ (by linarith [hx.2])
    rw [hBBx]
    exact max_le hK0 hxF
  have hB : (∫ u in β..(1/2), max 0 (BB β u)) ≤ 0 := by
    refine int_le_C hβ12 ?_ hI2
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hx0 : β < x := hx.1
    have hx14 : (1:ℝ)/4 ≤ x := by linarith [hx.1]
    have hx12 : x ≤ 1/2 := le_of_lt hx.2
    exact max_le (le_refl 0) (BB_le_C_nonpos hβ0 hx0 hx14 hx12 hβ14 hβ12)
  have hsum : (∫ u in (1/4)..(1/2), max 0 (BB β u))
      = (∫ u in (1/4)..β, max 0 (BB β u)) + (∫ u in β..(1/2), max 0 (BB β u)) := by
    rw [← hadd]
  have hfin : (β-1/4)*(3/4 - Real.log 2 + 1/100) + 0 ≤ 1/30 := by
    have h1 : β - 1/4 ≤ 1/4 := by linarith
    have h2 : β - 1/4 ≥ 0 := by linarith
    have := mul_le_mul_of_nonneg_right h1 hK0
    have h3 : (1/4:ℝ)*(3/4 - Real.log 2 + 1/100) ≤ 1/30 := by
      have := Real.log_two_gt_d9; linarith
    linarith
  linarith

/-- The middle numerical fact, in the form needed below (from the commons'
`boxWindow_regionB_mid`). -/
lemma int_max_BB_mid {β : ℝ} (h0 : (1:ℝ)/2 ≤ β) (h1 : β ≤ 3/4) :
    (Mbd β - 4)⁺ * (β-1/2)^2 + (3/4-β)*(668528197/10^10) ≤ 1/30 := by
  have h := boxWindow_regionB_mid h0 h1
  have e : (Mbd β - 4)⁺ = max 0 (boxC1 β + 1/(4*β^2) - 4) := by
    have hM : Mbd β - 4 = boxC1 β + 1/(4*β^2) - 4 := by rw [Mbd, C1_eq_boxC1]
    have h2 : (Mbd β - 4)⁺ = max (Mbd β - 4) 0 := rfl
    rw [h2, hM, max_comm]
  rw [e]
  exact h

/-- The `1/2 ≤ β ≤ 3/4` case of the region-B bound. -/
lemma regionB_mid_high {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ12 : 1/2 ≤ β) (hβ34 : β ≤ 3/4) :
    (∫ u in (1/4)..(1/2), max 0 (BB β u)) ≤ 1/30 := by
  have hc1 : (1:ℝ)/4 ≤ 1-β := by linarith
  have hc2 : 1-β ≤ 1/2 := by linarith
  have hI1 : IntervalIntegrable (fun u => max 0 (BB β u)) volume (1/4) (1-β) :=
    intervalIntegrable_max_BB' hβ0 hβ1 (a := (1:ℝ)/4) (b := 1-β) (by norm_num) hc1 hc2
  have hI2 : IntervalIntegrable (fun u => max 0 (BB β u)) volume (1-β) (1/2) :=
    intervalIntegrable_max_BB' hβ0 hβ1 (a := 1-β) (b := (1:ℝ)/2) hc1 hc2 (by norm_num)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hK0 : (0:ℝ) ≤ 3/4 - Real.log 2 + 1/100 := by
    have := Real.log_two_lt_d9; linarith
  have hA : (∫ u in (1/4)..(1-β), max 0 (BB β u)) ≤ (3/4-β)*(3/4 - Real.log 2 + 1/100) := by
    have hle : (∫ u in (1/4)..(1-β), max 0 (BB β u))
        ≤ (1-β-1/4)*(3/4 - Real.log 2 + 1/100) := by
      refine int_le_B (by norm_num) hc1 hc2 ?_ hI1
      intro x hx
      simp only [Set.mem_Ioo] at hx
      have hx14 : (1:ℝ)/4 ≤ x := le_of_lt hx.1
      have hxβ : x ≤ β := by linarith [hx.2]
      have hx1β : x ≤ 1-β := le_of_lt hx.2
      have hxF := F2f_le_bound hβ0 hβ1 hx14 hxβ hx1β
      have hBBx : BB β x = F2f β x := BB_eq_B hxβ (by linarith [hx.2])
      rw [hBBx]
      exact max_le hK0 hxF
    have e : (1:ℝ) - β - 1/4 = 3/4 - β := by ring
    rwa [e] at hle
  have hB : (∫ u in (1-β)..(1/2), max 0 (BB β u)) ≤ (Mbd β - 4)⁺ * (β-1/2)^2 := by
    have h := int_le_A hβ0 hβ1 (c := 1-β) (le_refl _) hc1 hc2
    have e : ((1:ℝ)/2 - (1-β))^2 = (β-1/2)^2 := by ring
    rwa [e] at h
  have hsum : (∫ u in (1/4)..(1/2), max 0 (BB β u))
      = (∫ u in (1/4)..(1-β), max 0 (BB β u)) + (∫ u in (1-β)..(1/2), max 0 (BB β u)) := by
    rw [← hadd]
  have hmid := int_max_BB_mid hβ12 hβ34
  have hKle : (3/4 : ℝ) - Real.log 2 + 1/100 ≤ 668528197/10^10 := by
    have := Real.log_two_gt_d9
    have hc : ((668528197:ℝ)/10^10) = 3/4 + 1/100 - 6931471803/10^10 := by norm_num
    rw [hc]; linarith
  have h34 : (0:ℝ) ≤ 3/4 - β := by linarith
  have hle := mul_le_mul_of_nonneg_left hKle h34
  linarith

/-- The `3/4 ≤ β` case of the region-B bound. -/
lemma regionB_high {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ34 : 3/4 ≤ β) :
    (∫ u in (1/4)..(1/2), max 0 (BB β u)) ≤ BWLH.Lb β := by
  have h := int_le_A hβ0 hβ1 (c := (1:ℝ)/4) (by linarith) (by norm_num) (by norm_num)
  have hcert := certD hβ0 hβ34 hβ1.le
  have hS := LbfSif_le_Lbfif hβ0 hβ1
  have hB := certB hβ0 (by linarith : (1:ℝ)/2 ≤ β) hβ1.le
  have hLbf : Lbf β = Lbfif β := by rw [Lbf, if_pos (by linarith : (1:ℝ)/2 ≤ β)]
  rw [← Lbf_eq_Lb β, hLbf] at *
  have hK : Mbd β - 4 ≤ 16 * Lbfif β := by
    have e : Mbd β - 4 = C1f β + 1/(4*β^2) - 4 := by rw [Mbd, ← C1f_eq_C1]
    rw [e]; linarith
  have h0 : (0:ℝ) ≤ 16 * Lbfif β := by linarith
  have hmax : (Mbd β - 4)⁺ ≤ 16 * Lbfif β := by
    have e : (Mbd β - 4)⁺ = max (Mbd β - 4) 0 := rfl
    rw [e]; exact max_le hK h0
  have hInt : (∫ u in (1/4)..(1/2), max 0 (BB β u)) ≤ (Mbd β - 4)⁺ / 16 := by
    have e : ((1:ℝ)/2 - (1:ℝ)/4)^2 = 1/16 := by norm_num
    rw [e] at h
    linarith
  linarith

/-- Region B: the correction integral is dominated by the minimum of the two available
lower bounds for `2 WJ β (1/2)`. -/
lemma regionB {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ u in (1/4)..(1/2), max 0 (BB β u)) ≤ max (1/30) (BWLH.Lb β) := by
  rcases le_or_gt β (1/4) with h | h
  · exact le_trans (regionB_low hβ0 hβ1 h) (le_max_right _ _)
  · have h4 : (1:ℝ)/4 ≤ β := le_of_lt h
    rcases le_or_gt β (1/2) with h2 | h2
    · exact le_trans (regionB_mid_low hβ0 hβ1 h4 h2) (le_max_left _ _)
    · have h12 : (1:ℝ)/2 ≤ β := le_of_lt h2
      rcases le_or_gt β (3/4) with h3 | h3
      · exact le_trans (regionB_mid_high hβ0 hβ1 h12 h3) (le_max_left _ _)
      · exact le_trans (regionB_high hβ0 hβ1 (le_of_lt h3)) (le_max_right _ _)

/-- `1/30 ≤ 2 WJ β (1/2)`. -/
lemma two_WJ_half_lb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (1:ℝ)/30 ≤ 2 * BWL.WJ β (1/2) := by
  have h := Commons.Analysis.Real.WJ_pair_half_lower hβ0 hβ1
  have h2 : (1:ℝ)/30 ≤ BWL.WJ β (1/2) + BWL.WJ β (1/2) := by
    convert h using 1
    unfold BWL.WJ BWL.WPT BWL.Whbfint
    rfl
  linarith

/-- The threshold is dominated by `2 WJ β (1/2)`. -/
lemma max_threshold_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    max (1/30) (BWLH.Lb β) ≤ 2 * BWL.WJ β (1/2) :=
  max_le (two_WJ_half_lb hβ0 hβ1) (two_WJ_ge_Lb hβ0 hβ1)

/-- The correction integral is bounded below by minus the region-B integral. -/
lemma Wg_diff_integral_lb {β a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha4 : 1/4 ≤ a) (ha2 : a ≤ 1/2) :
    -(∫ u in (1/4)..(1/2), max 0 (BB β u))
      ≤ ∫ u in a..(1/2), (BWL.Wg β (1-u) - BWL.Wg β u) := by
  have hiBB : IntervalIntegrable (fun u => max 0 (BB β u)) volume a (1/2) :=
    intervalIntegrable_max_BB' hβ0 hβ1 (a := a) (b := (1:ℝ)/2) ha4 ha2 (by norm_num)
  have hiBB14 : IntervalIntegrable (fun u => max 0 (BB β u)) volume (1/4) (1/2) :=
    intervalIntegrable_max_BB hβ0 hβ1
  have hi1 : IntervalIntegrable (fun u => max 0 (BB β u)) volume (1/4) a :=
    intervalIntegrable_max_BB' hβ0 hβ1 (a := (1:ℝ)/4) (b := a) (by norm_num) ha4 ha2
  have hiWg : IntervalIntegrable (BWL.Wg β) volume a (1/2) :=
    BWL.intervalIntegrable_Wg' hβ0 hβ1 (by linarith) ha2 (by linarith)
  have hiWg1 : IntervalIntegrable (fun u => BWL.Wg β (1-u)) volume a (1/2) := by
    have hh : IntervalIntegrable (BWL.Wg β) volume (1/2) (1-a) :=
      BWL.intervalIntegrable_Wg' hβ0 hβ1 (by norm_num) (by linarith) (by linarith)
    have h2 := (hh.comp_sub_left (1:ℝ)).symm
    convert h2 using 1
    · ring
    · norm_num
  have hiWgd : IntervalIntegrable (fun u => BWL.Wg β (1-u) - BWL.Wg β u) volume a (1/2) :=
    hiWg1.sub hiWg
  have hmono : (∫ u in a..(1/2), -(max 0 (BB β u)))
      ≤ ∫ u in a..(1/2), (BWL.Wg β (1-u) - BWL.Wg β u) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo ha2 hiBB.neg hiWgd ?_
    intro u hu
    simp only [Set.mem_Ioo] at hu
    have hu16 : (1:ℝ)/6 ≤ u := by linarith [hu.1]
    have hu12 : u ≤ 1/2 := le_of_lt hu.2
    have hw := Wg_diff_le_BB hβ0 hβ1 hu16 hu12
    have hmax : BB β u ≤ max 0 (BB β u) := le_max_right _ _
    linarith
  rw [intervalIntegral.integral_neg] at hmono
  have hadd : (∫ u in (1/4)..(1/2), max 0 (BB β u))
      = (∫ u in (1/4)..a, max 0 (BB β u)) + (∫ u in a..(1/2), max 0 (BB β u)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hiBB]
  have hnn : (0:ℝ) ≤ ∫ u in (1/4)..a, max 0 (BB β u) :=
    intervalIntegral.integral_nonneg ha4 (fun x _ => le_max_left _ _)
  linarith [hmono, hadd, hnn]

end BWLH

/-- **Linnik `L = 5.5`**, left half of the window integral: for `δ ∈ [-1/2,-1/6]` the
integral of the box-window difference over `[δ,δ+1]` is nonnegative. -/
theorem boxWindow_left_half {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ δ : ℝ, -1/2 ≤ δ → δ ≤ -1/6 →
      0 ≤ ∫ s in δ..δ+1,
        ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        - ( (if (|s|:ℝ) ≤ 2-β then
              Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
           + (if (|s|:ℝ) ≤ β then
              Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) ) := by
  intro δ hδ1 hδ2
  set a : ℝ := -δ with ha
  have ha6 : (1:ℝ)/6 ≤ a := by rw [ha]; linarith
  have ha2 : a ≤ 1/2 := by rw [ha]; linarith
  have hcongr : (∫ s in δ..(δ+1),
        ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        - ( (if (|s|:ℝ) ≤ 2-β then
              Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
           + (if (|s|:ℝ) ≤ β then
              Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) ))
      = ∫ s in δ..(δ+1), BWLH.BWL.WK β s := by
    apply intervalIntegral.integral_congr
    intro s _
    rw [← BWLH.WK_winI β s]
    ring
  rw [hcongr]
  rw [show δ + 1 = 1 - a by rw [ha]; ring, show δ = -a by rw [ha]; ring]
  rcases le_or_gt a (1/4) with ha14 | ha14
  · exact BWLH.regionA hβ0 hβ1 ha6 ha14
  · have ha4 : (1:ℝ)/4 ≤ a := le_of_lt ha14
    have ha0 : 0 < a := by linarith
    have h1a0 : 0 < 1-a := by linarith
    have ha5 : a ≤ 5/6 := by linarith
    have h1a5 : 1-a ≤ 5/6 := by linarith
    rw [BWLH.BWL.WK_split hβ0 hβ1 ha6 ha2]
    have h1 := BWLH.BWL.integral_Wg_le_WK hβ0 hβ1 ha0 ha5
    have h2 := BWLH.BWL.integral_Wg_le_WK hβ0 hβ1 h1a0 h1a5
    rw [BWLH.BWL.integral_Wg hβ0 hβ1 ha0 ha5] at h1
    rw [BWLH.BWL.integral_Wg hβ0 hβ1 h1a0 h1a5] at h2
    have hshift := BWLH.BWL.WJ_shift hβ0 hβ1 ha6 ha2
    have hint := BWLH.Wg_diff_integral_lb hβ0 hβ1 ha4 ha2
    have hreg := BWLH.regionB hβ0 hβ1
    have hW := BWLH.max_threshold_le hβ0 hβ1
    linarith

end Commons.Analysis.Integral
