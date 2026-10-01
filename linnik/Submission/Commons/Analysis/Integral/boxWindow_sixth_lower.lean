import Mathlib
import Submission.Commons.Analysis.Integral.boxWin_small_beta
import Submission.Commons.Analysis.Integral.wg_nonneg
import Submission.Commons.Analysis.Integral.boxWindow_sixth_upper
import Submission.Commons.Analysis.Integral.s_sq_HK_le_two
import Submission.Commons.Analysis.Integral.TT_zero_sub_sixth_le

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace BWSixthLower

open BoxWinSB

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-! ## Definitions -/

/-- Pointwise lower bound for the box-window integrand on `(0,1/6]`. -/
def Wg (β s : ℝ) : ℝ := TT β s - hBf β s - hbf β s

/-- The logarithmic jump constant `3/4 - log 2`. -/
def dlt : ℝ := 3/4 - Real.log 2

/-- Derivative of `TT β ·`. -/
def TTD (β x : ℝ) : ℝ :=
  - (26/5)*(3/2-β)*x/((3/2-β)^2+x^2)^2 - (26/5)*(1+β)*x/((1+β)^2+x^2)^2
  - ((2-β)^2-β^2)*x/((2-β)^2+x^2)^2
  - ((2-β)^2-β^2)^2*x/(2*((2-β)^2+x^2)^3)
  - 3*((2-β)^2-β^2)^3*x/(8*((2-β)^2+x^2)^4)

/-- Derivative of `Wg β ·` (logarithmic branch). -/
def WgD (β x : ℝ) : ℝ :=
  2/x - x*((26/5)*((3/2-β)/(((3/2-β)^2+x^2)^2) + (1+β)/(((1+β)^2+x^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+x^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+x^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+x^2)^4)
      + 1/(2*(2-β)^2) + 1/(2*β^2))

/-! ## `Mb ≤ hbf` -/

/-- The `β`-majorant is dominated by `hbf` (general `0 < β < 2`). -/
lemma Mb_le_hbf {β t : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (ht0 : 0 < t) :
    Mb β t ≤ hbf β t := by
  have hb : (0:ℝ) < 2 - β := by linarith
  have hbne : (2:ℝ) - β ≠ 0 := ne_of_gt hb
  have htne : t ≠ 0 := ne_of_gt ht0
  by_cases hc : t ≤ β
  · rw [Mb, hbf, if_pos hc, if_pos hc]
    have hmu1 : 1 ≤ (4*β^2+t^2)/(2*β*t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2*β - t)]
    have hlogmu : 0 ≤ Real.log ((4*β^2+t^2)/(2*β*t)) := Real.log_nonneg hmu1
    have hcoef : 1 - t^2/(2*((2-β)^2+β^2)) ≤ 1 := by
      have : (0:ℝ) ≤ t^2/(2*((2-β)^2+β^2)) := by positivity
      linarith
    have hsplit : (4*β^2+t^2)/(2*β*t) = (2*β/t) * (1 + t^2/(4*β^2)) := by
      field_simp
      ring
    have hlogeq : Real.log ((4*β^2+t^2)/(2*β*t))
        = Real.log (2*β) - Real.log t + Real.log (1 + t^2/(4*β^2)) := by
      rw [hsplit, Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity : (2:ℝ)*β ≠ 0) htne]
    have hle : Real.log (1 + t^2/(4*β^2)) ≤ t^2/(4*β^2) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + t^2/(4*β^2) by positivity)
      linarith
    have hmain : Real.log ((4*β^2+t^2)/(2*β*t)) ≤ Real.log (2*β) - Real.log t + t^2/(4*β^2) := by
      rw [hlogeq]; linarith
    have := mul_le_of_le_one_right hlogmu hcoef
    linarith [this, hmain]
  · rw [Mb, hbf, if_neg hc, if_neg hc]
    have hsqrt : (2-β) ≤ Real.sqrt ((2-β)^2+t^2) := by
      rw [Real.le_sqrt (le_of_lt hb) (by positivity)]
      nlinarith
    rw [le_div_iff₀ (by positivity : (0:ℝ) < t)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < t*Real.sqrt ((2-β)^2+t^2))]
    have hb1 : (0:ℝ) ≤ β*t := by positivity
    have h1 := mul_le_mul_of_nonneg_right hsqrt hb1
    nlinarith [h1]

/-- `Wg` is a pointwise lower bound for the integrand `F` on `(0,1/6]`. -/
lemma Wg_le_F {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6) :
    Wg β s ≤ BWSixth.F β s := by
  have hβ2 : β < 2 := by linarith
  have h1 : MB β s ≤ hBf β s := MB_le hβ0 hβ2 hs0
  have h2 : Mb β s ≤ hbf β s := Mb_le_hbf hβ0 hβ2 hs0
  simp only [Wg, BWSixth.F]
  linarith

/-! ## Monotonicity of `TT`, `hBf`, `hbf` -/

/-- `TT β ·` is antitone on `(0,∞)`. -/
lemma TT_antitone {β s u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 ≤ s) (hsu : s ≤ u) :
    TT β u ≤ TT β s := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hb : (0:ℝ) < 2-β := by linarith
  have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  have hsu2 : s^2 ≤ u^2 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u-s) (by linarith : (0:ℝ) ≤ u+s)]
  have hbase : (2-β)^2+s^2 ≤ (2-β)^2+u^2 := by nlinarith
  have h1 : (3/2-β)/((3/2-β)^2+u^2) ≤ (3/2-β)/((3/2-β)^2+s^2) := by
    apply div_le_div_of_nonneg_left hA.le (by positivity)
    nlinarith
  have h2 : (1+β)/((1+β)^2+u^2) ≤ (1+β)/((1+β)^2+s^2) := by
    apply div_le_div_of_nonneg_left hB.le (by positivity)
    nlinarith
  have h3 : ((2-β)^2-β^2)/(2*((2-β)^2+u^2)) ≤ ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) := by
    apply div_le_div_of_nonneg_left hC (by positivity)
    nlinarith
  have h4 : ((2-β)^2-β^2)^2/(8*((2-β)^2+u^2)^2) ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2-β)^2+s^2) hbase 2]
  have h5 : ((2-β)^2-β^2)^3/(16*((2-β)^2+u^2)^3) ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2-β)^2+s^2) hbase 3]
  simp only [TT]
  linarith

/-- `hBf β (1/6) ≤ hBf β s` for `0 < s ≤ 1/6`, `0 < β < 1`. -/
lemma hBf_sixth_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6) :
    hBf β (1/6) ≤ hBf β s := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hlog6 : Real.log (6*s) = Real.log s - Real.log (1/6) := by
    rw [show (6:ℝ)*s = s/(1/6) by ring, Real.log_div (ne_of_gt hs0) (by norm_num)]
  have h6s : (0:ℝ) < 6*s := by positivity
  have h1 : 1 - 6*s ≤ -(Real.log (6*s)) := by
    have := Real.log_le_sub_one_of_pos h6s; linarith
  have hdiff : hBf β s - hBf β (1/6)
      = -(Real.log (6*s)) + (s^2-(1/6)^2)/(4*(2-β)^2) := by
    simp only [hBf]
    rw [hlog6]; ring
  have hkey : -(1/6-s)*6 ≤ (s^2-(1/6)^2)/(4*(2-β)^2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*(2-β)^2)]
    have h1' : (0:ℝ) ≤ 1/6 - s := by linarith
    have h2' : (0:ℝ) ≤ 24*(2-β)^2 - (1/6+s) := by
      nlinarith [sq_nonneg ((2:ℝ)-β), hb, hs]
    have hmul := mul_nonneg h1' h2'
    nlinarith [hmul]
  linarith [hdiff, h1, hkey]


/-! ## `hbf` monotonicity facts -/

/-- `hbf β (1/6) ≤ hbf β s` for `1/6 ≤ β < 1`, `0 < s ≤ 1/6`. -/
lemma hbf_sixth_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ6 : 1/6 ≤ β)
    (hs0 : 0 < s) (hs : s ≤ 1/6) :
    hbf β (1/6) ≤ hbf β s := by
  have hbranch : s ≤ β := by linarith
  rw [hbf, hbf, if_pos hβ6, if_pos hbranch]
  have hlog6 : Real.log (6*s) = Real.log s - Real.log (1/6) := by
    rw [show (6:ℝ)*s = s/(1/6) by ring, Real.log_div (ne_of_gt hs0) (by norm_num)]
  have h6s : (0:ℝ) < 6*s := by positivity
  have h1 : 1 - 6*s ≤ -(Real.log (6*s)) := by
    have := Real.log_le_sub_one_of_pos h6s; linarith
  have hdiff : (Real.log (2*β) - Real.log s + s^2/(4*β^2))
      - (Real.log (2*β) - Real.log (1/6) + (1/6)^2/(4*β^2))
      = -(Real.log (6*s)) + (s^2-(1/6)^2)/(4*β^2) := by
    rw [hlog6]; ring
  have hkey : -(1/6-s)*6 ≤ (s^2-(1/6)^2)/(4*β^2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*β^2)]
    have h1' : (0:ℝ) ≤ 1/6 - s := by linarith
    have h2' : (0:ℝ) ≤ 24*β^2 - (1/6+s) := by nlinarith [hβ6]
    have hmul := mul_nonneg h1' h2'
    nlinarith [hmul]
  linarith [hdiff, h1, hkey]

/-- On the logarithmic branch `hbf β s ≥ log 2 + 1/4` (the value at `s = β`). -/
lemma hbf_logbranch_ge {β s : ℝ} (hβ0 : 0 < β) (hs0 : 0 < s) (hsβ : s ≤ β) :
    Real.log 2 + 1/4 ≤ hbf β s := by
  rw [hbf, if_pos hsβ]
  have hlog : Real.log (β/s) ≥ 1 - s/β := by
    have h1 : Real.log (s/β) ≤ s/β - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (s/β) = Real.log s - Real.log β := Real.log_div (ne_of_gt hs0) (ne_of_gt hβ0)
    have h3 : Real.log (β/s) = -(Real.log s - Real.log β) := by
      rw [Real.log_div (ne_of_gt hβ0) (ne_of_gt hs0)]; ring
    linarith
  have hsplit : Real.log (2*β) - Real.log s + s^2/(4*β^2) - (Real.log 2 + 1/4)
      = Real.log (β/s) + (s^2-β^2)/(4*β^2) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hβ0), Real.log_div (ne_of_gt hβ0) (ne_of_gt hs0)]
    field_simp
    ring
  have hkey : -(1 - s/β) ≤ (s^2-β^2)/(4*β^2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*β^2)]
    have hfac : (0:ℝ) ≤ β - s := by linarith
    have hfac2 : (0:ℝ) ≤ 3*β - s := by linarith
    have hmul := mul_nonneg hfac hfac2
    have heq : -(1 - s/β) * (4*β^2) = -4*β^2 + 4*β*s := by
      field_simp; ring
    rw [heq]; nlinarith [hmul]
  linarith [hsplit, hlog, hkey]

/-- On the `else` branch `hbf β s ≥ 6β = hbf β (1/6)` when `β < 1/6`. -/
lemma hbf_elsebranch_ge {β s : ℝ} (hβ0 : 0 < β) (hs0 : 0 < s) (hs : s ≤ 1/6)
    (hβs : ¬ s ≤ β) :
    6*β ≤ hbf β s := by
  rw [hbf, if_neg hβs]
  rw [le_div_iff₀ hs0]
  have h6s : 6*s ≤ 1 := by linarith
  nlinarith [hβ0, h6s]

/-! ## The logarithmic branch and its derivative -/

/-- The logarithmic branch of `hbf`. -/
def hbflog (β x : ℝ) : ℝ := Real.log (2*β) - Real.log x + x^2/(4*β^2)

/-- The logarithmic version of `Wg`. -/
def Wglog (β x : ℝ) : ℝ := TT β x - hBf β x - hbflog β x

lemma hbflog_eq_hbf {β x : ℝ} (hxβ : x ≤ β) : hbflog β x = hbf β x := by
  rw [hbf, if_pos hxβ]; rfl

lemma Wglog_eq_Wg {β x : ℝ} (hxβ : x ≤ β) : Wglog β x = Wg β x := by
  rw [Wg, Wglog, hbflog_eq_hbf hxβ]

/-! ### Derivative atoms -/

lemma hasDerivAt_const_div {c d x : ℝ} (hd : 0 ≤ d) (hx0 : 0 < x) :
    HasDerivAt (fun u : ℝ => c/(d+u^2)) (-(2*c*x)/(d+x^2)^2) x := by
  have hden : HasDerivAt (fun u : ℝ => d+u^2) (2*x) x := by
    have h : HasDerivAt (fun u : ℝ => u^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
    simpa using h.const_add d
  have hne : d+x^2 ≠ 0 := by positivity
  have hh := (hasDerivAt_const x c).div hden hne
  refine hh.congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_const_div_sq {c d x : ℝ} (hd : 0 ≤ d) (hx0 : 0 < x) :
    HasDerivAt (fun u : ℝ => c/(d+u^2)^2) (-(4*c*x)/(d+x^2)^3) x := by
  have h : HasDerivAt (fun u : ℝ => d+u^2) (2*x) x := by
    have hh : HasDerivAt (fun u : ℝ => u^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
    simpa using hh.const_add d
  have hden : HasDerivAt ((fun u : ℝ => d+u^2)^2) (2*(d+x^2)*(2*x)) x := by
    have h2 := h.pow 2
    convert h2 using 1
    all_goals first | rfl | ring_nf | norm_num
  have hne : (d+x^2)^2 ≠ 0 := by positivity
  have hh := (hasDerivAt_const x c).div hden (by simpa [Pi.pow_apply] using hne)
  refine hh.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_const_div_cube {c d x : ℝ} (hd : 0 ≤ d) (hx0 : 0 < x) :
    HasDerivAt (fun u : ℝ => c/(d+u^2)^3) (-(6*c*x)/(d+x^2)^4) x := by
  have h : HasDerivAt (fun u : ℝ => d+u^2) (2*x) x := by
    have hh : HasDerivAt (fun u : ℝ => u^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
    simpa using hh.const_add d
  have hden : HasDerivAt ((fun u : ℝ => d+u^2)^3) (3*(d+x^2)^2*(2*x)) x := by
    have h2 := h.pow 3
    convert h2 using 1
    all_goals first | rfl | ring_nf | norm_num
  have hne : (d+x^2)^3 ≠ 0 := by positivity
  have hh := (hasDerivAt_const x c).div hden (by simpa [Pi.pow_apply] using hne)
  refine hh.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_log_sub {c x : ℝ} (hx0 : 0 < x) :
    HasDerivAt (fun u : ℝ => Real.log c - Real.log u) (-1/x) x := by
  have hlog : HasDerivAt Real.log (1/x) x := by simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx0)
  have h := (hasDerivAt_const x (Real.log c)).sub hlog
  have hh : ((fun _ : ℝ => Real.log c) - Real.log) = (fun u : ℝ => Real.log c - Real.log u) := by
    funext u; rfl
  rw [hh] at h
  refine h.congr_deriv ?_
  rw [one_div]; ring

lemma hasDerivAt_sq_div {e x : ℝ} (he : e ≠ 0) :
    HasDerivAt (fun u : ℝ => u^2/(4*e)) (x/(2*e)) x := by
  have h : HasDerivAt (fun u : ℝ => u^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
  have h2 := h.div_const (4*e)
  refine h2.congr_deriv ?_
  field_simp
  ring

/-- Derivative of `TT β`. -/
lemma hasDerivAt_TT (β x : ℝ) (hx0 : 0 < x) :
    HasDerivAt (TT β) (TTD β x) x := by
  have h12 := (hasDerivAt_const_div (c := 3/2-β) (d := (3/2-β)^2) (sq_nonneg _) hx0).add
      (hasDerivAt_const_div (c := 1+β) (d := (1+β)^2) (sq_nonneg _) hx0)
  have h1 := h12.const_mul (13/5)
  have h3' := hasDerivAt_const_div (c := ((2-β)^2-β^2)/2) (d := (2-β)^2) (sq_nonneg _) hx0
  have h3 := h3'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext u; rw [div_div]))
  have h4' := hasDerivAt_const_div_sq (c := ((2-β)^2-β^2)^2/8) (d := (2-β)^2) (sq_nonneg _) hx0
  have h4 := h4'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext u; rw [div_div]))
  have h5' := hasDerivAt_const_div_cube (c := ((2-β)^2-β^2)^3/16) (d := (2-β)^2) (sq_nonneg _) hx0
  have h5 := h5'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext u; rw [div_div]))
  have hsum := (((h1.add h3).add h4).add h5)
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · apply Filter.EventuallyEq.of_eq
    funext u
    simp only [TT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · unfold TTD
    field_simp
    ring

/-- Derivative of `Wglog β`. -/
lemma hasDerivAt_Wglog {β x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 < x) :
    HasDerivAt (Wglog β) (WgD β x) x := by
  have hTT := hasDerivAt_TT β x hx0
  have h2b : (2:ℝ)-β ≠ 0 := by linarith
  have hB : HasDerivAt (fun u : ℝ => Real.log (2*(2-β)) - Real.log u + u^2/(4*(2-β)^2))
      (-1/x + x/(2*(2-β)^2)) x := by
    have h1 := hasDerivAt_log_sub (c := 2*(2-β)) hx0
    have h2 := hasDerivAt_sq_div (e := (2-β)^2) (pow_ne_zero 2 h2b) (x:=x)
    refine (h1.add h2).congr_of_eventuallyEq ?_
    apply Filter.EventuallyEq.of_eq
    funext u
    simp only [Pi.add_apply]
  have hb : HasDerivAt (hbflog β) (-1/x + x/(2*β^2)) x := by
    have h1 := hasDerivAt_log_sub (c := 2*β) hx0
    have h2 := hasDerivAt_sq_div (e := β^2) (pow_ne_zero 2 (ne_of_gt hβ0)) (x:=x)
    refine (h1.add h2).congr_of_eventuallyEq ?_
    apply Filter.EventuallyEq.of_eq
    funext u
    simp only [hbflog, Pi.add_apply]
  refine ((hTT.sub hB).sub hb).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · apply Filter.EventuallyEq.of_eq
    funext u
    simp only [Wglog, hBf, Pi.sub_apply]
  · unfold WgD TTD
    field_simp
    ring

/-! ## The bound `H0 ≤ 54` for the derivative of `TT` -/

/-- The value of the `H`-function at `0`. -/
def H0 (β : ℝ) : ℝ :=
  (26/5)*(1/(3/2-β)^3 + 1/(1+β)^3) + ((2-β)^2-β^2)/(2-β)^4
    + ((2-β)^2-β^2)^2/(2*(2-β)^6) + 3*((2-β)^2-β^2)^3/(8*(2-β)^8)

lemma H0_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ H0 β := by
  rw [H0]
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hb : (0:ℝ) < 2-β := by linarith
  have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  have h1 : (0:ℝ) ≤ 1/(3/2-β)^3 := by positivity
  have h2 : (0:ℝ) ≤ 1/(1+β)^3 := by positivity
  have h3 : (0:ℝ) ≤ ((2-β)^2-β^2)/(2-β)^4 := by positivity
  have h4 : (0:ℝ) ≤ ((2-β)^2-β^2)^2/(2*(2-β)^6) := by positivity
  have h5 : (0:ℝ) ≤ 3*((2-β)^2-β^2)^3/(8*(2-β)^8) := by positivity
  linarith

/-- `TT β b - TT β a ≤ (H0 β/6)(b-a)` for `0 < a ≤ b ≤ 1/6`. -/
lemma TT_sub_le {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a) (hab : a ≤ b)
    (hb6 : b ≤ 1/6) :
    TT β b - TT β a ≤ (H0 β/6)*(b-a) := by
  have h1 : TT β b ≤ TT β a := TT_antitone hβ0 hβ1 ha0.le hab
  have h2 : 0 ≤ H0 β := H0_nonneg hβ0 hβ1
  nlinarith [h1, h2, hab]

lemma TT_sub_le' {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a) (hab : a ≤ b)
    (hb6 : b ≤ 1/6) :
    TT β b - TT β a ≤ 9*(b-a) := by
  have h1 : TT β b ≤ TT β a := TT_antitone hβ0 hβ1 ha0.le hab
  nlinarith [h1, hab]

/-- Upper bound for the `H`-function. -/
lemma Hx_le_H0 {β v : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hv : 0 ≤ v) :
    (26/5)*((3/2-β)/(((3/2-β)^2+v^2)^2) + (1+β)/(((1+β)^2+v^2)^2))
    + ((2-β)^2-β^2)/(((2-β)^2+v^2)^2)
    + ((2-β)^2-β^2)^2/(2*((2-β)^2+v^2)^3)
    + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+v^2)^4) ≤ H0 β := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hb : (0:ℝ) < 2-β := by linarith
  have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  have e1 : (3/2-β)/(((3/2-β)^2+v^2)^2) ≤ 1/(3/2-β)^3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity : (0:ℝ) < (3/2-β)^3)]
    nlinarith [pow_le_pow_left₀ (sq_nonneg (3/2-β)) (by nlinarith : (3/2-β)^2 ≤ (3/2-β)^2+v^2) 2]
  have e2 : (1+β)/(((1+β)^2+v^2)^2) ≤ 1/(1+β)^3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity : (0:ℝ) < (1+β)^3)]
    nlinarith [pow_le_pow_left₀ (sq_nonneg (1+β)) (by nlinarith : (1+β)^2 ≤ (1+β)^2+v^2) 2]
  have e3 : ((2-β)^2-β^2)/(((2-β)^2+v^2)^2) ≤ ((2-β)^2-β^2)/(2-β)^4 := by
    apply div_le_div_of_nonneg_left hC (by positivity)
    nlinarith [pow_le_pow_left₀ (sq_nonneg (2-β)) (by nlinarith : (2-β)^2 ≤ (2-β)^2+v^2) 2]
  have e4 : ((2-β)^2-β^2)^2/(2*((2-β)^2+v^2)^3) ≤ ((2-β)^2-β^2)^2/(2*(2-β)^6) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [pow_le_pow_left₀ (sq_nonneg (2-β)) (by nlinarith : (2-β)^2 ≤ (2-β)^2+v^2) 3]
  have e5 : 3*((2-β)^2-β^2)^3/(8*((2-β)^2+v^2)^4) ≤ 3*((2-β)^2-β^2)^3/(8*(2-β)^8) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [pow_le_pow_left₀ (sq_nonneg (2-β)) (by nlinarith : (2-β)^2 ≤ (2-β)^2+v^2) 4]
  rw [H0]
  linarith

lemma H0_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : H0 β ≤ 54 := by
  have hA : (1/2:ℝ) ≤ 3/2-β := by linarith
  have hB : (1:ℝ) ≤ 1+β := by linarith
  have hA3 : (1:ℝ)/(3/2-β)^3 ≤ 8 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hA 3]
  have hB3 : (1:ℝ)/(1+β)^3 ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hB 3]
  have hb : (0:ℝ) < 2-β := by linarith
  have ht : (0:ℝ) ≤ 1-β := by linarith
  have hCeq : (2-β)^2-β^2 = 4*(1-β) := by ring
  have hbt : (2:ℝ)-β = 1+(1-β) := by ring
  have e1 : ((2-β)^2-β^2)/(2-β)^4 ≤ 1 := by
    rw [hCeq, hbt, div_le_one (by positivity)]
    nlinarith [ht, sq_nonneg (1-β), pow_nonneg ht 3, pow_nonneg ht 4]
  have hb6 : (1+(1-β))^6 = 1+6*(1-β)+15*(1-β)^2+20*(1-β)^3+15*(1-β)^4+6*(1-β)^5+(1-β)^6 := by ring
  have e2 : ((2-β)^2-β^2)^2/(2*(2-β)^6) ≤ 8/15 := by
    rw [hCeq, hbt, div_le_iff₀ (by positivity)]
    nlinarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5, pow_nonneg ht 6]
  have e3 : 3*((2-β)^2-β^2)^3/(8*(2-β)^8) ≤ 3/7 := by
    rw [hCeq, hbt, div_le_iff₀ (by positivity)]
    nlinarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8]
  rw [H0]
  nlinarith [hA3, hB3, e1, e2, e3]

/-- `-(1/6)·H0 ≤ TTD β v` on `(0,1/6]`. -/
lemma TTD_ge {β v : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hv0 : 0 < v) (hv6 : v ≤ 1/6) :
    -(H0 β/6) ≤ TTD β v := by
  have hH := Hx_le_H0 hβ0 hβ1 hv0.le
  have hH0 := H0_le hβ0 hβ1
  have hbr : (0:ℝ) ≤ (26/5)*((3/2-β)/(((3/2-β)^2+v^2)^2) + (1+β)/(((1+β)^2+v^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+v^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+v^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+v^2)^4) := by
    have hA : (0:ℝ) < 3/2-β := by linarith
    have hB : (0:ℝ) < 1+β := by linarith
    have hb : (0:ℝ) < 2-β := by linarith
    have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
    positivity
  have hv : v*((26/5)*((3/2-β)/(((3/2-β)^2+v^2)^2) + (1+β)/(((1+β)^2+v^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+v^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+v^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+v^2)^4)) ≤ H0 β/6 := by
    nlinarith [hH, hbr, hv6]
  have key2 : TTD β v = -(v*((26/5)*((3/2-β)/(((3/2-β)^2+v^2)^2) + (1+β)/(((1+β)^2+v^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+v^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+v^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+v^2)^4))) := by
    rw [TTD]; ring
  rw [key2]; linarith [hv]

/-- `TTD β v ≤ 0`. -/
lemma TTD_nonpos {β v : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hv0 : 0 < v) : TTD β v ≤ 0 := by
  have hbr : (0:ℝ) ≤ (26/5)*((3/2-β)/(((3/2-β)^2+v^2)^2) + (1+β)/(((1+β)^2+v^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+v^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+v^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+v^2)^4) := by
    have hA : (0:ℝ) < 3/2-β := by linarith
    have hB : (0:ℝ) < 1+β := by linarith
    have hb : (0:ℝ) < 2-β := by linarith
    have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
    positivity
  have key2 : TTD β v = -(v*((26/5)*((3/2-β)/(((3/2-β)^2+v^2)^2) + (1+β)/(((1+β)^2+v^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+v^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+v^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+v^2)^4))) := by
    rw [TTD]; ring
  rw [key2]; nlinarith [hbr, hv0]

/-- `TTD β` is interval integrable on `[a,b]` for `0 < a ≤ b ≤ 1/6`. -/
lemma intervalIntegrable_TTD {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a)
    (hab : a ≤ b) (hb6 : b ≤ 1/6) :
    IntervalIntegrable (TTD β) volume a b := by
  refine IntervalIntegrable.mono_fun' (f := TTD β) (g := fun _ : ℝ => H0 β/6) intervalIntegrable_const ?_ ?_
  · exact (by unfold TTD; fun_prop : Measurable (TTD β)).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro v hv
    rw [Set.uIoc_of_le hab] at hv
    obtain ⟨hv1, hv2⟩ := hv
    have hv0 : 0 < v := lt_trans ha0 hv1
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨TTD_ge hβ0 hβ1 hv0 (le_trans hv2 hb6), ?_⟩
    have h2 := TTD_nonpos hβ0 hβ1 hv0
    have h3 := H0_le hβ0 hβ1
    have h4 := H0_nonneg hβ0 hβ1
    linarith

/-- `TT β a - TT β b ≤ 9(b-a)` for `0 < a ≤ b ≤ 1/6`. -/
lemma TT_decrease_le {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a) (hab : a ≤ b)
    (hb6 : b ≤ 1/6) :
    TT β a - TT β b ≤ 9*(b-a) := by
  have hderiv : ∀ v ∈ Set.uIcc a b, HasDerivAt (TT β) (TTD β v) v := by
    intro v hv
    rw [Set.uIcc_of_le hab] at hv
    exact hasDerivAt_TT β v (lt_of_lt_of_le ha0 hv.1)
  have hint : IntervalIntegrable (TTD β) volume a b := intervalIntegrable_TTD hβ0 hβ1 ha0 hab hb6
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hm : (∫ v in a..b, -TTD β v) ≤ ∫ v in a..b, (fun _ : ℝ => (9:ℝ)) v := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab hint.neg intervalIntegrable_const
    intro v hv
    have hv0 : 0 < v := lt_trans ha0 hv.1
    have h1 : -(H0 β/6) ≤ TTD β v := TTD_ge hβ0 hβ1 hv0 (le_trans hv.2.le hb6)
    have h2 := H0_le hβ0 hβ1
    show -TTD β v ≤ (9:ℝ)
    nlinarith [h1, h2]
  rw [intervalIntegral.integral_neg, hFT, intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  linarith [hm]

/-- `WgD β ≥ 0` on `(0, min(β,1/6)]`. -/
lemma WgD_nonneg {β x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 < x) (hxβ : x ≤ β)
    (hx6 : x ≤ 1/6) :
    0 ≤ WgD β x := by
  have hK := s_sq_HK_le_two hβ0 hβ1 hx0 hxβ hx6
  have h : x*((26/5)*((3/2-β)/(((3/2-β)^2+x^2)^2) + (1+β)/(((1+β)^2+x^2)^2))
      + ((2-β)^2-β^2)/(((2-β)^2+x^2)^2)
      + ((2-β)^2-β^2)^2/(2*((2-β)^2+x^2)^3)
      + 3*((2-β)^2-β^2)^3/(8*((2-β)^2+x^2)^4)
      + 1/(2*(2-β)^2) + 1/(2*β^2)) ≤ 2/x := by
    rw [le_div_iff₀ hx0]
    nlinarith [hK]
  rw [WgD]
  linarith

/-- `Wg` is monotone on the logarithmic branch. -/
lemma Wg_mono_log {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a) (hab : a ≤ b)
    (hbβ : b ≤ β) (hb6 : b ≤ 1/6) : Wg β a ≤ Wg β b := by
  have hderiv : ∀ v ∈ Set.uIcc a b, HasDerivAt (Wglog β) (WgD β v) v := by
    intro v hv
    rw [Set.uIcc_of_le hab] at hv
    exact hasDerivAt_Wglog hβ0 hβ1 (lt_of_lt_of_le ha0 hv.1)
  have hint : IntervalIntegrable (WgD β) volume a b := by
    have hTTD : IntervalIntegrable (TTD β) volume a b := intervalIntegrable_TTD hβ0 hβ1 ha0 hab hb6
    have h2v : IntervalIntegrable (fun v : ℝ => 2/v) volume a b := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro v hv
      rw [Set.uIcc_of_le hab] at hv
      exact ne_of_gt (lt_of_lt_of_le ha0 hv.1)
    have hlin1 : IntervalIntegrable (fun v : ℝ => v/(2*(2-β)^2)) volume a b := by
      have h2b : (0:ℝ) < 2-β := by linarith
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_id continuousOn_const
      intro v hv
      exact ne_of_gt (by positivity)
    have hlin2 : IntervalIntegrable (fun v : ℝ => v/(2*β^2)) volume a b := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_id continuousOn_const
      intro v hv
      exact ne_of_gt (by positivity)
    have hkey : WgD β = fun v : ℝ => TTD β v + 2/v - v/(2*(2-β)^2) - v/(2*β^2) := by
      funext v; unfold WgD TTD; ring
    rw [hkey]
    exact ((hTTD.add h2v).sub hlin1).sub hlin2
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hnn : 0 ≤ ∫ v in a..b, WgD β v := by
    apply intervalIntegral.integral_nonneg hab
    intro v hv
    exact WgD_nonneg hβ0 hβ1 (lt_of_lt_of_le ha0 hv.1) (le_trans hv.2 hbβ) (le_trans hv.2 hb6)
  rw [← Wglog_eq_Wg (le_trans hab hbβ), ← Wglog_eq_Wg hbβ]
  linarith [hFT, hnn]

/-- For `β ≥ 1/6`, `Wg β s ≤ Wg β (1/6)` on `(0,1/6]`. -/
lemma Wg_le_sixth {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ6 : 1/6 ≤ β)
    (hs0 : 0 < s) (hs : s ≤ 1/6) :
    Wg β s ≤ Wg β (1/6) :=
  Wg_mono_log hβ0 hβ1 hs0 hs (by linarith) (by norm_num)

/-- `Wg β (1/6) ≥ 0`. -/
lemma Wg_sixth_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ Wg β (1/6) := by
  have h := wg_nonneg hβ0 hβ1 (by norm_num : (1:ℝ)/6 ≤ 1/6) (by norm_num : (1:ℝ)/6 ≤ 5/6)
  simpa only [Wg, TT, hBf, hbf] using h

/-- On the `else` branch (`β < s ≤ 1/6`), `Wg β s ≤ Wg β (1/6) + 7/50`. -/
lemma Wg_else_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ16 : β < 1/6)
    (hs0 : 0 < s) (hβs : β < s) (hs6 : s ≤ 1/6) :
    Wg β s ≤ Wg β (1/6) + 7/50 := by
  have hΔ := TT_zero_sub_sixth_le hβ0 hβ1 (le_of_lt hβ16)
  have hWeq : Wg β (1/6) = TT β (1/6) - hBf β (1/6) - 6*β := by
    rw [Wg, hbf, if_neg (not_le.mpr hβ16)]
    field_simp
  have hcb : hbf β (1/6) = 6*β := by
    rw [hbf, if_neg (not_le.mpr hβ16)]; field_simp
  have hV : Wg β s = TT β s - hBf β s - β/s := by
    rw [Wg, hbf, if_neg (not_le.mpr hβs)]
  rw [hV, hWeq]
  have hb : (0:ℝ) < 2-β := by linarith
  have h1 : TT β s ≤ TT β 0 := TT_antitone hβ0 hβ1 (le_refl 0) (by positivity)
  have h2 : hBf β s ≥ hBf β (1/6) := hBf_sixth_le hβ0 hβ1 hs0 hs6
  have h3 : 6*β ≤ β/s := by
    rw [le_div_iff₀ hs0]; nlinarith [hβ0, hβs, hs6]
  linarith [hΔ]

/-- On the logarithmic branch (`s ≤ β < 1/6`), `Wg β s ≤ Wg β (1/6) + 7/50`. -/
lemma Wg_log_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ16 : β < 1/6)
    (hs0 : 0 < s) (hsβ : s ≤ β) :
    Wg β s ≤ Wg β (1/6) + 7/50 := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hWeq : Wg β (1/6) = TT β (1/6) - hBf β (1/6) - 6*β := by
    rw [Wg, hbf, if_neg (not_le.mpr hβ16)]
    field_simp
  have hmono : Wg β s ≤ Wg β β :=
    Wg_mono_log (a := s) (b := β) hβ0 hβ1 hs0 hsβ le_rfl (le_of_lt hβ16)
  have hWβ : Wg β β = TT β β - hBf β β - (Real.log 2 + 1/4) := by
    rw [Wg, hbf, if_pos le_rfl, Real.log_mul (by norm_num) (ne_of_gt hβ0)]
    field_simp
    ring
  have hTT : TT β β - TT β (1/6) ≤ 9*(1/6-β) :=
    TT_decrease_le hβ0 hβ1 hβ0 (le_of_lt hβ16) (le_refl (1/6))
  have hbl : hBf β (1/6) - hBf β β ≤ -(1/6-β)*(71/12) := by
    have hlog6' : Real.log (6*β) = Real.log β - Real.log (1/6) := by
      rw [show (6:ℝ)*β = β/(1/6) by ring, Real.log_div (ne_of_gt hβ0) (by norm_num)]
    have hbd : hBf β (1/6) - hBf β β
        = Real.log (6*β) + ((1/6)^2 - β^2)/(4*(2-β)^2) := by
      simp only [hBf]; rw [hlog6']; ring
    have h1 : Real.log (6*β) ≤ -6*(1/6-β) := by
      have hx : (0:ℝ) < 6*β := by positivity
      have h := Real.log_le_sub_one_of_pos hx
      linarith
    have h2 : ((1/6)^2 - β^2)/(4*(2-β)^2) ≤ (1/6-β)*(1/12) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg β, hβ16]
    rw [hbd]; nlinarith [h1, h2]
  have hdlt : dlt ≤ 7/50 := by rw [dlt]; linarith [Real.log_two_gt_d9]
  have hdl : 6*β - (Real.log 2 + 1/4) = dlt - (1 - 6*β) := by rw [dlt]; ring
  have h6 : (1:ℝ) - 6*β ≥ 0 := by linarith
  have hfin : Wg β β ≤ Wg β (1/6) + 7/50 := by
    rw [hWβ, hWeq]; linarith [hTT, hbl, hdlt, hdl]
  linarith [hmono, hfin]

/-- For `β ≤ 1/6`, `Wg β s ≤ Wg β (1/6) + 7/50` on `(0,1/6]`. -/
lemma Wg_le_sixth_small {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ6 : β ≤ 1/6)
    (hs0 : 0 < s) (hs : s ≤ 1/6) :
    Wg β s ≤ Wg β (1/6) + 7/50 := by
  rcases lt_or_eq_of_le hβ6 with hlt | heq
  · by_cases hsb : s ≤ β
    · exact Wg_log_le hβ0 hβ1 hlt hs0 hsb
    · exact Wg_else_le hβ0 hβ1 hlt hs0 (lt_of_not_ge hsb) hs
  · subst heq
    exact le_trans (Wg_le_sixth hβ0 hβ1 le_rfl hs0 hs) (by linarith)


/-! ## Integrability on `[0,1/6]` -/

lemma intervalIntegrable_hBf_sixth {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (hBf β) volume (0:ℝ) (1/6) := by
  have heq : hBf β = fun s : ℝ => Real.log (2*(2-β)) - Real.log s + s^2/(4*(2-β)^2) := rfl
  rw [heq]
  exact (intervalIntegrable_const.sub intervalIntegrable_log').add
    (by apply Continuous.intervalIntegrable; fun_prop)

lemma intervalIntegrable_hbf_sixth {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (hbf β) volume (0:ℝ) (1/6) := by
  refine IntervalIntegrable.mono_fun' (f := hbf β)
    (g := fun s : ℝ => |Real.log (2*β)| + (-Real.log s) + s^2/(4*β^2) + 3) ?_ ?_ ?_
  · have h1 : IntervalIntegrable (fun s : ℝ => |Real.log (2*β)|) volume (0:ℝ) (1/6) :=
      intervalIntegrable_const
    exact (((h1.add intervalIntegrable_log'.neg).add
      (by apply Continuous.intervalIntegrable; fun_prop)).add intervalIntegrable_const)
  · exact (measurable_hbf β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/6)] at hs
    obtain ⟨hs0, hs6⟩ := hs
    rw [Real.norm_eq_abs]
    by_cases hc : s ≤ β
    · rw [hbf, if_pos hc]
      have hlog0 : Real.log s ≤ 0 := Real.log_nonpos hs0.le (by linarith)
      have habs : |Real.log (2*β) - Real.log s + s^2/(4*β^2)| ≤ |Real.log (2*β)| + (-Real.log s) + s^2/(4*β^2) := by
        have e1 : |Real.log (2*β) - Real.log s + s^2/(4*β^2)|
            ≤ |Real.log (2*β) - Real.log s| + |s^2/(4*β^2)| := abs_add_le _ _
        have e2 : |Real.log (2*β) - Real.log s| ≤ |Real.log (2*β)| + |Real.log s| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (Real.log (2*β)) (-Real.log s)
        have e3 : |Real.log s| = -Real.log s := abs_of_nonpos hlog0
        have e4 : |s^2/(4*β^2)| = s^2/(4*β^2) := abs_of_nonneg (by positivity)
        linarith [e1, e2, e3, e4]
      have hlog2 : 0 ≤ |Real.log (2*β)| := abs_nonneg _
      have hlog0' : 0 ≤ -Real.log s := by linarith
      have hs2 : 0 ≤ s^2/(4*β^2) := by positivity
      linarith [habs]
    · rw [hbf, if_neg hc]
      have h1 : β/s ≤ 1 := by rw [div_le_one hs0]; linarith
      have hpos : 0 ≤ β/s := by positivity
      rw [abs_of_nonneg hpos]
      have hlog2 : 0 ≤ |Real.log (2*β)| := abs_nonneg _
      have hlog0 : 0 ≤ -Real.log s := by linarith [Real.log_nonpos hs0.le (by linarith)]
      have hs2 : 0 ≤ s^2/(4*β^2) := by positivity
      linarith

/-- `Wg β` is interval integrable on `[0,1/6]`. -/
lemma intervalIntegrable_Wg_sixth {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (Wg β) volume (0:ℝ) (1/6) := by
  have h1 : IntervalIntegrable (TT β) volume (0:ℝ) (1/6) := BWSixth.intervalIntegrable_TT hβ0 hβ1
  have h2 : IntervalIntegrable (hBf β) volume (0:ℝ) (1/6) := intervalIntegrable_hBf_sixth hβ0 hβ1
  have h3 : IntervalIntegrable (hbf β) volume (0:ℝ) (1/6) := intervalIntegrable_hbf_sixth hβ0 hβ1
  have h := (h1.sub h2).sub h3
  rwa [show (fun s : ℝ => TT β s - hBf β s - hbf β s) = Wg β from rfl] at h

/-! ## The bounds for `∫_0^{1/6} TT`, `∫_0^{1/6} hBf` and `∫_0^{1/6} hbf` -/

lemma integral_TT_sixth_ge {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (1/6)*TT β (1/6) ≤ ∫ s in (0:ℝ)..(1/6), TT β s := by
  have hmono : (∫ s in (0:ℝ)..(1/6), (TT β (1/6) : ℝ)) ≤ ∫ s in (0:ℝ)..(1/6), TT β s := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) intervalIntegrable_const
      (BWSixth.intervalIntegrable_TT hβ0 hβ1)
    intro s hs
    exact TT_antitone hβ0 hβ1 hs.1.le (le_of_lt hs.2)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  linarith [hmono]

lemma integral_hBf_sixth_sub_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ s in (0:ℝ)..(1/6), (hBf β s - hBf β (1/6))) ≤ 1/6 := by
  have hpt : ∀ s ∈ Set.Ioo (0:ℝ) (1/6), hBf β s - hBf β (1/6) ≤ Real.log ((1/6)/s) := by
    intro s hs
    have hd : hBf β s - hBf β (1/6) = Real.log ((1/6)/s) + (s^2-(1/6)^2)/(4*(2-β)^2) := by
      simp only [hBf]
      rw [Real.log_div (by norm_num) (ne_of_gt hs.1)]; ring
    rw [hd]
    have h2 : (s^2-(1/6)^2)/(4*(2-β)^2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [hs.1, hs.2]
    linarith
  have hi1 : IntervalIntegrable (fun s : ℝ => hBf β s - hBf β (1/6)) volume (0:ℝ) (1/6) :=
    (intervalIntegrable_hBf_sixth hβ0 hβ1).sub intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.log ((1/6)/s)) volume (0:ℝ) (1/6) :=
    BWSixth.intervalIntegrable_log_div (by norm_num)
  have hmono : (∫ s in (0:ℝ)..(1/6), (hBf β s - hBf β (1/6))) ≤
      ∫ s in (0:ℝ)..(1/6), Real.log ((1/6)/s) :=
    intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi1 hi2 hpt
  rw [BWSixth.integral_log_div (by norm_num : (0:ℝ) < 1/6) (by norm_num : (0:ℝ) < 1/6)] at hmono
  norm_num at hmono
  linarith [hmono]

lemma integral_hbf_sixth_sub_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ6 : 1/6 ≤ β) :
    (∫ s in (0:ℝ)..(1/6), (hbf β s - hbf β (1/6))) ≤ 1/6 := by
  have hc : hbf β (1/6) = Real.log (2*β) - Real.log (1/6) + (1/6)^2/(4*β^2) := by
    rw [hbf, if_pos hβ6]
  have hpt : ∀ s ∈ Set.Ioo (0:ℝ) (1/6),
      hbf β s - hbf β (1/6) ≤ Real.log ((1/6)/s) := by
    intro s hs
    have hsβ : s ≤ β := le_trans (le_of_lt hs.2) hβ6
    rw [hbf, hbf, if_pos hsβ, if_pos hβ6, Real.log_div (by norm_num) (ne_of_gt hs.1)]
    have h2 : s^2/(4*β^2) - (1/6)^2/(4*β^2) ≤ 0 := by
      rw [← sub_div]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [hs.1, hs.2]
    linarith [h2]
  have hi1 : IntervalIntegrable (fun s : ℝ => hbf β s - hbf β (1/6)) volume (0:ℝ) (1/6) :=
    (intervalIntegrable_hbf_sixth hβ0 hβ1).sub intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.log ((1/6)/s)) volume (0:ℝ) (1/6) :=
    BWSixth.intervalIntegrable_log_div (by norm_num)
  have hmono : (∫ s in (0:ℝ)..(1/6), (hbf β s - hbf β (1/6))) ≤
      ∫ s in (0:ℝ)..(1/6), Real.log ((1/6)/s) :=
    intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi1 hi2 hpt
  rw [BWSixth.integral_log_div (by norm_num : (0:ℝ) < 1/6) (by norm_num : (0:ℝ) < 1/6)] at hmono
  norm_num at hmono
  linarith [hmono]


/-- `∫_0^{1/6}(hbf β s - hbf β (1/6)) ≤ 1/8 + 1/72` for `β < 1/6`. -/
lemma integral_hbf_sixth_sub_le_small {β : ℝ} (hβ0 : 0 < β) (hβ16 : β < 1/6) :
    (∫ s in (0:ℝ)..(1/6), (hbf β s - hbf β (1/6))) ≤ 1/8 + 1/72 := by
  have hc : hbf β (1/6) = 6*β := by rw [hbf, if_neg (not_le.mpr hβ16)]; field_simp
  rw [hc]
  have hβle : (0:ℝ) ≤ β := hβ0.le
  have hle16 : β ≤ 1/6 := le_of_lt hβ16
  have hi : IntervalIntegrable (fun s : ℝ => hbf β s - 6*β) volume (0:ℝ) (1/6) :=
    (intervalIntegrable_hbf_sixth hβ0 (by linarith)).sub intervalIntegrable_const
  have hi1 : IntervalIntegrable (fun s : ℝ => hbf β s - 6*β) volume (0:ℝ) β :=
    hi.mono_set (by
      intro x hx
      rw [Set.uIcc_of_le hβle] at hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/6)]
      exact ⟨hx.1, le_trans hx.2 hle16⟩)
  have hi2 : IntervalIntegrable (fun s : ℝ => hbf β s - 6*β) volume β (1/6) :=
    hi.mono_set (by
      intro x hx
      rw [Set.uIcc_of_le hle16] at hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/6)]
      exact ⟨le_trans hβle hx.1, hx.2⟩)
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  rw [hsplit]
  have e1 : (∫ s in (0:ℝ)..β, (hbf β s - 6*β)) = β*(Real.log 2 + 1) + β/12 - 6*β^2 := by
    have hcongr : (∫ s in (0:ℝ)..β, (hbf β s - 6*β))
        = ∫ s in (0:ℝ)..β, (Real.log ((2*β)/s) + s^2/(4*β^2) - 6*β) := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le hβle] at hs
      simp only [hbf, if_pos hs.2]
      rw [← Real.log_div (by positivity) (ne_of_gt hs.1)]
    rw [hcongr]
    have hA : IntervalIntegrable (fun s : ℝ => Real.log ((2*β)/s)) volume (0:ℝ) β :=
      BWSixth.intervalIntegrable_log_div (by positivity)
    have hB : IntervalIntegrable (fun s : ℝ => s^2/(4*β^2)) volume (0:ℝ) β := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_sub (hA.add hB) intervalIntegrable_const,
        intervalIntegral.integral_add hA hB]
    have eA : (∫ s in (0:ℝ)..β, Real.log ((2*β)/s)) = β*(Real.log 2 + 1) := by
      rw [BWSixth.integral_log_div (c := 2*β) (by positivity) hβ0]
      rw [show (2*β)/β = 2 by field_simp]
    have eB : (∫ s in (0:ℝ)..β, s^2/(4*β^2)) = β/12 := by
      have h3 : (∫ s in (0:ℝ)..β, s^2) = β^3/3 := by
        have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) β, HasDerivAt (fun s : ℝ => s^3/3) (x^2) x := by
          intro x _
          have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
          refine h.congr_deriv ?_
          ring
        have hint : IntervalIntegrable (fun s : ℝ => s^2) volume (0:ℝ) β := by
          apply Continuous.intervalIntegrable; fun_prop
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
        norm_num
      rw [show (fun s : ℝ => s^2/(4*β^2)) = fun s : ℝ => (1/(4*β^2)) * s^2 by funext s; ring]
      rw [intervalIntegral.integral_const_mul, h3]
      field_simp
      ring
    have eC : (∫ s in (0:ℝ)..β, (6*β:ℝ)) = 6*β^2 := by
      rw [intervalIntegral.integral_const]; simp; ring
    rw [eA, eB, eC]
  have e2 : (∫ s in β..(1/6), (hbf β s - 6*β)) = β*Real.log (1/(6*β)) - β + 6*β^2 := by
    have hcongr : (∫ s in β..(1/6), (hbf β s - 6*β)) = ∫ s in β..(1/6), (β/s - 6*β) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      rw [Set.uIoc_of_le hle16] at hs
      rw [hbf, if_neg (not_le.mpr hs.1)]
    rw [hcongr]
    have hA : IntervalIntegrable (fun s : ℝ => β/s) volume β (1/6) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hle16] at hx
      exact ne_of_gt (lt_of_lt_of_le hβ0 hx.1)
    rw [intervalIntegral.integral_sub hA intervalIntegrable_const]
    have eA : (∫ s in β..(1/6), β/s) = β*(Real.log (1/6) - Real.log β) := by
      rw [show (fun s : ℝ => β/s) = fun s : ℝ => β * (1/s) by funext s; ring]
      rw [intervalIntegral.integral_const_mul]
      have hderiv : ∀ x ∈ Set.uIcc β (1/6), HasDerivAt Real.log (1/x) x := by
        intro x hx
        rw [Set.uIcc_of_le hle16] at hx
        simpa [one_div] using Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hβ0 hx.1))
      have hint : IntervalIntegrable (fun s : ℝ => 1/s) volume β (1/6) := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro x hx
        rw [Set.uIcc_of_le hle16] at hx
        exact ne_of_gt (lt_of_lt_of_le hβ0 hx.1)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have eC : (∫ s in β..(1/6), (6*β:ℝ)) = 6*β*(1/6-β) := by
      rw [intervalIntegral.integral_const]; simp; ring
    rw [eA, eC]
    have hlog : Real.log (1/6) - Real.log β = Real.log (1/(6*β)) := by
      rw [← Real.log_div (by norm_num) (ne_of_gt hβ0)]; ring
    rw [hlog]; ring
  rw [e1, e2]
  have htot : β*(Real.log 2 + 1) + β/12 - 6*β^2 + (β*Real.log (1/(6*β)) - β + 6*β^2)
      = β*(Real.log (1/(3*β)) + 1/12) := by
    have hlog : Real.log (1/(3*β)) = Real.log 2 + Real.log (1/(6*β)) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
      ring
    rw [hlog]; ring
  rw [htot]
  have hlogmax : β*Real.log (1/(3*β)) ≤ 1/8 := by
    have hy : (0:ℝ) < 1/(3*β) := by positivity
    have hye : Real.log (1/(3*β)) ≤ (1/(3*β))/Real.exp 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1/(3*β))/Real.exp 1 by positivity)
      rw [Real.log_div (ne_of_gt hy) (Real.exp_ne_zero 1), Real.log_exp] at h
      linarith
    have h1 : β*Real.log (1/(3*β)) ≤ β*((1/(3*β))/Real.exp 1) :=
      mul_le_mul_of_nonneg_left hye hβ0.le
    have h2 : β*((1/(3*β))/Real.exp 1) = 1/(3*Real.exp 1) := by field_simp
    have h3 : 1/(3*Real.exp 1) ≤ 1/8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := Real.exp_one_gt_d9
      linarith
    linarith [h1, h2, h3]
  nlinarith [hlogmax, hβ16]



/-! ## Assembly -/

lemma Wg_sixth_int_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ6 : 1/6 ≤ β) :
    (1/6)*Wg β (1/6) - 1/3 ≤ ∫ s in (0:ℝ)..(1/6), Wg β s := by
  have hW : Wg β (1/6) = TT β (1/6) - hBf β (1/6) - hbf β (1/6) := rfl
  have hlin : (∫ s in (0:ℝ)..(1/6), Wg β s)
      = (∫ s in (0:ℝ)..(1/6), TT β s) - (∫ s in (0:ℝ)..(1/6), hBf β s)
        - (∫ s in (0:ℝ)..(1/6), hbf β s) := by
    have h1 : IntervalIntegrable (TT β) volume (0:ℝ) (1/6) := BWSixth.intervalIntegrable_TT hβ0 hβ1
    have h2 : IntervalIntegrable (hBf β) volume (0:ℝ) (1/6) := intervalIntegrable_hBf_sixth hβ0 hβ1
    have h3 : IntervalIntegrable (hbf β) volume (0:ℝ) (1/6) := intervalIntegrable_hbf_sixth hβ0 hβ1
    rw [show Wg β = fun s : ℝ => TT β s - hBf β s - hbf β s from rfl,
        intervalIntegral.integral_sub (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2]
  rw [hlin, hW]
  have h1 := integral_TT_sixth_ge hβ0 hβ1
  have h2 := integral_hBf_sixth_sub_le hβ0 hβ1
  have h3 := integral_hbf_sixth_sub_le hβ0 hβ1 hβ6
  have h2' : (∫ s in (0:ℝ)..(1/6), hBf β s) ≤ (1/6)*hBf β (1/6) + 1/6 := by
    have hsub : (∫ s in (0:ℝ)..(1/6), (hBf β s - hBf β (1/6)))
        = (∫ s in (0:ℝ)..(1/6), hBf β s) - (1/6)*hBf β (1/6) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_hBf_sixth hβ0 hβ1) intervalIntegrable_const,
          intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
    linarith [hsub, h2]
  have h3' : (∫ s in (0:ℝ)..(1/6), hbf β s) ≤ (1/6)*hbf β (1/6) + 1/6 := by
    have hsub : (∫ s in (0:ℝ)..(1/6), (hbf β s - hbf β (1/6)))
        = (∫ s in (0:ℝ)..(1/6), hbf β s) - (1/6)*hbf β (1/6) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_hbf_sixth hβ0 hβ1) intervalIntegrable_const,
          intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
    linarith [hsub, h3]
  linarith [h1, h2', h3']

lemma Wg_sixth_int_lower_small {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ16 : β < 1/6) :
    (1/6)*Wg β (1/6) - (1/6 + 1/8 + 1/72) ≤ ∫ s in (0:ℝ)..(1/6), Wg β s := by
  have hW : Wg β (1/6) = TT β (1/6) - hBf β (1/6) - hbf β (1/6) := rfl
  have hlin : (∫ s in (0:ℝ)..(1/6), Wg β s)
      = (∫ s in (0:ℝ)..(1/6), TT β s) - (∫ s in (0:ℝ)..(1/6), hBf β s)
        - (∫ s in (0:ℝ)..(1/6), hbf β s) := by
    have h1 : IntervalIntegrable (TT β) volume (0:ℝ) (1/6) := BWSixth.intervalIntegrable_TT hβ0 hβ1
    have h2 : IntervalIntegrable (hBf β) volume (0:ℝ) (1/6) := intervalIntegrable_hBf_sixth hβ0 hβ1
    have h3 : IntervalIntegrable (hbf β) volume (0:ℝ) (1/6) := intervalIntegrable_hbf_sixth hβ0 hβ1
    rw [show Wg β = fun s : ℝ => TT β s - hBf β s - hbf β s from rfl,
        intervalIntegral.integral_sub (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2]
  rw [hlin, hW]
  have h1 := integral_TT_sixth_ge hβ0 hβ1
  have h2 := integral_hBf_sixth_sub_le hβ0 hβ1
  have h3 := integral_hbf_sixth_sub_le_small hβ0 hβ16
  have h2' : (∫ s in (0:ℝ)..(1/6), hBf β s) ≤ (1/6)*hBf β (1/6) + 1/6 := by
    have hsub : (∫ s in (0:ℝ)..(1/6), (hBf β s - hBf β (1/6)))
        = (∫ s in (0:ℝ)..(1/6), hBf β s) - (1/6)*hBf β (1/6) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_hBf_sixth hβ0 hβ1) intervalIntegrable_const,
          intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
    linarith [hsub, h2]
  have h3' : (∫ s in (0:ℝ)..(1/6), hbf β s) ≤ (1/6)*hbf β (1/6) + (1/8 + 1/72) := by
    have hsub : (∫ s in (0:ℝ)..(1/6), (hbf β s - hbf β (1/6)))
        = (∫ s in (0:ℝ)..(1/6), hbf β s) - (1/6)*hbf β (1/6) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_hbf_sixth hβ0 hβ1) intervalIntegrable_const,
          intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
    linarith [hsub, h3]
  linarith [h1, h2', h3']

lemma Wg_tail_le {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6)
    (hβ6 : 1/6 ≤ β) :
    (∫ s in t..(1/6), Wg β s) ≤ (1/6-t)*Wg β (1/6) := by
  have hpt : ∀ s ∈ Set.Ioo t (1/6), Wg β s ≤ Wg β (1/6) := by
    intro s hs
    exact Wg_le_sixth hβ0 hβ1 hβ6 (lt_trans ht0 hs.1) hs.2.le
  have hi1 : IntervalIntegrable (Wg β) volume t (1/6) := by
    refine (intervalIntegrable_Wg_sixth hβ0 hβ1).mono_set ?_
    intro x hx
    rw [Set.uIcc_of_le ht] at hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/6)]
    exact ⟨le_trans ht0.le hx.1, hx.2⟩
  have hmono : (∫ s in t..(1/6), Wg β s) ≤ ∫ s in t..(1/6), (Wg β (1/6) : ℝ) :=
    intervalIntegral.integral_mono_on_of_le_Ioo ht hi1 intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  linarith [hmono]

lemma Wg_tail_le_small {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6)
    (hβ16 : β < 1/6) :
    (∫ s in t..(1/6), Wg β s) ≤ (1/6-t)*(Wg β (1/6) + 7/50) := by
  have hpt : ∀ s ∈ Set.Ioo t (1/6), Wg β s ≤ Wg β (1/6) + 7/50 := by
    intro s hs
    exact Wg_le_sixth_small hβ0 hβ1 (le_of_lt hβ16) (lt_trans ht0 hs.1) hs.2.le
  have hi1 : IntervalIntegrable (Wg β) volume t (1/6) := by
    refine (intervalIntegrable_Wg_sixth hβ0 hβ1).mono_set ?_
    intro x hx
    rw [Set.uIcc_of_le ht] at hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/6)]
    exact ⟨le_trans ht0.le hx.1, hx.2⟩
  have hmono : (∫ s in t..(1/6), Wg β s) ≤ ∫ s in t..(1/6), (Wg β (1/6) + 7/50) :=
    intervalIntegral.integral_mono_on_of_le_Ioo ht hi1 intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  linarith [hmono]

lemma intervalIntegrable_Wg_t {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6) :
    IntervalIntegrable (Wg β) volume (0:ℝ) t := by
  refine (intervalIntegrable_Wg_sixth hβ0 hβ1).mono_set ?_
  intro x hx
  rw [Set.uIcc_of_le ht0.le] at hx
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/6)]
  exact ⟨hx.1, le_trans hx.2 ht⟩

lemma intervalIntegrable_Wg_tail {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t)
    (ht : t ≤ 1/6) :
    IntervalIntegrable (Wg β) volume t (1/6) := by
  refine (intervalIntegrable_Wg_sixth hβ0 hβ1).mono_set ?_
  intro x hx
  rw [Set.uIcc_of_le ht] at hx
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/6)]
  exact ⟨le_trans ht0.le hx.1, hx.2⟩

lemma Wg_integral_lower {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6) :
    -(1:ℝ)/3 ≤ ∫ s in (0:ℝ)..t, Wg β s := by
  have hW0 : (0:ℝ) ≤ Wg β (1/6) := Wg_sixth_nonneg hβ0 hβ1
  have hsplit : (∫ s in (0:ℝ)..t, Wg β s)
      = (∫ s in (0:ℝ)..(1/6), Wg β s) - (∫ s in t..(1/6), Wg β s) := by
    have := intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_Wg_t hβ0 hβ1 ht0 ht)
      (intervalIntegrable_Wg_tail hβ0 hβ1 ht0 ht)
    linarith
  rw [hsplit]
  rcases lt_or_ge β (1/6) with hβ16 | hβ6
  · have hE := Wg_sixth_int_lower_small hβ0 hβ1 hβ16
    have htail := Wg_tail_le_small hβ0 hβ1 ht0 ht hβ16
    nlinarith [hE, htail, hW0, ht0, ht]
  · have hE := Wg_sixth_int_lower hβ0 hβ1 hβ6
    have htail := Wg_tail_le hβ0 hβ1 ht0 ht hβ6
    nlinarith [hE, htail, hW0, ht0, ht]

end BWSixthLower

open BWSixthLower BWSixth

/-- For `0 < β < 1` and `0 < t ≤ 1/6`, the integral over `[0,t]` of the box-window
integrand is at least `-1/3`. -/
theorem boxWindow_sixth_lower {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6) :
    -(1:ℝ)/3 ≤
    (∫ s in (0:ℝ)..t,
        ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        - ( (if (|s|:ℝ) ≤ 2-β then
              Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
           + (if (|s|:ℝ) ≤ β then
              Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) )) := by
  have hfun : (fun s : ℝ =>
        ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        - ( (if (|s|:ℝ) ≤ 2-β then
              Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
           + (if (|s|:ℝ) ≤ β then
              Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) )) = BoxWinSB.G β := by
    funext s
    have hs2 : |s|^2 = s^2 := sq_abs s
    simp only [BoxWinSB.G, BoxWinSB.TT, BoxWinSB.MBbig, BoxWinSB.Mb, BoxWinSB.MB, hs2]
    ring
  rw [hfun]
  have hGF : (∫ s in (0:ℝ)..t, BoxWinSB.G β s) = ∫ s in (0:ℝ)..t, BWSixth.F β s := by
    apply intervalIntegral.integral_congr_ae'
    · apply Filter.Eventually.of_forall
      intro x hx
      exact BWSixth.G_eq_F hβ1 hx.1 hx.2 ht
    · apply Filter.Eventually.of_forall
      intro x hx
      exfalso
      linarith [hx.1, hx.2, ht0]
  rw [hGF]
  have hIntF : IntervalIntegrable (BWSixth.F β) volume (0:ℝ) t := BWSixth.intervalIntegrable_F hβ0 hβ1 ht0 ht
  have hIntW : IntervalIntegrable (Wg β) volume (0:ℝ) t := intervalIntegrable_Wg_t hβ0 hβ1 ht0 ht
  have hmono : (∫ s in (0:ℝ)..t, Wg β s) ≤ ∫ s in (0:ℝ)..t, BWSixth.F β s :=
    intervalIntegral.integral_mono_on_of_le_Ioo ht0.le hIntW hIntF
      (fun s hs => Wg_le_F hβ0 hβ1 hs.1 (le_trans hs.2.le ht))
  have hlow := Wg_integral_lower hβ0 hβ1 ht0 ht
  linarith

end

end Commons.Analysis.Integral

