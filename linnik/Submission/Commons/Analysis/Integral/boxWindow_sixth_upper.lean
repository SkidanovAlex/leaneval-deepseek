import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Analysis.Integral.boxWin_small_beta

namespace Commons.Analysis.Integral
namespace BWSixth

open MeasureTheory intervalIntegral Filter
open scoped Topology
open scoped Interval

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open BoxWinSB

/-! ### The constant upper bound for the positive part -/

def Hc (β : ℝ) : ℝ := (13/5)*(1/(3/2-β) + 1/(1+β))

def Qc (β : ℝ) : ℝ :=
  ((2-β)^2-β^2)/(2*((2-β)^2)) + ((2-β)^2-β^2)^2/(8*((2-β)^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2)^3)

def Pc (β : ℝ) : ℝ := Hc β + Qc β

def UA (β s : ℝ) : ℝ :=
  Pc β - (143/144)*Real.log (2*(2-β)/s) - (71/72)*Real.log (2*β/s)

def UB (β s : ℝ) : ℝ := Pc β - (143/144)*Real.log (2*(2-β)/s)

lemma log_two_ge : (0.693:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]

lemma log_six_ge : (1.79:ℝ) ≤ Real.log 6 := by
  have h : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h]; linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

lemma log_twelve_ge : (2.48:ℝ) ≤ Real.log 12 := by
  have h : Real.log 12 = 2*Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ) = 2^2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [h]; linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

lemma log_twentytwo_ge : (2.89:ℝ) ≤ Real.log 22 := by
  have h18 : Real.log 18 = Real.log 2 + 2*Real.log 3 := by
    rw [show (18:ℝ) = 2*3^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have hle : Real.log 18 ≤ Real.log 22 := Real.log_le_log (by norm_num) (by norm_num)
  rw [h18] at hle
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

/-! ### Bounds for `Hc`, `Qc`, `Pc` -/

lemma Qc_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : Qc β ≤ 11/16 := by
  have hC : (2-β)^2-β^2 = 4*(1-β) := by ring
  have hD : (0:ℝ) < (2-β)^2 := by nlinarith
  have hb : (0:ℝ) < 2-β := by linarith
  have h1 : 4*(1-β) ≤ (2-β)^2 := by nlinarith [sq_nonneg β]
  have h10 : (0:ℝ) ≤ 4*(1-β) := by linarith
  have e1 : ((2-β)^2-β^2)/(2*((2-β)^2)) = (4*(1-β))/(2*((2-β)^2)) := by rw [hC]
  have e2 : ((2-β)^2-β^2)^2/(8*((2-β)^2)^2) = (4*(1-β))^2/(8*((2-β)^2)^2) := by rw [hC]
  have e3 : ((2-β)^2-β^2)^3/(16*((2-β)^2)^3) = (4*(1-β))^3/(16*((2-β)^2)^3) := by rw [hC]
  have h2 : (4*(1-β))/(2*((2-β)^2)) ≤ 1/2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*((2-β)^2))]
    linarith
  have h3 : (4*(1-β))^2/(8*((2-β)^2)^2) ≤ 1/8 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*((2-β)^2)^2)]
    nlinarith [h1, h10, hD]
  have h4 : (4*(1-β))^3/(16*((2-β)^2)^3) ≤ 1/16 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 16*((2-β)^2)^3)]
    have hp : (4*(1-β))^3 ≤ ((2-β)^2)^3 := pow_le_pow_left₀ h10 h1 3
    linarith
  simp only [Qc, e1, e2, e3]
  linarith

lemma Hc_le_one_sixth {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1/6) : Hc β ≤ 91/20 := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have h1 : 1/(3/2-β) ≤ 3/4 := by
    rw [div_le_iff₀ hA]; linarith
  have h2 : 1/(1+β) ≤ 1 := by
    rw [div_le_one hB]; linarith
  simp only [Hc]
  linarith

lemma Hc_le_half {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/2) (hβ2 : 1/6 ≤ β) : Hc β ≤ 169/35 := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have h1 : 1/(3/2-β) ≤ 1 := by
    rw [div_le_one hA]; linarith
  have h2 : 1/(1+β) ≤ 6/7 := by
    rw [div_le_iff₀ hB]; linarith
  simp only [Hc]
  linarith

lemma Hc_le_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : Hc β ≤ 13/2 := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have key : 1/(3/2-β) + 1/(1+β) = (5/2)/((3/2-β)*(1+β)) := by
    rw [div_add_div _ _ (ne_of_gt hA) (ne_of_gt hB)]
    congr 1
    ring
  have h2 : (5/2)/((3/2-β)*(1+β)) ≤ 5/2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (3/2-β)*(1+β))]
    nlinarith [sq_nonneg β, hβ1]
  simp only [Hc]
  rw [key]
  linarith

lemma Pc_le_one_sixth {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1/6) : Pc β ≤ 419/80 := by
  have hβ1 : β < 1 := by linarith
  have h1 := Hc_le_one_sixth hβ0 hβ
  have h2 := Qc_le hβ0 hβ1
  simp only [Pc]
  linarith

lemma Pc_le_half {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/2) (hβ2 : 1/6 ≤ β) :
    Pc β ≤ 169/35 + 11/16 := by
  have hβ1' : β < 1 := by linarith
  have h1 := Hc_le_half hβ0 hβ1 hβ2
  have h2 := Qc_le hβ0 hβ1'
  simp only [Pc]
  linarith

lemma Pc_le_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : Pc β ≤ 13/2 + 11/16 := by
  have h1 := Hc_le_one hβ0 hβ1
  have h2 := Qc_le hβ0 hβ1
  simp only [Pc]
  linarith

/-! ### The integrand as the difference of three pieces -/

/-- The integrand on the positive half-line (all `|s|` replaced by `s`, first branch taken). -/
def F (β s : ℝ) : ℝ := TT β s - MB β s - Mb β s

lemma G_eq_F {β t : ℝ} (hβ1 : β < 1) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ t) (ht : t ≤ 1/6) :
    G β s = F β s := by
  have hsle : s ≤ 2-β := by linarith
  have hsabs : |s| = s := abs_of_pos hs0
  simp only [G, F, MBbig, hsabs]
  rw [if_pos hsle]

/-! ### Pointwise estimates -/

lemma div_le_inv_self {A s : ℝ} (hA : 0 < A) : A/(A^2+s^2) ≤ 1/A := by
  rw [div_le_iff₀ (by positivity : (0:ℝ) < A^2+s^2)]
  have h : (1/A)*(A^2+s^2) = A + s^2/A := by
    field_simp
  rw [h]
  have : (0:ℝ) ≤ s^2/A := by positivity
  linarith

lemma TT_le_Pc {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : TT β s ≤ Pc β := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hD : (0:ℝ) < (2-β)^2 := by nlinarith
  have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  have h1 : (3/2-β)/((3/2-β)^2+s^2) ≤ 1/(3/2-β) := div_le_inv_self hA
  have h2 : (1+β)/((1+β)^2+s^2) ≤ 1/(1+β) := div_le_inv_self hB
  have h3 : ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) ≤ ((2-β)^2-β^2)/(2*((2-β)^2)) :=
    div_le_div_of_nonneg_left hC (by positivity) (by nlinarith)
  have hDP : (2-β)^2 ≤ (2-β)^2+s^2 := by nlinarith [sq_nonneg s]
  have h4 : ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2)^2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2-β)^2) hDP 2])
  have h5 : ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2)^3) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2-β)^2) hDP 3])
  simp only [TT, Pc, Hc, Qc]
  linarith

lemma MB_nonneg' {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6) :
    0 ≤ MB β s := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hmu1 : 1 ≤ (4*(2-β)^2+s^2)/(2*(2-β)*s) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2*(2-β) - s)]
  have h1 : 0 ≤ Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) := Real.log_nonneg hmu1
  have h2 : (0:ℝ) ≤ 1 - s^2/(4*(2-β)^2) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith [hs, hb, sq_nonneg s]
  simp only [MB]
  exact mul_nonneg h1 h2

lemma MB_le_log {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6) :
    MB β s ≤ Real.log (2*(2-β)/s) + 1 := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hsplit : (4*(2-β)^2+s^2)/(2*(2-β)*s) = (2*(2-β)/s)*(1+s^2/(4*(2-β)^2)) := by
    field_simp
    ring
  have hlogeq : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))
      = Real.log (2*(2-β)/s) + Real.log (1+s^2/(4*(2-β)^2)) := by
    rw [hsplit, Real.log_mul (by positivity) (by positivity)]
  have hcorr : Real.log (1+s^2/(4*(2-β)^2)) ≤ s^2/(4*(2-β)^2) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + s^2/(4*(2-β)^2) by positivity)
    linarith
  have hcoef : (0:ℝ) ≤ 1 - s^2/(4*(2-β)^2) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith [hs, hb, sq_nonneg s]
  have hcoef1 : 1 - s^2/(4*(2-β)^2) ≤ 1 := by
    have : (0:ℝ) ≤ s^2/(4*(2-β)^2) := by positivity
    linarith
  have hs2 : s^2/(4*(2-β)^2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hs, hb, sq_nonneg s]
  have hlog0 : 0 ≤ Real.log (2*(2-β)/s) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    nlinarith
  have haux : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) ≤ Real.log (2*(2-β)/s) + 1 := by
    rw [hlogeq]; linarith
  simp only [MB]
  nlinarith [haux, hcoef, hcoef1, hlog0, hcorr]

lemma MB_ge {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6) :
    (143/144)*Real.log (2*(2-β)/s) ≤ MB β s := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hs2 : s^2 ≤ 1/36 := by nlinarith
  have hcoef : (143/144:ℝ) ≤ 1 - s^2/(4*(2-β)^2) := by
    have h : s^2/(4*(2-β)^2) ≤ 1/144 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*(2-β)^2)]
      nlinarith [sq_nonneg (2-β), hb, hs2]
    linarith
  have hc0 : (0:ℝ) ≤ 1 - s^2/(4*(2-β)^2) := by linarith
  have hlog : Real.log (2*(2-β)/s) ≤ Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) := by
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*(2-β)*s)]
    have he : (2*(2-β)/s)*(2*(2-β)*s) = 4*(2-β)^2 := by
      field_simp
      ring
    rw [he]; nlinarith [sq_nonneg s]
  have hlog0 : 0 ≤ Real.log (2*(2-β)/s) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    nlinarith
  have h1 : (143/144)*Real.log (2*(2-β)/s)
      ≤ (1 - s^2/(4*(2-β)^2))*Real.log (2*(2-β)/s) :=
    mul_le_mul_of_nonneg_right hcoef hlog0
  have h2 : (1 - s^2/(4*(2-β)^2))*Real.log (2*(2-β)/s)
      ≤ (1 - s^2/(4*(2-β)^2))*Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) :=
    mul_le_mul_of_nonneg_left hlog hc0
  simp only [MB]
  linarith

lemma Mb_nonneg' {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6) :
    0 ≤ Mb β s := by
  have hb : (0:ℝ) < 2-β := by linarith
  by_cases hc : s ≤ β
  · rw [Mb, if_pos hc]
    have h1 : 0 ≤ Real.log ((4*β^2+s^2)/(2*β*s)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2*β - s)]
    have h2 : (0:ℝ) ≤ 1 - s^2/(2*((2-β)^2+β^2)) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith [sq_nonneg (2-β), sq_nonneg β, sq_nonneg s, hc]
    exact mul_nonneg h1 h2
  · rw [Mb, if_neg hc]
    positivity

lemma Mb_ge_log {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6)
    (hsβ : s ≤ β) :
    (71/72)*Real.log (2*β/s) ≤ Mb β s := by
  have hb : (0:ℝ) < 2-β := by linarith
  rw [Mb, if_pos hsβ]
  have hcoef : (71/72:ℝ) ≤ 1 - s^2/(2*((2-β)^2+β^2)) := by
    have h : s^2/(2*((2-β)^2+β^2)) ≤ 1/72 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*((2-β)^2+β^2))]
      nlinarith [sq_nonneg (2-β), sq_nonneg β, sq_nonneg s, hs]
    linarith
  have hc0 : (0:ℝ) ≤ 1 - s^2/(2*((2-β)^2+β^2)) := by linarith
  have hlog : Real.log (2*β/s) ≤ Real.log ((4*β^2+s^2)/(2*β*s)) := by
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*β*s)]
    have he : (2*β/s)*(2*β*s) = 4*β^2 := by
      field_simp
      ring
    rw [he]; nlinarith [sq_nonneg s]
  have hlog0 : 0 ≤ Real.log (2*β/s) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    linarith
  have h1 : (71/72)*Real.log (2*β/s) ≤ (1 - s^2/(2*((2-β)^2+β^2)))*Real.log (2*β/s) :=
    mul_le_mul_of_nonneg_right hcoef hlog0
  have h2 : (1 - s^2/(2*((2-β)^2+β^2)))*Real.log (2*β/s)
      ≤ (1 - s^2/(2*((2-β)^2+β^2)))*Real.log ((4*β^2+s^2)/(2*β*s)) :=
    mul_le_mul_of_nonneg_left hlog hc0
  linarith

lemma abs_Mb_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) (hs : s ≤ 1/6) :
    |Mb β s| ≤ |Real.log (2*β/s)| + 1 := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hnn := Mb_nonneg' hβ0 hβ1 hs0 hs
  rw [abs_of_nonneg hnn]
  by_cases hc : s ≤ β
  · rw [Mb, if_pos hc]
    have hsplit : (4*β^2+s^2)/(2*β*s) = (2*β/s)*(1+s^2/(4*β^2)) := by
      field_simp; ring
    have hlogeq : Real.log ((4*β^2+s^2)/(2*β*s))
        = Real.log (2*β/s) + Real.log (1+s^2/(4*β^2)) := by
      rw [hsplit, Real.log_mul (by positivity) (by positivity)]
    have hcorr : Real.log (1+s^2/(4*β^2)) ≤ s^2/(4*β^2) := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + s^2/(4*β^2) by positivity)
      linarith
    have hsβ2 : s^2/(4*β^2) ≤ 1/4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*β^2)]
      nlinarith
    have hsmall : Real.log ((4*β^2+s^2)/(2*β*s)) ≤ Real.log (2*β/s) + 1/4 := by
      rw [hlogeq]; linarith
    have hlog0 : 0 ≤ Real.log (2*β/s) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hs0]; linarith
    have hcoef1 : 1 - s^2/(2*((2-β)^2+β^2)) ≤ 1 := by
      have : (0:ℝ) ≤ s^2/(2*((2-β)^2+β^2)) := by positivity
      linarith
    have hcoef0 : 0 ≤ 1 - s^2/(2*((2-β)^2+β^2)) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith [sq_nonneg (2-β), sq_nonneg β, sq_nonneg s, hc]
    have habs : |Real.log (2*β/s)| = Real.log (2*β/s) := abs_of_nonneg hlog0
    rw [habs]
    nlinarith [hsmall, hcoef0, hcoef1, hlog0]
  · rw [Mb, if_neg hc]
    have hsqrt : Real.sqrt ((2-β)^2+s^2) ≥ (2-β) := by
      rw [ge_iff_le, Real.le_sqrt (le_of_lt hb) (by positivity)]
      nlinarith
    have hle1 : (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2)) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < s*Real.sqrt ((2-β)^2+s^2))]
      have h1 : (2-β)*s ≤ s*Real.sqrt ((2-β)^2+s^2) := by
        have := mul_le_mul_of_nonneg_left hsqrt hs0.le
        nlinarith
      nlinarith [h1, hb, hs0]
    have habs : |Real.log (2*β/s)| ≥ 0 := abs_nonneg _
    linarith

/-! ### The integral of `log (c/s)` -/

lemma intervalIntegrable_log_div {c : ℝ} (hc : 0 < c) {a b : ℝ} :
    IntervalIntegrable (fun s : ℝ => Real.log (c/s)) volume a b := by
  have h0 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  have h : (fun s : ℝ => Real.log (c/s)) =ᵐ[volume]
      (fun s : ℝ => Real.log c - Real.log s) := by
    filter_upwards [h0] with s hs
    rw [Real.log_div (ne_of_gt hc) hs]
  have hbase : IntervalIntegrable (fun s : ℝ => Real.log c - Real.log s) volume a b :=
    intervalIntegrable_const.sub (intervalIntegrable_log')
  exact hbase.congr_ae ((ae_mono Measure.restrict_le_self) h.symm)

lemma integral_log_div {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, Real.log (c/s)) = t*(Real.log (c/t) + 1) := by
  have h0 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  have h1 : (∫ s in (0:ℝ)..t, Real.log (c/s))
      = ∫ s in (0:ℝ)..t, (Real.log c - Real.log s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [h0] with s hs hmem
    rw [Real.log_div (ne_of_gt hc) hs]
  rw [h1, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_log',
    intervalIntegral.integral_const, _root_.integral_log_from_zero]
  rw [Real.log_div (ne_of_gt hc) (ne_of_gt ht)]
  ring

/-! ### Integrability of the pieces -/

lemma measurable_TT (β : ℝ) : Measurable (TT β) := by
  unfold TT
  fun_prop

lemma measurable_MB (β : ℝ) : Measurable (MB β) := by
  unfold MB
  fun_prop

lemma measurable_Mb (β : ℝ) : Measurable (Mb β) := by
  unfold Mb
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · fun_prop
  · fun_prop

lemma TT_nonneg {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ TT β s := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hD : (0:ℝ) < (2-β)^2 := by nlinarith
  have hC : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
  have h1 : (0:ℝ) ≤ (3/2-β)/((3/2-β)^2+s^2) := div_nonneg hA.le (by positivity)
  have h2 : (0:ℝ) ≤ (1+β)/((1+β)^2+s^2) := div_nonneg hB.le (by positivity)
  have h3 : (0:ℝ) ≤ ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) := div_nonneg hC (by positivity)
  have h4 : (0:ℝ) ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) := div_nonneg (by positivity) (by positivity)
  have h5 : (0:ℝ) ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) := div_nonneg (by positivity) (by positivity)
  simp only [TT]
  linarith

lemma intervalIntegrable_TT {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a b : ℝ} :
    IntervalIntegrable (TT β) volume a b := by
  refine IntervalIntegrable.mono_fun' (f := TT β) (g := fun _ : ℝ => Pc β)
    intervalIntegrable_const ?_ ?_
  · exact (measurable_TT β).aestronglyMeasurable
  · rw [Filter.EventuallyLE]
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (TT_nonneg hβ0 hβ1)]
      exact TT_le_Pc hβ0 hβ1

lemma intervalIntegrable_abs_log_div {c t : ℝ} (hc : 0 < c) (ht0 : 0 ≤ t) (ht : t ≤ 1/6) :
    IntervalIntegrable (fun s : ℝ => |Real.log (c/s)|) volume 0 t := by
  refine IntervalIntegrable.mono_fun' (f := fun s : ℝ => |Real.log (c/s)|)
    (g := fun s : ℝ => |Real.log c| + (-Real.log s) + 1) ?_ ?_ ?_
  · have h : IntervalIntegrable (fun s : ℝ => |Real.log c| + (-Real.log s) + 1) volume 0 t :=
      (intervalIntegrable_const.add intervalIntegrable_log'.neg).add intervalIntegrable_const
    exact h
  · have hm : Measurable (fun s : ℝ => |Real.log (c/s)|) := by
      apply Measurable.abs
      exact Real.measurable_log.comp (measurable_const.div measurable_id)
    exact hm.aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le ht0] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hx1' : x ≤ 1/6 := le_trans hx1 ht
    rw [Real.norm_eq_abs, abs_abs]
    have h2 : Real.log (c/x) = Real.log c - Real.log x :=
      Real.log_div (ne_of_gt hc) (ne_of_gt hx0)
    rw [h2]
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx0.le (by linarith)
    have htri : |Real.log c - Real.log x| ≤ |Real.log c| + (-Real.log x) := by
      have h1 : |Real.log c + (-Real.log x)| ≤ |Real.log c| + |-Real.log x| := abs_add_le _ _
      have h2 : |(-Real.log x)| = -Real.log x := abs_of_nonneg (by linarith)
      rw [h2] at h1
      simpa [sub_eq_add_neg] using h1
    linarith

lemma intervalIntegrable_MB {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t)
    (ht : t ≤ 1/6) : IntervalIntegrable (MB β) volume 0 t := by
  have hc : (0:ℝ) < 2*(2-β) := by linarith
  refine IntervalIntegrable.mono_fun' (f := MB β)
    (g := fun s : ℝ => Real.log (2*(2-β)/s) + 1) ?_ ?_ ?_
  · exact (intervalIntegrable_log_div hc).add intervalIntegrable_const
  · exact (measurable_MB β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le ht0.le] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hx1' : x ≤ 1/6 := le_trans hx1 ht
    rw [Real.norm_eq_abs, abs_of_nonneg (MB_nonneg' hβ0 hβ1 hx0 hx1')]
    exact MB_le_log hβ0 hβ1 hx0 hx1'

lemma intervalIntegrable_Mb {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t)
    (ht : t ≤ 1/6) : IntervalIntegrable (Mb β) volume 0 t := by
  have hc : (0:ℝ) < 2*β := by linarith
  refine IntervalIntegrable.mono_fun' (f := Mb β)
    (g := fun s : ℝ => |Real.log (2*β/s)| + 1) ?_ ?_ ?_
  · exact (intervalIntegrable_abs_log_div hc ht0.le ht).add intervalIntegrable_const
  · exact (measurable_Mb β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le ht0.le] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hx1' : x ≤ 1/6 := le_trans hx1 ht
    exact abs_Mb_le hβ0 hβ1 hx0 hx1'

lemma intervalIntegrable_F {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t)
    (ht : t ≤ 1/6) : IntervalIntegrable (F β) volume 0 t := by
  have h1 := intervalIntegrable_TT (β := β) (a := (0:ℝ)) (b := t) hβ0 hβ1
  have h2 := intervalIntegrable_MB hβ0 hβ1 ht0 ht
  have h3 := intervalIntegrable_Mb hβ0 hβ1 ht0 ht
  have h := (h1.sub h2).sub h3
  exact h

lemma intervalIntegrable_UA {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    IntervalIntegrable (UA β) volume 0 t := by
  have hc1 : (0:ℝ) < 2*(2-β) := by linarith
  have hc2 : (0:ℝ) < 2*β := by linarith
  have h : IntervalIntegrable (UA β) volume 0 t :=
    (intervalIntegrable_const.sub
      ((intervalIntegrable_log_div hc1).const_mul (143/144))).sub
      ((intervalIntegrable_log_div hc2).const_mul (71/72))
  exact h

lemma intervalIntegrable_UB {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    IntervalIntegrable (UB β) volume 0 t := by
  have hc1 : (0:ℝ) < 2*(2-β) := by linarith
  have h : IntervalIntegrable (UB β) volume 0 t :=
    intervalIntegrable_const.sub ((intervalIntegrable_log_div hc1).const_mul (143/144))
  exact h

/-! ### The value of the upper bounds' integrals -/

lemma integral_UA {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    (∫ s in (0:ℝ)..t, UA β s)
      = Pc β * t - (143/144)*t*(Real.log (2*(2-β)/t)+1)
          - (71/72)*t*(Real.log (2*β/t)+1) := by
  have hc1 : (0:ℝ) < 2*(2-β) := by linarith
  have hc2 : (0:ℝ) < 2*β := by linarith
  have hi1 : IntervalIntegrable (fun s : ℝ => Real.log (2*(2-β)/s)) volume 0 t :=
    intervalIntegrable_log_div hc1
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.log (2*β/s)) volume 0 t :=
    intervalIntegrable_log_div hc2
  simp only [UA]
  rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub (hi1.const_mul (143/144)))
      (hi2.const_mul (71/72))]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hi1.const_mul (143/144))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_log_div hc1 ht0, integral_log_div hc2 ht0, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

lemma integral_UB {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) :
    (∫ s in (0:ℝ)..t, UB β s)
      = Pc β * t - (143/144)*t*(Real.log (2*(2-β)/t)+1) := by
  have hc1 : (0:ℝ) < 2*(2-β) := by linarith
  have hi1 : IntervalIntegrable (fun s : ℝ => Real.log (2*(2-β)/s)) volume 0 t :=
    intervalIntegrable_log_div hc1
  simp only [UB]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hi1.const_mul (143/144))]
  rw [intervalIntegral.integral_const_mul, integral_log_div hc1 ht0,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring


/-! ### The arithmetic lemmas -/

/-- Core arithmetic step: a universal bound `≤ 3/2` for the coefficient gives the result. -/
lemma arith_step {β P t X1 X2 Pmax : ℝ} (ht0 : 0 < t) (ht : t ≤ 1/6)
    (hP : P ≤ Pmax) (hL1 : X1 ≤ Real.log (2*(2-β)/t)) (hL2 : X2 ≤ Real.log (2*β/t))
    (hcoef : Pmax - (143/144)*(X1+1) - (71/72)*(X2+1) ≤ 3/2) :
    P * t - (143/144)*t*(Real.log (2*(2-β)/t)+1)
      - (71/72)*t*(Real.log (2*β/t)+1) ≤ 1/4 := by
  have hA : (143/144)*t*(X1+1) ≤ (143/144)*t*(Real.log (2*(2-β)/t)+1) := by
    have h1 : X1 + 1 ≤ Real.log (2*(2-β)/t) + 1 := by linarith
    have h2 : t*(X1+1) ≤ t*(Real.log (2*(2-β)/t)+1) := mul_le_mul_of_nonneg_left h1 ht0.le
    have h3 : (143/144)*(t*(X1+1)) ≤ (143/144)*(t*(Real.log (2*(2-β)/t)+1)) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  have hB : (71/72)*t*(X2+1) ≤ (71/72)*t*(Real.log (2*β/t)+1) := by
    have h1 : X2 + 1 ≤ Real.log (2*β/t) + 1 := by linarith
    have h2 : t*(X2+1) ≤ t*(Real.log (2*β/t)+1) := mul_le_mul_of_nonneg_left h1 ht0.le
    have h3 : (71/72)*(t*(X2+1)) ≤ (71/72)*(t*(Real.log (2*β/t)+1)) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  have h1 : P*t ≤ Pmax*t := mul_le_mul_of_nonneg_right hP ht0.le
  have hfin : Pmax*t - (143/144)*t*(X1+1) - (71/72)*t*(X2+1) ≤ 1/4 := by
    nlinarith [hcoef, ht0, ht]
  linarith

lemma arith_A {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6)
    (hcase : t ≤ β) :
    Pc β * t - (143/144)*t*(Real.log (2*(2-β)/t)+1)
      - (71/72)*t*(Real.log (2*β/t)+1) ≤ 1/4 := by
  have hlog2 : (0.693:ℝ) ≤ Real.log (2*β/t) := by
    have hle : (2:ℝ) ≤ 2*β/t := by
      rw [le_div_iff₀ ht0]; linarith
    exact le_trans log_two_ge (Real.log_le_log (by norm_num) hle)
  rcases le_or_gt β (1/6) with hβ6 | hβ6
  · have hlog1 : (2.89:ℝ) ≤ Real.log (2*(2-β)/t) := by
      have hle : (22:ℝ) ≤ 2*(2-β)/t := by
        rw [le_div_iff₀ ht0]
        nlinarith
      exact le_trans log_twentytwo_ge (Real.log_le_log (by norm_num) hle)
    exact arith_step ht0 ht (Pc_le_one_sixth hβ0 hβ6) hlog1 hlog2 (by norm_num)
  · have hlog1 : (2.48:ℝ) ≤ Real.log (2*(2-β)/t) := by
      have hle : (12:ℝ) ≤ 2*(2-β)/t := by
        rw [le_div_iff₀ ht0]
        nlinarith
      exact le_trans log_twelve_ge (Real.log_le_log (by norm_num) hle)
    rcases le_or_gt β (1/2) with hβh | hβh
    · exact arith_step ht0 ht (Pc_le_half hβ0 hβh (le_of_lt hβ6)) hlog1 hlog2 (by norm_num)
    · have hlog2' : (1.79:ℝ) ≤ Real.log (2*β/t) := by
        have hle : (6:ℝ) ≤ 2*β/t := by
          rw [le_div_iff₀ ht0]
          nlinarith
        exact le_trans log_six_ge (Real.log_le_log (by norm_num) hle)
      exact arith_step ht0 ht (Pc_le_one hβ0 hβ1) hlog1 hlog2' (by norm_num)

lemma arith_B {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6)
    (hcase : β < t) :
    Pc β * t - (143/144)*t*(Real.log (2*(2-β)/t)+1) ≤ 1/4 := by
  have hlog1 : (2.89:ℝ) ≤ Real.log (2*(2-β)/t) := by
    have hle : (22:ℝ) ≤ 2*(2-β)/t := by
      rw [le_div_iff₀ ht0]
      nlinarith
    exact le_trans log_twentytwo_ge (Real.log_le_log (by norm_num) hle)
  have hβ6 : β ≤ 1/6 := le_of_lt (lt_of_lt_of_le hcase ht)
  have hP : Pc β ≤ 419/80 := Pc_le_one_sixth hβ0 hβ6
  have h1 : Pc β * t ≤ 419/80 * t := mul_le_mul_of_nonneg_right hP ht0.le
  have hA : (143/144)*t*(2.89+1) ≤ (143/144)*t*(Real.log (2*(2-β)/t)+1) := by
    have h2 : t*(2.89+1) ≤ t*(Real.log (2*(2-β)/t)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) ht0.le
    have h3 : (143/144)*(t*(2.89+1)) ≤ (143/144)*(t*(Real.log (2*(2-β)/t)+1)) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  have hcoef : (419/80:ℝ) - (143/144)*(2.89+1) ≤ 3/2 := by norm_num
  nlinarith [h1, hA, hcoef, ht0, ht]

/-! ### The main theorem -/

theorem boxWindow_sixth_upper_core {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t)
    (ht : t ≤ 1/6) :
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
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) )) ≤ 1/4 := by
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
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) )) = G β := by
    funext s
    have hs2 : |s|^2 = s^2 := sq_abs s
    simp only [G, TT, MBbig, Mb, MB, hs2]
    ring
  rw [hfun]
  have hGF : (∫ s in (0:ℝ)..t, G β s) = ∫ s in (0:ℝ)..t, F β s := by
    apply intervalIntegral.integral_congr_ae'
    · apply Filter.Eventually.of_forall
      intro x hx
      exact G_eq_F hβ1 hx.1 hx.2 ht
    · apply Filter.Eventually.of_forall
      intro x hx
      exfalso
      linarith [hx.1, hx.2, ht0]
  rw [hGF]
  by_cases hcase : t ≤ β
  · have hIntF := intervalIntegrable_F hβ0 hβ1 ht0 ht
    have hIntU := intervalIntegrable_UA (β := β) (t := t) hβ0 hβ1 ht0
    have hmono : (∫ s in (0:ℝ)..t, F β s) ≤ ∫ s in (0:ℝ)..t, UA β s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht0.le hIntF hIntU
      intro x hx
      have hx0 : 0 < x := hx.1
      have hxt : x ≤ t := hx.2.le
      have h1 := TT_le_Pc hβ0 hβ1 (s := x)
      have h2 := MB_ge hβ0 hβ1 hx0 (le_trans hxt ht)
      have h3 := Mb_ge_log hβ0 hβ1 hx0 (le_trans hxt ht) (le_trans hxt hcase)
      simp only [F, UA]
      linarith
    rw [integral_UA hβ0 hβ1 ht0] at hmono
    have har := arith_A hβ0 hβ1 ht0 ht hcase
    linarith
  · push_neg at hcase
    have hIntF := intervalIntegrable_F hβ0 hβ1 ht0 ht
    have hIntU := intervalIntegrable_UB (β := β) (t := t) hβ0 hβ1 ht0
    have hmono : (∫ s in (0:ℝ)..t, F β s) ≤ ∫ s in (0:ℝ)..t, UB β s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht0.le hIntF hIntU
      intro x hx
      have hx0 : 0 < x := hx.1
      have hxt : x ≤ t := hx.2.le
      have h1 := TT_le_Pc hβ0 hβ1 (s := x)
      have h2 := MB_ge hβ0 hβ1 hx0 (le_trans hxt ht)
      have h3 := Mb_nonneg' hβ0 hβ1 hx0 (le_trans hxt ht)
      simp only [F, UB]
      linarith
    rw [integral_UB hβ0 hβ1 ht0] at hmono
    have har := arith_B hβ0 hβ1 ht0 ht hcase
    linarith

end

end BWSixth

open BWSixth in
/-- For `0 < β < 1` and `0 < t ≤ 1/6`, the integral over `[0,t]` of the box-window
integrand is at most `1/4`. -/
theorem boxWindow_sixth_upper {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ht0 : 0 < t) (ht : t ≤ 1/6) :
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
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) )) ≤ 1/4 :=
  BWSixth.boxWindow_sixth_upper_core hβ0 hβ1 ht0 ht

end Commons.Analysis.Integral