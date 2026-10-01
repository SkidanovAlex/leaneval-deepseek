import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Analysis.SpecialFunctions.arctan_ge_taylor8
import Submission.Commons.Analysis.Integral.integral_inv_sq_add

open MeasureTheory intervalIntegral Filter
open scoped Topology

namespace Commons.Analysis.Integral

/-! Helper namespace for the proof of `boxWin_small_beta` (kept separate so that the helper
names cannot clash with those of sibling files). -/
namespace BoxWinSB

noncomputable section

/-! ## The integrand decomposed -/

/-- Positive (target-kernel) part of the integrand, as a function of `t = |s|`. -/
def TT (β t : ℝ) : ℝ :=
  (13/5)*((3/2-β)/((3/2-β)^2+t^2)+(1+β)/((1+β)^2+t^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2+t^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+t^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+t^2)^3)

/-- The `B`-majorant (log branch). -/
def MB (β t : ℝ) : ℝ :=
  Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t))*(1-t^2/(4*(2-β)^2))

/-- The `B`-majorant with its branch cut at `2-β`. -/
def MBbig (β t : ℝ) : ℝ :=
  if t ≤ 2-β then MB β t else (2-β)^2/(t*Real.sqrt ((2-β)^2+t^2))

/-- The `β`-majorant. -/
def Mb (β t : ℝ) : ℝ :=
  if t ≤ β then Real.log ((4*β^2+t^2)/(2*β*t))*(1-t^2/(2*((2-β)^2+β^2)))
    else (2-β)*β/(t*Real.sqrt ((2-β)^2+t^2))

/-- The integrand of the target statement. -/
def G (β s : ℝ) : ℝ := TT β |s| - MBbig β |s| - Mb β |s|

/-- Upper bound for the `B`-majorant. -/
def hBf (β s : ℝ) : ℝ := Real.log (2*(2-β)) - Real.log s + s^2/(4*(2-β)^2)

/-- Upper bound for the `β`-majorant. -/
def hbf (β s : ℝ) : ℝ :=
  if s ≤ β then Real.log (2*β) - Real.log s + s^2/(4*β^2) else β/s

/-- Pointwise lower bound for the integrand. -/
def LOW (β s : ℝ) : ℝ :=
  (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) + 13/20
    - hBf β s - hbf β s

@[simp] lemma G_neg (β s : ℝ) : G β (-s) = G β s := by
  simp [G]

/-- On `(0,1/4]` the integrand is the difference of the three pieces, with both `if`s
taking their *then*-branch for the first one. -/
lemma G_eq {β s : ℝ} (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    G β s = TT β s - MB β s - Mb β s := by
  have hsabs : |s| = s := abs_of_pos hs0
  have hle : s ≤ 2 - β := by linarith
  simp only [G, MBbig, hsabs]
  rw [if_pos hle]

/-! ## Pointwise lower bounds for the integrand -/

/-- The three Taylor-correction terms dominate `13/20` on the window. -/
lemma TT_lower {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) + 13/20 ≤ TT β s := by
  have hβ2 : β^2 ≤ 1/16 := by nlinarith
  have hs2 : s^2 ≤ 1/16 := by nlinarith
  have hY : (0:ℝ) < (2-β)^2+s^2 := by positivity
  have hDpos : (0:ℝ) < (2-β)^2-β^2 := by nlinarith
  -- `24 Y ≤ 25 D`
  have hkey : 24*((2-β)^2+s^2) ≤ 25*((2-β)^2-β^2) := by
    have hcert : 25*((2-β)^2-β^2) - 24*((2-β)^2+s^2)
        = 24*(1/16 - s^2) + 24*(1/16 - β^2) + 4*(1/4-β) := by ring
    nlinarith [hcert, hβ2, hs2, hβ1]
  have h24 : (0:ℝ) ≤ 24*((2-β)^2+s^2) := by positivity
  have h2 := pow_le_pow_left₀ h24 hkey 2
  have h3 := pow_le_pow_left₀ h24 hkey 3
  have hterm1 : (12/25:ℝ) ≤ ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*((2-β)^2+s^2))]
    nlinarith [hkey]
  have hterm2 : (72/625:ℝ) ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 8*((2-β)^2+s^2)^2)]
    nlinarith [h2]
  have hterm3 : (13824/250000:ℝ) ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 16*((2-β)^2+s^2)^3)]
    nlinarith [h3]
  have hsum : (13/20:ℝ) ≤ 12/25 + 72/625 + 13824/250000 := by norm_num
  have heq : TT β s = (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
      + (((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) := by
    simp only [TT]; ring
  rw [heq]
  linarith

/-- The `B`-majorant is dominated by `hBf`. -/
lemma MB_le {β t : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (ht0 : 0 < t) :
    MB β t ≤ hBf β t := by
  have hb : (0:ℝ) < 2 - β := by linarith
  have hbne : (2:ℝ) - β ≠ 0 := ne_of_gt hb
  have htne : t ≠ 0 := ne_of_gt ht0
  have hmu1 : 1 ≤ (4*(2-β)^2+t^2)/(2*(2-β)*t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2*(2-β) - t)]
  have hlogmu : 0 ≤ Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t)) := Real.log_nonneg hmu1
  have hcoef : 1 - t^2/(4*(2-β)^2) ≤ 1 := by
    have : (0:ℝ) ≤ t^2/(4*(2-β)^2) := by positivity
    linarith
  have hsplit : (4*(2-β)^2+t^2)/(2*(2-β)*t) = (2*(2-β)/t) * (1 + t^2/(4*(2-β)^2)) := by
    field_simp
    ring
  have hlogeq : Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t))
      = Real.log (2*(2-β)) - Real.log t + Real.log (1 + t^2/(4*(2-β)^2)) := by
    rw [hsplit, Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity : (2:ℝ)*(2-β) ≠ 0) htne]
  have hle : Real.log (1 + t^2/(4*(2-β)^2)) ≤ t^2/(4*(2-β)^2) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + t^2/(4*(2-β)^2) by positivity)
    linarith
  have hmain : Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t)) ≤ hBf β t := by
    rw [hBf, hlogeq]; linarith
  have := mul_le_of_le_one_right hlogmu hcoef
  simp only [MB, hBf]
  linarith [this, hmain]

/-- The `β`-majorant is dominated by `hbf`. -/
lemma Mb_le {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (ht0 : 0 < t) :
    Mb β t ≤ hbf β t := by
  have hb : (0:ℝ) < 2 - β := by linarith
  have hbne : (2:ℝ) - β ≠ 0 := ne_of_gt hb
  have htne : t ≠ 0 := ne_of_gt ht0
  have hβne : β ≠ 0 := ne_of_gt hβ0
  by_cases hc : t ≤ β
  · rw [Mb, hbf, if_pos hc, if_pos hc]
    have hD : (0:ℝ) < 2*((2-β)^2+β^2) := by positivity
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
    have hden : (0:ℝ) < Real.sqrt ((2-β)^2+t^2) := Real.sqrt_pos.mpr (by positivity)
    rw [le_div_iff₀ (by positivity : (0:ℝ) < t)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < t*Real.sqrt ((2-β)^2+t^2))]
    have hb1 : (0:ℝ) ≤ β*t := by positivity
    have h1 := mul_le_mul_of_nonneg_right hsqrt hb1
    nlinarith [h1]

/-- Pointwise lower bound for the integrand on the window. -/
lemma G_lower {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    LOW β s ≤ G β s := by
  have hβ2 : β < 2 := by linarith
  have h1 := TT_lower hβ0 hβ1 hs0 hs1
  have h2 := MB_le hβ0 hβ2 hs0
  have h3 := Mb_le hβ0 hβ1 hs0
  rw [G_eq hβ1 hs0 hs1]
  simp only [LOW, hbf, Mb] at h3 ⊢
  by_cases hc : s ≤ β
  · simp only [if_pos hc] at h3 ⊢
    linarith
  · simp only [if_neg hc] at h3 ⊢
    linarith

/-! ## Coarse bounds used for integrability -/

/-- The positive part is bounded by `6` on the window. -/
lemma TT_ub {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    TT β s ≤ 6 := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hb : (7:ℝ)/4 ≤ 2-β := by linarith
  have hD4 : (2-β)^2-β^2 ≤ 4 := by nlinarith
  have hY : (49:ℝ)/16 ≤ (2-β)^2+s^2 := by nlinarith [sq_nonneg ((2:ℝ)-β), sq_nonneg s]
  have hY0 : (0:ℝ) < (2-β)^2+s^2 := by linarith
  have ht1 : (3/2-β)/((3/2-β)^2+s^2) ≤ 4/5 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (3/2-β)^2+s^2)]
    nlinarith [sq_nonneg ((3:ℝ)/2-β), sq_nonneg s, hβ1, hβ0]
  have ht2 : (1+β)/((1+β)^2+s^2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+β)^2+s^2)]
    nlinarith [sq_nonneg ((1:ℝ)+β), sq_nonneg s]
  have ht3 : ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) ≤ 32/49 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*((2-β)^2+s^2))]
    nlinarith [hD4, hY]
  have ht4 : ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) ≤ 512/2401 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*((2-β)^2+s^2)^2)]
    nlinarith [hD4, hY, sq_nonneg ((2-β)^2-β^2), sq_nonneg ((2-β)^2+s^2)]
  have ht5 : ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) ≤ 16384/117649 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 16*((2-β)^2+s^2)^3)]
    nlinarith [hD4, hY, sq_nonneg ((2-β)^2-β^2), sq_nonneg ((2-β)^2+s^2),
      sq_nonneg (((2-β)^2-β^2)^2 - 16), sq_nonneg (((2-β)^2-β^2) - 4)]
  simp only [TT]
  linarith

/-- The `B`-majorant is nonnegative. -/
lemma MB_nonneg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (ht0 : 0 < t) (ht1 : t ≤ 1/4) :
    0 ≤ MB β t := by
  have hb : (7:ℝ)/4 ≤ 2 - β := by linarith
  have hmu1 : 1 ≤ (4*(2-β)^2+t^2)/(2*(2-β)*t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2*(2-β) - t)]
  have h1 : 0 ≤ Real.log ((4*(2-β)^2+t^2)/(2*(2-β)*t)) := Real.log_nonneg hmu1
  have h2 : (0:ℝ) ≤ 1 - t^2/(4*(2-β)^2) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith [ht1, ht0, hb]
  exact mul_nonneg h1 h2

/-- `hBf` is nonnegative on the window. -/
lemma hBf_nonneg {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    0 ≤ hBf β s := by
  have hb : (7:ℝ)/4 ≤ 2-β := by linarith
  have h2b : (0:ℝ) < 2*(2-β) := by linarith
  have hlog1 : Real.log (7/2) ≤ Real.log (2*(2-β)) := by
    apply Real.log_le_log (by norm_num); linarith
  have hlog4 : Real.log 4 ≤ -Real.log s := by
    have h : Real.log s ≤ Real.log (1/4) := Real.log_le_log hs0 hs1
    have h4 : Real.log (1/4) = -Real.log 4 := by
      rw [show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  have h7 : 0 < Real.log (7/2) := Real.log_pos (by norm_num)
  have h4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  simp only [hBf]
  have hfrac : (0:ℝ) ≤ s^2/(4*(2-β)^2) := by positivity
  linarith

/-- `hbf` is nonnegative on the window. -/
lemma hbf_nonneg {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) :
    0 ≤ hbf β s := by
  simp only [hbf]
  by_cases hc : s ≤ β
  · rw [if_pos hc]
    have h2b : (0:ℝ) < 2*β := by linarith
    have hlog : Real.log 2 ≤ Real.log (2*β) - Real.log s := by
      rw [← Real.log_div (by positivity : (2:ℝ)*β ≠ 0) (ne_of_gt hs0)]
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hs0]
      linarith
    have hfrac : (0:ℝ) ≤ s^2/(4*β^2) := by positivity
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  · rw [if_neg hc]
    positivity

/-- `hbf` is at most `1 - log s` on the window. -/
lemma hbf_ub {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    hbf β s ≤ 1 - Real.log s := by
  simp only [hbf]
  by_cases hc : s ≤ β
  · rw [if_pos hc]
    have h2b : (0:ℝ) < 2*β := by linarith
    have hlog : Real.log (2*β) ≤ Real.log (1/2) := by
      apply Real.log_le_log h2b; linarith
    have hlog2 : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    have hfrac : s^2/(4*β^2) ≤ 1/4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*β^2)]
      nlinarith [hc, hβ0]
    rw [hlog2] at hlog
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  · rw [if_neg hc]
    rw [div_le_iff₀ hs0]
    have hlog : Real.log s ≤ 0 := Real.log_nonpos hs0.le (by linarith)
    nlinarith

/-- Upper bound for `hBf` on the window. -/
lemma hBf_ub {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    hBf β s ≤ Real.log 4 - Real.log s + 1/196 := by
  have hb : (7:ℝ)/4 ≤ 2-β := by linarith
  have h2b : (0:ℝ) < 2*(2-β) := by linarith
  have hlog : Real.log (2*(2-β)) ≤ Real.log 4 := Real.log_le_log h2b (by linarith)
  have hfrac : s^2/(4*(2-β)^2) ≤ 1/196 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*(2-β)^2)]
    nlinarith [hs1, hs0, sq_nonneg ((2:ℝ)-β)]
  simp only [hBf]; linarith

/-- Coarse upper bound for the `B`-majorant on the window. -/
lemma MB_le_log4 {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    MB β s ≤ Real.log 4 - Real.log s + 1/196 := by
  have hβ2 : β < 2 := by linarith
  have h1 := MB_le hβ0 hβ2 hs0
  have h2 := hBf_ub hβ0 hβ1 hs0 hs1
  linarith

/-- The `β`-majorant is nonnegative. -/
lemma Mb_nonneg {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (ht0 : 0 < t) (ht1 : t ≤ 1/4) :
    0 ≤ Mb β t := by
  have hb : (0:ℝ) < 2 - β := by linarith
  rw [Mb]
  by_cases hc : t ≤ β
  · rw [if_pos hc]
    have hmu1 : 1 ≤ (4*β^2+t^2)/(2*β*t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2*β - t)]
    have h1 : 0 ≤ Real.log ((4*β^2+t^2)/(2*β*t)) := Real.log_nonneg hmu1
    have h2 : (0:ℝ) ≤ 1 - t^2/(2*((2-β)^2+β^2)) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith [ht0, ht1, hβ0, hβ1]
    exact mul_nonneg h1 h2
  · rw [if_neg hc]
    have h1 : (0:ℝ) < t*Real.sqrt ((2-β)^2+t^2) := by positivity
    have h2 : (0:ℝ) ≤ (2-β) := by linarith
    positivity

/-- Coarse upper bound for the `β`-majorant on the window. -/
lemma Mb_le_one {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    Mb β s ≤ 1 - Real.log s := by
  have h1 := Mb_le hβ0 hβ1 hs0
  have h2 := hbf_ub hβ0 hβ1 hs0 hs1
  linarith


/-! ## Measurability -/

lemma measurable_G (β : ℝ) : Measurable (G β) := by
  unfold G TT MBbig Mb MB
  refine Measurable.sub (Measurable.sub ?_ ?_) ?_
  · repeat' first | apply Measurable.add | apply Measurable.mul | fun_prop
  · exact Measurable.ite (measurableSet_le measurable_abs measurable_const) (by fun_prop) (by fun_prop)
  · exact Measurable.ite (measurableSet_le measurable_abs measurable_const) (by fun_prop) (by fun_prop)

lemma measurable_LOW (β : ℝ) : Measurable (LOW β) := by
  unfold LOW hBf hbf
  refine Measurable.sub (Measurable.sub ?_ ?_) ?_
  · repeat' first | apply Measurable.add | apply Measurable.mul | fun_prop
  · fun_prop
  · exact Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) (by fun_prop)

lemma measurable_hbf (β : ℝ) : Measurable (hbf β) := by
  unfold hbf
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) (by fun_prop)

/-! ## Pointwise bounds by an integrable dominating function -/

private lemma term_h_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) ≤ 117/25 := by
  have ht1 : (3/2-β)/((3/2-β)^2+s^2) ≤ 4/5 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (3/2-β)^2+s^2)]
    nlinarith [sq_nonneg ((3:ℝ)/2-β), sq_nonneg s, hβ1, hβ0]
  have ht2 : (1+β)/((1+β)^2+s^2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+β)^2+s^2)]
    nlinarith [sq_nonneg ((1:ℝ)+β), sq_nonneg s]
  linarith

/-- The integrand is dominated by `9 - 2 log s` on the window. -/
lemma norm_G_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    ‖G β s‖ ≤ 9 - 2 * Real.log s := by
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs0.le (by linarith)
  have hTT := TT_ub hβ0 hβ1 hs0 hs1
  have hMB0 := MB_nonneg hβ0 hβ1 hs0 hs1
  have hMb0 := Mb_nonneg hβ0 hβ1 hs0 hs1
  have hMBl := MB_le_log4 hβ0 hβ1 hs0 hs1
  have hMbl := Mb_le_one hβ0 hβ1 hs0 hs1
  have hlog4 : Real.log 4 ≤ 2 := by
    have h := Real.log_two_lt_d9
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hTT0 : 0 ≤ TT β s := by
    have hA : (0:ℝ) < 3/2-β := by linarith
    have hB : (0:ℝ) < 1+β := by linarith
    have hD : (0:ℝ) < (2-β)^2-β^2 := by nlinarith
    have hb : (0:ℝ) < 2-β := by linarith
    have h1 : (0:ℝ) ≤ (3/2-β)/((3/2-β)^2+s^2) := div_nonneg hA.le (by positivity)
    have h2 : (0:ℝ) ≤ (1+β)/((1+β)^2+s^2) := div_nonneg hB.le (by positivity)
    have h3 : (0:ℝ) ≤ ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) := div_nonneg hD.le (by positivity)
    have h4 : (0:ℝ) ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) := div_nonneg (by positivity) (by positivity)
    have h5 : (0:ℝ) ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) := div_nonneg (by positivity) (by positivity)
    simp only [TT]
    linarith
  rw [Real.norm_eq_abs, abs_le]
  rw [G_eq hβ1 hs0 hs1]
  constructor <;> linarith

/-- The lower-bound function is dominated by `9 - 2 log s` on the window. -/
lemma norm_LOW_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hs0 : 0 < s) (hs1 : s ≤ 1/4) :
    ‖LOW β s‖ ≤ 9 - 2 * Real.log s := by
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs0.le (by linarith)
  have hth := term_h_le hβ0 hβ1 hs0 hs1
  have hB0 := hBf_nonneg hβ0 hβ1 hs0 hs1
  have hb0 := hbf_nonneg hβ0 hβ1 hs0
  have hBu := hBf_ub hβ0 hβ1 hs0 hs1
  have hbu := hbf_ub hβ0 hβ1 hs0 hs1
  have hlog4 : Real.log 4 ≤ 2 := by
    have h := Real.log_two_lt_d9
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hth0 : (0:ℝ) ≤ (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) := by
    have hA : (0:ℝ) < 3/2-β := by linarith
    have hB : (0:ℝ) < 1+β := by linarith
    have h1 : (0:ℝ) ≤ (3/2-β)/((3/2-β)^2+s^2) := div_nonneg hA.le (by positivity)
    have h2 : (0:ℝ) ≤ (1+β)/((1+β)^2+s^2) := div_nonneg hB.le (by positivity)
    have := add_nonneg h1 h2
    positivity
  rw [Real.norm_eq_abs, abs_le]
  simp only [LOW]
  constructor <;> linarith

/-! ## Interval integrability on `[0,1/4]` -/

lemma intervalIntegrable_dom :
    IntervalIntegrable (fun s : ℝ => 9 - 2 * Real.log s) volume (0:ℝ) (1/4) := by
  have h1 : IntervalIntegrable (fun s : ℝ => (9:ℝ) + (-2) * Real.log s) volume (0:ℝ) (1/4) :=
    intervalIntegrable_const.add (intervalIntegrable_log'.const_mul (-2))
  have h2 : (fun s : ℝ => (9:ℝ) + (-2) * Real.log s) = fun s : ℝ => 9 - 2 * Real.log s := by
    funext s; ring
  rwa [h2] at h1

lemma intervalIntegrable_G {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    IntervalIntegrable (G β) volume (0:ℝ) (1/4) := by
  refine IntervalIntegrable.mono_fun' (f := G β) (g := fun s : ℝ => 9 - 2 * Real.log s)
    intervalIntegrable_dom ?_ ?_
  · exact (measurable_G β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hx
    exact norm_G_le hβ0 hβ1 hx.1 hx.2

lemma intervalIntegrable_LOW {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    IntervalIntegrable (LOW β) volume (0:ℝ) (1/4) := by
  refine IntervalIntegrable.mono_fun' (f := LOW β) (g := fun s : ℝ => 9 - 2 * Real.log s)
    intervalIntegrable_dom ?_ ?_
  · exact (measurable_LOW β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hx
    exact norm_LOW_le hβ0 hβ1 hx.1 hx.2

/-! ## The elementary integrals -/

/-- `∫_0^u log s ds = u log u - u`. -/
theorem integral_zero_u_log {u : ℝ} (hu : 0 < u) :
    (∫ s in (0:ℝ)..u, Real.log s) = u * Real.log u - u := by
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) u,
      HasDerivAt (fun s : ℝ => s * Real.log s - s) (Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log x + 1) x := by
      have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
      have h' : HasDerivAt (fun s : ℝ => s * Real.log s) ((1 : ℝ) * Real.log x + x * x⁻¹) x := h
      have hval : (1 : ℝ) * Real.log x + x * x⁻¹ = Real.log x + 1 := by
        rw [one_mul, mul_inv_cancel₀ hx0, add_comm]
      rwa [hval] at h'
    have h2 : HasDerivAt (fun s : ℝ => s) 1 x := hasDerivAt_id x
    have h3 := h1.sub h2
    have hval2 : Real.log x + 1 - 1 = Real.log x := by ring
    rwa [hval2] at h3
  have hint : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) u := intervalIntegrable_log'
  have hlim0 : Tendsto (fun s : ℝ => s * Real.log s - s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.log s * s ^ (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    have h1' : Tendsto (fun s : ℝ => s * Real.log s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa [Real.rpow_one, mul_comm] using h1
    have h2 : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h1'.sub h2
  have hlimu : Tendsto (fun s : ℝ => s * Real.log s - s) (𝓝[<] u)
      (𝓝 (u * Real.log u - u)) := by
    have hcont : ContinuousAt (fun s : ℝ => s * Real.log s - s) u := by
      apply ContinuousAt.sub
      · exact continuousAt_id.mul (Real.continuousAt_log (ne_of_gt hu))
      · exact continuousAt_id
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0:ℝ)) (b := u)
    (f := fun s : ℝ => s * Real.log s - s) (f' := fun s : ℝ => Real.log s) hu hderiv hint hlim0 hlimu
  linarith

/-- `∫_β^{1/4} ds/s = log(1/4) - log β`. -/
lemma integral_inv_beta {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in β..(1/4), 1/s) = Real.log (1/4) - Real.log β := by
  have hderiv : ∀ x ∈ Set.uIcc β (1/4), HasDerivAt Real.log (1/x) x := by
    intro x hx
    rw [Set.uIcc_of_le hβ1] at hx
    have hx0 : x ≠ 0 := by
      have : 0 < x := lt_of_lt_of_le hβ0 hx.1
      exact ne_of_gt this
    simpa [one_div] using Real.hasDerivAt_log hx0
  have hint : IntervalIntegrable (fun s : ℝ => 1/s) volume β (1/4) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hβ1] at hx
    have : 0 < x := lt_of_lt_of_le hβ0 hx.1
    exact ne_of_gt this
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using h

/-- `∫_0^{1/4} (A/(A²+s²) + B/(B²+s²)) = arctan(1/(6-4β)) + arctan(1/(4+4β))`. -/
lemma integral_hterm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in (0:ℝ)..(1/4), ((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)))
      = Real.arctan (1/(6-4*β)) + Real.arctan (1/(4+4*β)) := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hi1 : IntervalIntegrable (fun s : ℝ => (3/2-β)/((3/2-β)^2+s^2)) volume (0:ℝ) (1/4) := by
    apply Continuous.intervalIntegrable
    exact Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
  have hi2 : IntervalIntegrable (fun s : ℝ => (1+β)/((1+β)^2+s^2)) volume (0:ℝ) (1/4) := by
    apply Continuous.intervalIntegrable
    exact Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
  rw [intervalIntegral.integral_add hi1 hi2]
  have h1 := integral_inv_sq_add (k := 3/2-β) (p := (0:ℝ)) (q := 1/4) hA
  have h2 := integral_inv_sq_add (k := 1+β) (p := (0:ℝ)) (q := 1/4) hB
  rw [h1, h2]
  have e1 : (1/4 : ℝ)/(3/2-β) = 1/(6-4*β) := by
    rw [show (6:ℝ)-4*β = 4*(3/2-β) by ring]
    field_simp
  have e2 : (1/4 : ℝ)/(1+β) = 1/(4+4*β) := by
    rw [show (4:ℝ)+4*β = 4*(1+β) by ring]
    field_simp
  rw [e1, e2]
  simp only [zero_div, Real.arctan_zero, sub_zero]
  try ring

/-- `∫_0^{1/4} hBf β = (1/4)log(2(2-β)) + (1/4)log 4 + 1/4 + 1/(768 (2-β)²)`. -/
lemma integral_hBf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in (0:ℝ)..(1/4), hBf β s)
      = (1/4)*Real.log (2*(2-β)) + (1/4)*Real.log 4 + 1/4 + 1/(768*(2-β)^2) := by
  have hb : (0:ℝ) < 2-β := by linarith
  have heq : (fun s : ℝ => hBf β s)
      = fun s : ℝ => Real.log (2*(2-β)) - Real.log s + s^2/(4*(2-β)^2) := by
    funext s; simp [hBf]
  rw [heq]
  have hi1 : IntervalIntegrable (fun _ : ℝ => Real.log (2*(2-β))) volume (0:ℝ) (1/4) :=
    intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) (1/4) := intervalIntegrable_log'
  have hi3 : IntervalIntegrable (fun s : ℝ => s^2/(4*(2-β)^2)) volume (0:ℝ) (1/4) := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) continuous_const (fun s => by positivity)
  rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2]
  rw [intervalIntegral.integral_const, integral_zero_u_log (by norm_num : (0:ℝ) < 1/4)]
  have hsq : (∫ s in (0:ℝ)..(1/4), s^2) = (1/4)^3/3 := by
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (1/4),
        HasDerivAt (fun s : ℝ => s^3/3) (x^2) x := by
      intro x _
      have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
      refine h.congr_deriv ?_
      ring
    have hint : IntervalIntegrable (fun s : ℝ => s^2) volume (0:ℝ) (1/4) := by
      apply Continuous.intervalIntegrable; fun_prop
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => s^3/3) (f' := fun s : ℝ => s^2) hderiv hint
    rw [h]
    norm_num
  have hs2 : (∫ s in (0:ℝ)..(1/4), s^2/(4*(2-β)^2)) = (1/(4*(2-β)^2)) * ((1/4)^3/3) := by
    rw [← hsq, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hs2]
  have hlog14 : Real.log (1/4) = -Real.log 4 := by
    rw [show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog14]
  have hpos : (16 - β*16 + β^2*4) ≠ 0 := by
    have : (0:ℝ) < 16 - β*16 + β^2*4 := by nlinarith [sq_nonneg (β*2-4)]
    exact ne_of_gt this
  field_simp
  ring

/-- `∫_0^{1/4} hbf β = β log 2 + β + β/12 + β log(1/(4β))`. -/
lemma integral_hbf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in (0:ℝ)..(1/4), hbf β s)
      = β*Real.log 2 + β + β/12 + β*Real.log (1/(4*β)) := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hbne : β ≠ 0 := ne_of_gt hβ0
  have hβ4 : (0:ℝ) < β := hβ0
  -- integrability of `hbf β` on `[0,1/4]`
  have hInt : IntervalIntegrable (hbf β) volume (0:ℝ) (1/4) := by
    refine IntervalIntegrable.mono_fun' (f := hbf β) (g := fun s : ℝ => 9 - 2 * Real.log s)
      intervalIntegrable_dom ?_ ?_
    · exact (measurable_hbf β).aestronglyMeasurable
    · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro x hx
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have h0 := hbf_nonneg hβ0 hβ1 hx0
      have h1 := hbf_ub hβ0 hβ1 hx0 hx1
      have hlogs : Real.log x ≤ 0 := Real.log_nonpos hx0.le (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      linarith
  have hsplit : (∫ s in (0:ℝ)..(1/4), hbf β s)
      = (∫ s in (0:ℝ)..β, hbf β s) + (∫ s in β..(1/4), hbf β s) := by
    refine (integral_add_adjacent_intervals ?_ ?_).symm
    · refine hInt.mono_set ?_
      intro x hx
      rw [Set.uIcc_of_le hβ0.le] at hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)]
      exact ⟨hx.1, le_trans hx.2 hβ1⟩
    · refine hInt.mono_set ?_
      intro x hx
      rw [Set.uIcc_of_le hβ1] at hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)]
      exact ⟨le_trans hβ0.le hx.1, hx.2⟩
  rw [hsplit]
  -- first half
  have hfirst : (∫ s in (0:ℝ)..β, hbf β s)
      = (∫ s in (0:ℝ)..β, (Real.log (2*β) - Real.log s + s^2/(4*β^2))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hβ0.le] at hx
    simp only [hbf]
    rw [if_pos hx.2]
  have hsecond : (∫ s in β..(1/4), hbf β s) = (∫ s in β..(1/4), β/s) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le hβ1] at hx
    simp only [hbf]
    rw [if_neg (not_le.mpr hx.1)]
  rw [hfirst, hsecond]
  have hiA : IntervalIntegrable (fun _ : ℝ => Real.log (2*β)) volume (0:ℝ) β := intervalIntegrable_const
  have hiB : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) β := intervalIntegrable_log'
  have hiC : IntervalIntegrable (fun s : ℝ => s^2/(4*β^2)) volume (0:ℝ) β := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) continuous_const (fun s => by positivity)
  rw [intervalIntegral.integral_add (hiA.sub hiB) hiC, intervalIntegral.integral_sub hiA hiB]
  rw [intervalIntegral.integral_const, integral_zero_u_log hβ0]
  have hsq : (∫ s in (0:ℝ)..β, s^2) = β^3/3 := by
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) β,
        HasDerivAt (fun s : ℝ => s^3/3) (x^2) x := by
      intro x _
      have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
      refine h.congr_deriv ?_
      ring
    have hint : IntervalIntegrable (fun s : ℝ => s^2) volume (0:ℝ) β := by
      apply Continuous.intervalIntegrable; fun_prop
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => s^3/3) (f' := fun s : ℝ => s^2) hderiv hint
    rw [h]
    norm_num
  have hs2 : (∫ s in (0:ℝ)..β, s^2/(4*β^2)) = (1/(4*β^2)) * (β^3/3) := by
    rw [← hsq, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hs2]
  -- second half
  have hsec2 : (∫ s in β..(1/4), β/s) = β * (Real.log (1/4) - Real.log β) := by
    have hfac : (∫ s in β..(1/4), β/s) = β * (∫ s in β..(1/4), 1/s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _; ring
    rw [hfac, integral_inv_beta hβ0 hβ1]
  rw [hsec2]
  -- log identities
  have hlog1 : Real.log (2*β) = Real.log 2 + Real.log β := Real.log_mul (by norm_num) hbne
  have hlog2 : Real.log (1/4) - Real.log β = Real.log (1/(4*β)) := by
    rw [← Real.log_div (by norm_num : (1/4:ℝ) ≠ 0) hbne]
    congr 1
    ring
  rw [hlog2]
  rw [hlog1]
  field_simp
  ring

/-! ## Integrability of the two `h`-upper bounds -/

lemma intervalIntegrable_hBf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    IntervalIntegrable (hBf β) volume (0:ℝ) (1/4) := by
  have heq : (hBf β) = fun s : ℝ => Real.log (2*(2-β)) - Real.log s + s^2/(4*(2-β)^2) := by
    funext s; simp [hBf]
  rw [heq]
  have hi1 : IntervalIntegrable (fun _ : ℝ => Real.log (2*(2-β))) volume (0:ℝ) (1/4) :=
    intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun s : ℝ => Real.log s) volume (0:ℝ) (1/4) := intervalIntegrable_log'
  have hi3 : IntervalIntegrable (fun s : ℝ => s^2/(4*(2-β)^2)) volume (0:ℝ) (1/4) := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) continuous_const (fun s => by
      have h : (2:ℝ)-β ≠ 0 := by linarith
      positivity)
  exact (hi1.sub hi2).add hi3

lemma intervalIntegrable_hbf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    IntervalIntegrable (hbf β) volume (0:ℝ) (1/4) := by
  refine IntervalIntegrable.mono_fun' (f := hbf β) (g := fun s : ℝ => 9 - 2 * Real.log s)
    intervalIntegrable_dom ?_ ?_
  · exact (measurable_hbf β).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have h0 := hbf_nonneg hβ0 hβ1 hx0
    have h1 := hbf_ub hβ0 hβ1 hx0 hx1
    have hlogs : Real.log x ≤ 0 := Real.log_nonpos hx0.le (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith

/-! ## The value of `∫_0^{1/4} LOW` and its lower bound -/

lemma integral_LOW_eq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in (0:ℝ)..(1/4), LOW β s)
      = (13/5)*(Real.arctan (1/(6-4*β)) + Real.arctan (1/(4+4*β))) + 13/80
        - (∫ s in (0:ℝ)..(1/4), hBf β s) - (∫ s in (0:ℝ)..(1/4), hbf β s) := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hi1 : IntervalIntegrable (fun s : ℝ => (3/2-β)/((3/2-β)^2+s^2)) volume (0:ℝ) (1/4) := by
    apply Continuous.intervalIntegrable
    exact Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
  have hi2 : IntervalIntegrable (fun s : ℝ => (1+β)/((1+β)^2+s^2)) volume (0:ℝ) (1/4) := by
    apply Continuous.intervalIntegrable
    exact Continuous.div continuous_const (by fun_prop) (fun s => by positivity)
  have ha : IntervalIntegrable
      (fun s : ℝ => (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)))
      volume (0:ℝ) (1/4) :=
    (hi1.add hi2).const_mul (13/5)
  have hc : IntervalIntegrable (fun _ : ℝ => (13/20:ℝ)) volume (0:ℝ) (1/4) := intervalIntegrable_const
  have hBfi := intervalIntegrable_hBf hβ0 hβ1
  have hbfi := intervalIntegrable_hbf hβ0 hβ1
  have heq1 : (LOW β) = fun s : ℝ =>
      ((13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) + 13/20) - hBf β s - hbf β s := by
    funext s; simp [LOW]
  rw [heq1]
  rw [intervalIntegral.integral_sub ((ha.add hc).sub hBfi) hbfi]
  rw [intervalIntegral.integral_sub (ha.add hc) hBfi]
  rw [intervalIntegral.integral_add ha hc]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_hterm hβ0 hβ1, intervalIntegral.integral_const]
  norm_num

/-! ## Bounds for the two `h`-integrals -/

lemma integral_hBf_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in (0:ℝ)..(1/4), hBf β s) ≤ Real.log 2 + 1/4 + 1/2352 := by
  rw [integral_hBf hβ0 hβ1]
  have hb : (0:ℝ) < 2-β := by linarith
  have hlog2 : (1/4)*Real.log (2*(2-β)) + (1/4)*Real.log 4 ≤ Real.log 2 := by
    have hlogm : Real.log ((2*(2-β))*4) = Real.log (2*(2-β)) + Real.log 4 :=
      Real.log_mul (by positivity) (by norm_num)
    have hm : (1/4)*Real.log (2*(2-β)) + (1/4)*Real.log 4 = (1/4)*Real.log ((2*(2-β))*4) := by
      rw [hlogm]; ring
    rw [hm, show (2*(2-β))*4 = 8*(2-β) by ring]
    have h16 : Real.log (8*(2-β)) ≤ Real.log 16 := Real.log_le_log (by positivity) (by linarith)
    have hlog16 : Real.log 16 = 4*Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    rw [hlog16] at h16
    linarith
  have hsmall : 1/(768*(2-β)^2) ≤ 1/2352 := by
    have h : (2352:ℝ) ≤ 768*(2-β)^2 := by nlinarith [sq_nonneg ((2:ℝ)-β), hβ1]
    exact one_div_le_one_div_of_le (by norm_num) h
  linarith

lemma integral_hbf_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in (0:ℝ)..(1/4), hbf β s) ≤ (1 + Real.log 2 + 1/12)/4 := by
  rw [integral_hbf hβ0 hβ1]
  have hlog : Real.log (1/(4*β)) ≤ 1/(4*β) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h1 : β*Real.log (1/(4*β)) ≤ β*(1/(4*β) - 1) := mul_le_mul_of_nonneg_left hlog hβ0.le
  have hbne : β ≠ 0 := ne_of_gt hβ0
  have h2 : β*(1/(4*β) - 1) = 1/4 - β := by
    field_simp
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [h2] at h1
  nlinarith [h1, hl2, hβ0, hβ1]

/-! ## The two transcendental estimates -/

lemma arctan_fifth_ge : (1973:ℝ)/10000 ≤ Real.arctan (1/5) := by
  have h := Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 (1/5) (by norm_num)
  have h2 : (1973:ℝ)/10000 ≤ 1/5 - (1/5)^3/3 + (1/5)^5/5 - (1/5)^7/7 + (1/5)^9/9
      - (1/5)^11/11 + (1/5)^13/13 - (1/5)^15/15 := by norm_num
  linarith

lemma phi_ge {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    2*Real.arctan (1/5) ≤ Real.arctan (1/(6-4*β)) + Real.arctan (1/(4+4*β)) := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hd1 : (0:ℝ) < 6-4*β := by linarith
  have hd2 : (0:ℝ) < 4+4*β := by linarith
  have h2 : 2*Real.arctan (1/5) = Real.arctan (5/12) := by
    have h := Real.arctan_add (x := (1/5:ℝ)) (y := (1/5:ℝ)) (by norm_num)
    have h' : ((1:ℝ)/5 + 1/5) / (1 - (1/5)*(1/5)) = 5/12 := by norm_num
    rw [h'] at h
    rw [two_mul]
    exact h
  have h1 : Real.arctan (1/(6-4*β)) + Real.arctan (1/(4+4*β))
      = Real.arctan (10/((6-4*β)*(4+4*β) - 1)) := by
    have hprod : (1/(6-4*β))*(1/(4+4*β)) < 1 := by
      rw [div_mul_div_comm, div_lt_one (by positivity)]
      nlinarith [sq_nonneg (β - 1/4), hβ1]
    have h := Real.arctan_add (x := 1/(6-4*β)) (y := 1/(4+4*β)) hprod
    have h' : (1/(6-4*β) + 1/(4+4*β)) / (1 - (1/(6-4*β))*(1/(4+4*β)))
        = 10/((6-4*β)*(4+4*β) - 1) := by
      field_simp
      ring
    rw [h'] at h
    exact h
  rw [h2, h1]
  apply Real.arctan_mono
  rw [le_div_iff₀ (by nlinarith [sq_nonneg (β - 1/4), hβ1] :
      (0:ℝ) < (6-4*β)*(4+4*β) - 1)]
  nlinarith [sq_nonneg (4*β - 1), hβ1]

/-! ## The half-integral is even and the final assembly -/

lemma integral_G_even {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) :
    (∫ s in (-(1/4):ℝ)..(1/4), G β s) = 2 * (∫ s in (0:ℝ)..(1/4), G β s) := by
  have hInt0 : IntervalIntegrable (G β) volume (0:ℝ) (1/4) := intervalIntegrable_G hβ0 hβ1
  have hInt1 : IntervalIntegrable (G β) volume (-(1/4):ℝ) (0:ℝ) := by
    have hc := (IntervalIntegrable.iff_comp_neg (f := G β) (a := (0:ℝ)) (b := (1/4:ℝ))).mp hInt0
    rw [show (fun x : ℝ => G β (-x)) = G β by funext x; exact G_neg β x] at hc
    simpa using hc.symm
  have hsym : (∫ s in (-(1/4):ℝ)..(0:ℝ), G β s) = (∫ s in (0:ℝ)..(1/4), G β s) := by
    have h := intervalIntegral.integral_comp_neg (f := G β) (a := (0:ℝ)) (b := (1/4:ℝ))
    simp only [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    exact G_neg β x
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt1 hInt0, hsym]
  ring

lemma final_arith :
    (-53:ℝ)/200 ≤ (13/5)*2*(1973/10000) + 13/80
      - ((6931471808:ℝ)/10^10 + 1/4 + 1/2352) - ((1 + (6931471808:ℝ)/10^10 + 1/12)/4) := by
  norm_num

end

end BoxWinSB

open BoxWinSB in
/-- For `β ≤ 1/4` the target integral over `[-1/4,1/4]` is bounded below by `-53/100`. -/
theorem boxWin_small_beta {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1/4) :
    (-53:ℝ)/100 ≤ ∫ s in ((-1:ℝ)/4)..(1/4),
      ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - (if (|s|:ℝ) ≤ 2-β then Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
        - (if (|s|:ℝ) ≤ β then Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) ) := by
  have hfun : (fun s : ℝ =>
      ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - (if (|s|:ℝ) ≤ 2-β then Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
        - (if (|s|:ℝ) ≤ β then Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ)*Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )) = G β := by
    funext s
    have hs2 : |s|^2 = s^2 := sq_abs s
    simp only [G, TT, MBbig, Mb, MB, hs2]
  rw [hfun]
  have hIntG := intervalIntegrable_G h0 h1
  have hIntL := intervalIntegrable_LOW h0 h1
  have hae : LOW β ≤ᵐ[volume.restrict (Set.Icc (0:ℝ) (1/4))] G β := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
    have hmeas : MeasurableSet {x : ℝ | ¬ (LOW β x ≤ G β x)} :=
      (measurableSet_le (measurable_LOW β) (measurable_G β)).compl
    rw [Measure.restrict_apply hmeas]
    refine measure_mono_null ?_ (measure_singleton (0:ℝ))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc] at hx
    obtain ⟨hbad, hx0, hx1⟩ := hx
    by_contra hne
    exact hbad (G_lower h0 h1 (lt_of_le_of_ne hx0 (Ne.symm hne)) hx1)
  have hmono : (∫ s in (0:ℝ)..(1/4), LOW β s) ≤ (∫ s in (0:ℝ)..(1/4), G β s) :=
    intervalIntegral.integral_mono_ae_restrict (by norm_num : (0:ℝ) ≤ 1/4) hIntL hIntG hae
  have hLOW := integral_LOW_eq h0 h1
  have hphi := phi_ge h0 h1
  have hBf := integral_hBf_le h0 h1
  have hbf := integral_hbf_le h0 h1
  have harct := arctan_fifth_ge
  have hl2 : Real.log 2 ≤ (6931471808:ℝ)/10^10 := by
    have h := Real.log_two_lt_d9
    have h' : (0.6931471808 : ℝ) = 6931471808/10^10 := by norm_num
    rw [h'] at h
    exact le_of_lt h
  have hhalf : (-53:ℝ)/200 ≤ (∫ s in (0:ℝ)..(1/4), G β s) := by
    rw [hLOW] at hmono
    have harith := final_arith
    nlinarith [hmono, hphi, hBf, hbf, harct, hl2, harith]
  have heven := integral_G_even h0 h1
  have hfin : (-53:ℝ)/100 ≤ 2 * (∫ s in (0:ℝ)..(1/4), G β s) := by linarith
  have : ((-1:ℝ)/4) = -(1/4 : ℝ) := by norm_num
  rw [this, heven]
  linarith


end Commons.Analysis.Integral