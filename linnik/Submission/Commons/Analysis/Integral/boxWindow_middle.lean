import Mathlib
import Submission.Commons.Analysis.Integral.boxWindow_B_lower_11_20
import Submission.Commons.Analysis.Integral.boxWindow_C_lower
import Submission.Commons.Analysis.Integral.boxMaj_le_target_kernel_ge_sixth
import Submission.Commons.Analysis.Integral.boxWindow_sixth_upper
import Submission.Commons.Analysis.Integral.boxWindow_sixth_lower
import Submission.Commons.Analysis.Integral.boxWindow_threequarter_pointwise


namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral

noncomputable section

/-!
# `boxWindow_middle`

We prove that for `0 < β < 1` and `δ ∈ [-1/6, 1/6]` the window integral
`∫_δ^{δ+1} E(β,s) ds` of the target integrand `E` is nonnegative.

The integrand is even in `s`.  Writing `Φ(t) = ∫_0^t E(β,s) ds`, the key estimates are

* `Φ(1/4) ≥ -53/200` (from `boxWindow_C_lower` + evenness),
* `∫_{1/4}^{3/4} E ≥ 11/20` (from `boxWindow_B_lower_11_20`),
* `E ≥ 0` for `s ≥ 1/6` (from `boxMaj_le_target_kernel_ge_sixth`),
* `∫_{3/4}^{5/6} E ≥ 1/10` (from `boxWindow_threequarter_pointwise`),
* `Φ(t) ≤ 1/4` for `t ∈ [0,1/6]` (from `boxWindow_sixth_upper`),
* `Φ(t) ≥ -1/3` for `t ∈ [0,1/6]` (from `boxWindow_sixth_lower`).

Then for `δ ∈ [0,1/6]` we have
`∫_δ^{δ+1} E = Φ(δ+1) - Φ(δ) ≥ (Φ(1/4) + 11/20) - 1/4 = 7/200 > 0`,
while for `δ ∈ [-1/6,0]` we have
`∫_δ^{δ+1} E = Φ(-δ) + Φ(δ+1) ≥ -1/3 + 77/200 = 31/600 > 0`.
-/

/-- The integrand of the target statement (verbatim). -/
def boxI (β : ℝ) (s : ℝ) : ℝ :=
  ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
    - ( (if (|s|:ℝ) ≤ 2-β then
          Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
         else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
       + (if (|s|:ℝ) ≤ β then
          Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
         else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) )
    + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) )

lemma boxI_even (β : ℝ) (s : ℝ) : boxI β (-s) = boxI β s := by
  unfold boxI
  simp only [abs_neg]
  ring

/-- On `(0,3/4]` the target integrand coincides with the version `boxE` of
`boxWindow_B_lower_11_20`. -/
lemma boxI_eq_boxE {β s : ℝ} (hs0 : 0 < s) (hs : s ≤ 3/4) (hβ1 : β < 1) :
    boxI β s = boxE β s := by
  have h2b : s ≤ 2 - β := by linarith
  unfold boxI boxE
  rw [abs_of_pos hs0, if_pos h2b]
  ring

section pieces

/-- The positive part of the integrand. -/
def bxT (β s : ℝ) : ℝ :=
    (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)

/-- The `2-β` majorant. -/
def bxB (β s : ℝ) : ℝ :=
  if (|s|:ℝ) ≤ 2-β then
    Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
  else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))

/-- The `β` majorant. -/
def bxb (β s : ℝ) : ℝ :=
  if (|s|:ℝ) ≤ β then
    Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
  else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))

lemma boxI_eq_pieces (β s : ℝ) : boxI β s = bxT β s - bxB β s - bxb β s := by
  unfold boxI bxT bxB bxb; ring

lemma bxT_nonneg {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 ≤ bxT β s := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hD : (0:ℝ) ≤ (2-β)^2 - β^2 := by nlinarith
  unfold bxT
  have h1 : 0 ≤ (3/2-β)/((3/2-β)^2+s^2) := div_nonneg hA.le (by positivity)
  have h2 : 0 ≤ (1+β)/((1+β)^2+s^2) := div_nonneg hB.le (by positivity)
  have h3 : 0 ≤ ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) := div_nonneg hD (by positivity)
  have h4 : 0 ≤ ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) := div_nonneg (by positivity) (by positivity)
  have h5 : 0 ≤ ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) := div_nonneg (by positivity) (by positivity)
  linarith

lemma bxT_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : bxT β s ≤ 15 := by
  have hA : (0:ℝ) < 3/2-β := by linarith
  have hB : (0:ℝ) < 1+β := by linarith
  have hA2 : (1:ℝ) ≤ (2-β)^2 := by nlinarith
  have hDle : (2-β)^2 - β^2 ≤ 4 := by nlinarith [hβ0]
  have hD0 : (0:ℝ) ≤ (2-β)^2 - β^2 := by nlinarith
  have hkey : (3/2-β)*(1+β) ≥ 1 := by nlinarith
  have h13 : (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) ≤ 13/2 := by
    have e : (3/2-β)/((3/2-β)^2+s^2) ≤ 1/(3/2-β) := by
      rw [div_le_div_iff₀ (by positivity) hA]; nlinarith [sq_nonneg s]
    have e2 : (1+β)/((1+β)^2+s^2) ≤ 1/(1+β) := by
      rw [div_le_div_iff₀ (by positivity) hB]; nlinarith [sq_nonneg s]
    have e3 : 1/(3/2-β) + 1/(1+β) ≤ 5/2 := by
      rw [div_add_div _ _ (ne_of_gt hA) (ne_of_gt hB)]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (3/2-β)*(1+β))]
      nlinarith
    linarith
  have h2 : ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h3 : ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  unfold bxT
  linarith

lemma bxB_abs_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) :
    |bxB β s| ≤ 25 + |Real.log s| := by
  have hA : (0:ℝ) < 2 - β := by linarith
  rw [bxB, abs_of_pos hs0]
  by_cases h : s ≤ 2 - β
  · rw [if_pos h]
    have h20 : 4*(2-β)^2+s^2 ≤ 21 := by nlinarith [sq_nonneg β, sq_nonneg s, hA, hβ1, h]
    have hlog_num : Real.log (4*(2-β)^2+s^2) ≤ 21 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4*(2-β)^2+s^2 by positivity)
      linarith
    have hnum0 : (0:ℝ) ≤ Real.log (4*(2-β)^2+s^2) := Real.log_nonneg (by nlinarith [hA])
    have hlog_2A : Real.log (2*(2-β)) ≤ 3 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2*(2-β) by positivity)
      nlinarith
    have h2A0 : (0:ℝ) ≤ Real.log (2*(2-β)) := Real.log_nonneg (by linarith)
    have hsplit : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))
        = Real.log (4*(2-β)^2+s^2) - Real.log (2*(2-β)) - Real.log s := by
      rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (by positivity : (2:ℝ)*(2-β) ≠ 0) (ne_of_gt hs0)]
      ring
    have hcoef : |1 - s^2/(4*(2-β)^2)| ≤ 1 := by
      have hx2 : s^2/(4*(2-β)^2) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [h, hA, sq_nonneg (s - (2-β)), sq_nonneg s]
      have hx : (0:ℝ) ≤ s^2/(4*(2-β)^2) := div_nonneg (sq_nonneg s) (by positivity)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hsplit, abs_mul]
    have hmain : |Real.log (4*(2-β)^2+s^2) - Real.log (2*(2-β)) - Real.log s|
        ≤ 21 + 3 + |Real.log s| := by
      have hab : |Real.log (4*(2-β)^2+s^2) - Real.log (2*(2-β))|
          ≤ |Real.log (4*(2-β)^2+s^2)| + |Real.log (2*(2-β))| := abs_sub _ _
      have hs2 : |Real.log (4*(2-β)^2+s^2) - Real.log (2*(2-β)) - Real.log s|
          ≤ |Real.log (4*(2-β)^2+s^2) - Real.log (2*(2-β))| + |Real.log s| := abs_sub _ _
      rw [abs_of_nonneg hnum0, abs_of_nonneg h2A0] at hab
      linarith
    calc |Real.log (4*(2-β)^2+s^2) - Real.log (2*(2-β)) - Real.log s| * |1 - s^2/(4*(2-β)^2)|
        ≤ (21 + 3 + |Real.log s|) * 1 :=
          mul_le_mul hmain hcoef (abs_nonneg _) (by positivity)
      _ ≤ 25 + |Real.log s| := by linarith [abs_nonneg (Real.log s)]
  · rw [if_neg h]
    have hden : (2-β) ≤ Real.sqrt ((2-β)^2+s^2) := by
      have h2 : Real.sqrt ((2-β)^2) ≤ Real.sqrt ((2-β)^2+s^2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq hA.le] at h2
    have hlt : 2 - β < s := not_le.mp h
    rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
    rw [div_le_iff₀ (by positivity)]
    have hsq : (2-β)*(2-β) ≤ s * Real.sqrt ((2-β)^2+s^2) :=
      mul_le_mul hlt.le hden hA.le (by linarith)
    have h1 : (1:ℝ) ≤ 21 + |Real.log s| := by linarith [abs_nonneg (Real.log s)]
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ s * Real.sqrt ((2-β)^2+s^2))
    nlinarith [hsq, h2]

lemma bxb_abs_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) :
    |bxb β s| ≤ 7 + 4 * |Real.log s| := by
  have hA : (0:ℝ) < 2 - β := by linarith
  rw [bxb, abs_of_pos hs0]
  by_cases h : s ≤ β
  · rw [if_pos h]
    have hs1 : s ≤ 1 := by linarith
    have hlog_s_nonpos : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1
    have habs_s : |Real.log s| = -Real.log s := abs_of_nonpos hlog_s_nonpos
    have hnum_le : Real.log (4*β^2+s^2) ≤ 6 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4*β^2+s^2 by positivity)
      nlinarith [sq_nonneg s, sq_nonneg β, hβ1, h]
    have hnum_ge : -Real.log (4*β^2+s^2) ≤ 2*|Real.log s| := by
      have hss : 0 < s*s := by positivity
      have hle : s*s ≤ 4*β^2+s^2 := by nlinarith [sq_nonneg β]
      have hlog := Real.log_le_log hss hle
      have e : Real.log (s*s) = 2*Real.log s := by
        rw [Real.log_mul (ne_of_gt hs0) (ne_of_gt hs0)]; ring
      rw [e] at hlog
      rw [habs_s]; linarith
    have hnum_abs : |Real.log (4*β^2+s^2)| ≤ 6 + 2*|Real.log s| :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hlog_beta : |Real.log (2*β)| ≤ 1 + |Real.log s| := by
      have hlt : Real.log s ≤ Real.log β := Real.log_le_log hs0 h
      have hbeta_nonpos : Real.log β ≤ 0 := Real.log_nonpos hβ0.le (by linarith)
      have habs_beta : |Real.log β| = -Real.log β := abs_of_nonpos hbeta_nonpos
      have h1 : Real.log (2*β) = Real.log 2 + Real.log β :=
        Real.log_mul (by norm_num) (ne_of_gt hβ0)
      rw [h1]
      have h2 : |Real.log 2 + Real.log β| ≤ |Real.log 2| + |Real.log β| := abs_add_le _ _
      have h3 : |Real.log 2| ≤ 1 := by
        rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
        exact le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
      have h4 : |Real.log β| ≤ |Real.log s| := by
        rw [habs_beta, habs_s]; linarith
      linarith
    have hcoef : |1 - s^2/(2*((2-β)^2+β^2))| ≤ 1 := by
      have hx : (0:ℝ) ≤ s^2/(2*((2-β)^2+β^2)) := div_nonneg (sq_nonneg s) (by positivity)
      have hx2 : s^2/(2*((2-β)^2+β^2)) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [h, hβ0, hβ1, sq_nonneg (s - β), sq_nonneg s, sq_nonneg β]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hsplit : Real.log ((4*β^2+s^2)/(2*β*s))
        = Real.log (4*β^2+s^2) - Real.log (2*β) - Real.log s := by
      rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (by positivity : (2:ℝ)*β ≠ 0) (ne_of_gt hs0)]
      ring
    rw [hsplit, abs_mul]
    have hmain : |Real.log (4*β^2+s^2) - Real.log (2*β) - Real.log s|
        ≤ 7 + 4 * |Real.log s| := by
      have hab : |Real.log (4*β^2+s^2) - Real.log (2*β)|
          ≤ |Real.log (4*β^2+s^2)| + |Real.log (2*β)| := abs_sub _ _
      have hs2 : |Real.log (4*β^2+s^2) - Real.log (2*β) - Real.log s|
          ≤ |Real.log (4*β^2+s^2) - Real.log (2*β)| + |Real.log s| := abs_sub _ _
      linarith
    calc |Real.log (4*β^2+s^2) - Real.log (2*β) - Real.log s| * |1 - s^2/(2*((2-β)^2+β^2))|
        ≤ (7 + 4 * |Real.log s|) * 1 :=
          mul_le_mul hmain hcoef (abs_nonneg _) (by positivity)
      _ = 7 + 4 * |Real.log s| := by ring
  · rw [if_neg h]
    have hlt : β < s := not_le.mp h
    have hden : 2-β ≤ Real.sqrt ((2-β)^2+s^2) := by
      have h2 : Real.sqrt ((2-β)^2) ≤ Real.sqrt ((2-β)^2+s^2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq hA.le] at h2
    rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
    rw [div_le_iff₀ (by positivity)]
    have hsq : β * (2-β) ≤ s * Real.sqrt ((2-β)^2+s^2) :=
      mul_le_mul hlt.le hden hA.le (le_of_lt hs0)
    have h1 : (1:ℝ) ≤ 7 + 4 * |Real.log s| := by
      have := abs_nonneg (Real.log s); linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ s * Real.sqrt ((2-β)^2+s^2))
    linarith [hsq, h2]

lemma boxI_abs_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 < s) :
    |boxI β s| ≤ 48 + 5 * |Real.log s| := by
  have h1 := bxT_le (s := s) hβ0 hβ1
  have h2 := bxT_nonneg (s := s) hβ0 hβ1
  have h3 := bxB_abs_le hβ0 hβ1 hs0
  have h4 := bxb_abs_le hβ0 hβ1 hs0
  rw [boxI_eq_pieces]
  have h5 : |bxT β s - bxB β s - bxb β s| ≤ |bxT β s| + |bxB β s| + |bxb β s| := by
    have a1 := abs_sub (bxT β s - bxB β s) (bxb β s)
    have a2 := abs_sub (bxT β s) (bxB β s)
    linarith
  rw [abs_of_nonneg h2] at h5
  linarith

lemma measurable_boxI (β : ℝ) : Measurable (boxI β) := by
  have hA : Measurable
      (fun s : ℝ => (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))) := by fun_prop
  have hB : Measurable (fun s : ℝ => ((2-β)^2-β^2)/(2*((2-β)^2+s^2))) := by fun_prop
  have hC : Measurable (fun s : ℝ => ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)) := by fun_prop
  have hD : Measurable (fun s : ℝ => ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) := by fun_prop
  have hset1 : MeasurableSet {s : ℝ | (|s|:ℝ) ≤ 2 - β} :=
    measurableSet_le measurable_abs measurable_const
  have hset2 : MeasurableSet {s : ℝ | (|s|:ℝ) ≤ β} :=
    measurableSet_le measurable_abs measurable_const
  have h1a : Measurable (fun s : ℝ =>
      Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))) := by fun_prop
  have h1b : Measurable (fun s : ℝ =>
      (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) := by fun_prop
  have h2a : Measurable (fun s : ℝ =>
      Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))) := by fun_prop
  have h2b : Measurable (fun s : ℝ =>
      (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) := by fun_prop
  have hite1 : Measurable (fun s : ℝ => if (|s|:ℝ) ≤ 2-β then
      Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
      else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) :=
    Measurable.ite hset1 h1a h1b
  have hite2 : Measurable (fun s : ℝ => if (|s|:ℝ) ≤ β then
      Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
      else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) :=
    Measurable.ite hset2 h2a h2b
  have hsum : Measurable (fun s : ℝ => (if (|s|:ℝ) ≤ 2-β then
      Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
      else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
      + (if (|s|:ℝ) ≤ β then
      Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
      else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))) := hite1.add hite2
  unfold boxI
  exact ((hA.sub hsum).add hB).add hC |>.add hD

/-- Integrability of the target integrand on `[0,x]`. -/
lemma intervalIntegrable_boxI_0 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℝ}
    (hx : 0 ≤ x) : IntervalIntegrable (boxI β) volume 0 x := by
  refine IntervalIntegrable.mono_fun' (f := boxI β)
    (g := fun s : ℝ => 5*|Real.log s| + 49) ?_ ?_ ?_
  · have h : IntervalIntegrable (fun s : ℝ => |Real.log s|) volume (0:ℝ) x :=
      intervalIntegral.intervalIntegrable_log'.abs
    simpa using (h.const_mul 5).add intervalIntegrable_const
  · exact (measurable_boxI β).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le hx] at hs
    rw [Real.norm_eq_abs]
    have h1 : |boxI β s| ≤ 48 + 5*|Real.log s| := boxI_abs_le hβ0 hβ1 hs.1
    linarith

/-- Integrability of the target integrand on any interval. -/
lemma intervalIntegrable_boxI_gen {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a b : ℝ) :
    IntervalIntegrable (boxI β) volume a b :=
  intervalIntegrable_of_even (f := boxI β) (fun x => (boxI_even β x).symm)
    (fun x hx => intervalIntegrable_boxI_0 hβ0 hβ1 hx.le)

/-- Any interval with endpoints in `[-1/6, 7/6]` is an integration interval for the target
integrand. -/
lemma intervalIntegrable_boxI {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a b : ℝ) :
    IntervalIntegrable (boxI β) volume a b :=
  intervalIntegrable_boxI_gen hβ0 hβ1 a b

end pieces

section bounds

/-- Pointwise nonnegativity for `s ≥ 1/6`. -/
lemma boxI_nonneg_of_ge_sixth {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs : 1/6 ≤ s) :
    0 ≤ boxI β s := by
  have hspos : 0 < s := by linarith
  have h := boxMaj_le_target_kernel_ge_sixth hβ0 hβ1 hs
  unfold boxI
  rw [abs_of_pos hspos]
  linarith [h]

lemma integral_sixth_upper' {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ht0 : 0 ≤ t) (ht : t ≤ 1/6) : (∫ s in (0:ℝ)..t, boxI β s) ≤ 1/4 := by
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h, intervalIntegral.integral_same]; norm_num
  · exact boxWindow_sixth_upper hβ0 hβ1 h ht

lemma integral_sixth_lower' {β t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ht0 : 0 ≤ t) (ht : t ≤ 1/6) : -(1:ℝ)/3 ≤ ∫ s in (0:ℝ)..t, boxI β s := by
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h, intervalIntegral.integral_same]; norm_num
  · exact boxWindow_sixth_lower hβ0 hβ1 h ht

/-- `∫_0^{1/4} E ≥ -53/200`. -/
lemma integral_quarter_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    -(53:ℝ)/200 ≤ ∫ s in (0:ℝ)..(1/4), boxI β s := by
  have heq : (∫ s in (-(1/4):ℝ)..(1/4), boxI β s)
      = ∫ s in (-(1/4):ℝ)..(1/4),
        ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
          + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
          + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
          + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
          - (if (|s|:ℝ) ≤ 2-β then
              Real.log ((4*(2-β)^2+(|s|:ℝ)^2)/(2*(2-β)*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(4*(2-β)^2))
             else (2-β)^2/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2)))
          - (if (|s|:ℝ) ≤ β then
              Real.log ((4*β^2+(|s|:ℝ)^2)/(2*β*(|s|:ℝ)))*(1-(|s|:ℝ)^2/(2*((2-β)^2+β^2)))
             else (2-β)*β/((|s|:ℝ) * Real.sqrt ((2-β)^2+(|s|:ℝ)^2))) ) := by
    apply intervalIntegral.integral_congr
    intro x _
    unfold boxI
    ring
  have hC : -(53:ℝ)/100 ≤ ∫ s in (-(1/4):ℝ)..(1/4), boxI β s := by
    rw [heq]
    simpa only [neg_div] using boxWindow_C_lower hβ0 hβ1
  have hsym : (∫ s in (-(1/4):ℝ)..(1/4), boxI β s)
      = 2 * (∫ s in (0:ℝ)..(1/4), boxI β s) := by
    have hi0 : IntervalIntegrable (boxI β) volume (0:ℝ) (1/4) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have hi1 : IntervalIntegrable (boxI β) volume (-(1/4):ℝ) (0:ℝ) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have heven : (∫ s in (-(1/4):ℝ)..(0:ℝ), boxI β s) = (∫ s in (0:ℝ)..(1/4), boxI β s) := by
      have h := intervalIntegral.integral_comp_neg (f := boxI β) (a := (0:ℝ)) (b := (1/4:ℝ))
      simp only [neg_zero] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro x _
      exact boxI_even β x
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi0, heven]
    ring
  linarith

/-- `∫_{1/4}^{3/4} E ≥ 11/20`. -/
lemma integral_B_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (11:ℝ)/20 ≤ ∫ s in (1/4:ℝ)..(3/4), boxI β s := by
  have hcongr : (∫ s in (1/4:ℝ)..(3/4), boxI β s)
      = ∫ s in (1/4:ℝ)..(3/4), boxE β s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 3/4)] at hs
    exact boxI_eq_boxE (by linarith [hs.1]) hs.2 hβ1
  rw [hcongr]
  exact boxWindow_B_lower_11_20 hβ0 hβ1

/-- `∫_{3/4}^{5/6} E ≥ 1/10`. -/
lemma integral_seven_sixth_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (1:ℝ)/20 ≤ ∫ s in (3/4:ℝ)..(5/6), boxI β s := by
  have hi : IntervalIntegrable (boxI β) volume (3/4:ℝ) (5/6) :=
    intervalIntegrable_boxI hβ0 hβ1 _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (3/4:ℝ) ≤ 5/6)
    intervalIntegrable_const hi
    (fun s hs => boxWindow_threequarter_pointwise hβ0 hβ1 hs.1 hs.2)
  have hconst : (∫ s in (3/4:ℝ)..(5/6), (3:ℝ)/5) = 1/20 := by
    rw [intervalIntegral.integral_const]
    norm_num
  calc (1:ℝ)/20 = (∫ s in (3/4:ℝ)..(5/6), (3:ℝ)/5) := hconst.symm
    _ ≤ ∫ s in (3/4:ℝ)..(5/6), boxI β s := hmono

/-- Splitting `∫_0^{δ+1}` for `δ ∈ [0,1/6]`. -/
lemma integral_zero_one_add {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/6) :
    (7:ℝ)/200 ≤ (∫ s in (0:ℝ)..(δ+1), boxI β s) - ∫ s in (0:ℝ)..δ, boxI β s := by
  have h1 : (∫ s in (0:ℝ)..(δ+1), boxI β s)
      = (∫ s in (0:ℝ)..(1/4), boxI β s) + (∫ s in (1/4:ℝ)..(3/4), boxI β s)
        + (∫ s in (3/4:ℝ)..(δ+1), boxI β s) := by
    have hi01 : IntervalIntegrable (boxI β) volume (0:ℝ) (1/4) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have hi12 : IntervalIntegrable (boxI β) volume (1/4:ℝ) (3/4) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have hi23 : IntervalIntegrable (boxI β) volume (3/4:ℝ) (δ+1) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have e1 : (∫ s in (0:ℝ)..(1/4), boxI β s) + (∫ s in (1/4:ℝ)..(3/4), boxI β s)
        = ∫ s in (0:ℝ)..(3/4), boxI β s :=
      intervalIntegral.integral_add_adjacent_intervals hi01 hi12
    have e2 : (∫ s in (0:ℝ)..(3/4), boxI β s) + (∫ s in (3/4:ℝ)..(δ+1), boxI β s)
        = ∫ s in (0:ℝ)..(δ+1), boxI β s :=
      intervalIntegral.integral_add_adjacent_intervals (hi01.trans hi12) hi23
    linarith [e1, e2]
  have h2 : (0:ℝ) ≤ ∫ s in (3/4:ℝ)..(δ+1), boxI β s :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun s hs => boxI_nonneg_of_ge_sixth hβ0 hβ1 (by linarith [hs.1]))
  have h3 := integral_quarter_lower hβ0 hβ1
  have h4 := integral_B_lower hβ0 hβ1
  have h5 : (∫ s in (0:ℝ)..δ, boxI β s) ≤ 1/4 :=
    integral_sixth_upper' hβ0 hβ1 hδ0 hδ1
  linarith

/-- The main estimate for `δ ∈ [-1/6,0]`. -/
lemma integral_neg_side {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ0 : -1/6 ≤ δ) (hδ1 : δ ≤ 0) :
    (0:ℝ) ≤ ∫ s in δ..(δ+1), boxI β s := by
  have hsplit : (∫ s in δ..(δ+1), boxI β s)
      = (∫ s in δ..0, boxI β s) + (∫ s in (0:ℝ)..(δ+1), boxI β s) := by
    have hi1 : IntervalIntegrable (boxI β) volume δ 0 :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have hi2 : IntervalIntegrable (boxI β) volume (0:ℝ) (δ+1) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hsym : (∫ s in δ..0, boxI β s) = (∫ s in (0:ℝ)..(-δ), boxI β s) := by
    have h := intervalIntegral.integral_comp_neg (f := boxI β) (a := (0:ℝ)) (b := -δ)
    simp only [neg_zero, neg_neg] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    exact boxI_even β x
  have hlow : -(1:ℝ)/3 ≤ ∫ s in (0:ℝ)..(-δ), boxI β s :=
    integral_sixth_lower' hβ0 hβ1 (by linarith) (by linarith)
  have hle : (∫ s in (0:ℝ)..(δ+1), boxI β s) ≥ (∫ s in (0:ℝ)..(5/6), boxI β s) := by
    have hi1 : IntervalIntegrable (boxI β) volume (0:ℝ) (5/6) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have hi2 : IntervalIntegrable (boxI β) volume (5/6:ℝ) (δ+1) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have hnon : (0:ℝ) ≤ ∫ s in (5/6:ℝ)..(δ+1), boxI β s :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun s hs => boxI_nonneg_of_ge_sixth hβ0 hβ1 (by linarith [hs.1]))
    have := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    linarith
  have hfive : (67:ℝ)/200 ≤ ∫ s in (0:ℝ)..(5/6), boxI β s := by
    have h1 : (∫ s in (0:ℝ)..(5/6), boxI β s)
        = (∫ s in (0:ℝ)..(1/4), boxI β s) + (∫ s in (1/4:ℝ)..(3/4), boxI β s)
          + (∫ s in (3/4:ℝ)..(5/6), boxI β s) := by
      have hi01 : IntervalIntegrable (boxI β) volume (0:ℝ) (1/4) :=
        intervalIntegrable_boxI hβ0 hβ1 _ _
      have hi12 : IntervalIntegrable (boxI β) volume (1/4:ℝ) (3/4) :=
        intervalIntegrable_boxI hβ0 hβ1 _ _
      have hi23 : IntervalIntegrable (boxI β) volume (3/4:ℝ) (5/6) :=
        intervalIntegrable_boxI hβ0 hβ1 _ _
      have e1 : (∫ s in (0:ℝ)..(1/4), boxI β s) + (∫ s in (1/4:ℝ)..(3/4), boxI β s)
          = ∫ s in (0:ℝ)..(3/4), boxI β s :=
        intervalIntegral.integral_add_adjacent_intervals hi01 hi12
      have e2 : (∫ s in (0:ℝ)..(3/4), boxI β s) + (∫ s in (3/4:ℝ)..(5/6), boxI β s)
          = ∫ s in (0:ℝ)..(5/6), boxI β s :=
        intervalIntegral.integral_add_adjacent_intervals (hi01.trans hi12) hi23
      linarith [e1, e2]
    have h3 := integral_quarter_lower hβ0 hβ1
    have h4 := integral_B_lower hβ0 hβ1
    have h5 := integral_seven_sixth_lower hβ0 hβ1
    linarith
  have hsix := integral_sixth_lower' hβ0 hβ1 (β := β) (by linarith : (0:ℝ) ≤ -δ)
    (by linarith : -δ ≤ 1/6)
  linarith

/-- The main estimate for `δ ∈ [0,1/6]`. -/
lemma integral_pos_side {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/6) :
    (0:ℝ) ≤ ∫ s in δ..(δ+1), boxI β s := by
  have hsplit : (∫ s in δ..(δ+1), boxI β s)
      = (∫ s in (0:ℝ)..(δ+1), boxI β s) - (∫ s in (0:ℝ)..δ, boxI β s) := by
    have hi1 : IntervalIntegrable (boxI β) volume (0:ℝ) δ :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have hi2 : IntervalIntegrable (boxI β) volume δ (δ+1) :=
      intervalIntegrable_boxI hβ0 hβ1 _ _
    have := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    linarith
  have hmain := integral_zero_one_add hβ0 hβ1 hδ0 hδ1
  linarith

end bounds

/-- **The middle window inequality.**  For `0 < β < 1` and `δ ∈ [-1/6,1/6]` the window
integral of the target integrand is nonnegative. -/
theorem boxWindow_middle {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ δ : ℝ, -1/6 ≤ δ → δ ≤ 1/6 →
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
  intro δ hδ0 hδ1
  change 0 ≤ ∫ s in δ..δ+1, boxI β s
  rcases lt_or_ge δ 0 with h | h
  · exact integral_neg_side hβ0 hβ1 hδ0 (le_of_lt h)
  · exact integral_pos_side hβ0 hβ1 h hδ1

end

end Commons.Analysis.Integral
