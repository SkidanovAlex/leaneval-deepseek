import Mathlib
import Submission.Commons.Analysis.Integral.boxWin_small_beta

namespace Commons.Analysis.Integral

open BoxWinSB

/-!
# `TT β 0 - TT β (1/6) ≤ 7/50` for `0 < β ≤ 1/6`

`TT` is a rational function of `β` and `t`, so the difference `TT β 0 - TT β (1/6)` is a
rational function of `β` alone.  We split it into its five constituent differences and
bound each separately on the window `(0, 1/6]`.
-/

private lemma TT_zero_eq (β : ℝ) : TT β 0 =
    (13/5)*((3/2-β)/((3/2-β)^2)) + (13/5)*((1+β)/((1+β)^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2)) + ((2-β)^2-β^2)^2/(8*((2-β)^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2)^3) := by
  simp only [TT] <;> ring_nf

private lemma TT_sixth_eq (β : ℝ) : TT β (1/6) =
    (13/5)*((3/2-β)/((3/2-β)^2+(1/6)^2)) + (13/5)*((1+β)/((1+β)^2+(1/6)^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2+(1/6)^2)) + ((2-β)^2-β^2)^2/(8*((2-β)^2+(1/6)^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+(1/6)^2)^3) := by
  simp only [TT] <;> ring_nf

private lemma diff1_le {β : ℝ} (hβ6 : β ≤ 1/6) :
    (13/5)*((3/2-β)/((3/2-β)^2)) - (13/5)*((3/2-β)/((3/2-β)^2+(1/6)^2)) ≤ 39/1280 := by
  have hA : (0:ℝ) < 3/2 - β := by linarith
  have ha : (4:ℝ)/3 ≤ 3/2 - β := by linarith
  have hD : (0:ℝ) < (3/2-β)*((3/2-β)^2+(1/6)^2) := by positivity
  have hkey : (13/5)*((3/2-β)/((3/2-β)^2)) - (13/5)*((3/2-β)/((3/2-β)^2+(1/6)^2))
      = (13/180)/((3/2-β)*((3/2-β)^2+(1/6)^2)) := by
    field_simp <;> ring
  rw [hkey, div_le_iff₀ hD]
  have hden : (64:ℝ)/27 ≤ (3/2-β)*((3/2-β)^2+(1/6)^2) := by
    have h3 : ((4:ℝ)/3)^3 ≤ (3/2-β)^3 := pow_le_pow_left₀ (by norm_num) ha 3
    nlinarith [h3, hA, sq_nonneg (3/2-β)]
  nlinarith [hden]

private lemma diff2_le {β : ℝ} (hβ0 : 0 < β) :
    (13/5)*((1+β)/((1+β)^2)) - (13/5)*((1+β)/((1+β)^2+(1/6)^2)) ≤ 13/185 := by
  have hB : (0:ℝ) < 1 + β := by linarith
  have hb1 : (1:ℝ) ≤ 1 + β := by linarith
  have hD : (0:ℝ) < (1+β)*((1+β)^2+(1/6)^2) := by positivity
  have hkey : (13/5)*((1+β)/((1+β)^2)) - (13/5)*((1+β)/((1+β)^2+(1/6)^2))
      = (13/180)/((1+β)*((1+β)^2+(1/6)^2)) := by
    field_simp <;> ring
  rw [hkey, div_le_iff₀ hD]
  have hden : (37:ℝ)/36 ≤ (1+β)*((1+β)^2+(1/6)^2) := by
    nlinarith [hb1, hB, sq_nonneg (1+β)]
  nlinarith [hden]

private lemma diff3_le {β : ℝ} (hβ0 : 0 < β) (hβ6 : β ≤ 1/6) :
    ((2-β)^2-β^2)/(2*((2-β)^2)) - ((2-β)^2-β^2)/(2*((2-β)^2+(1/6)^2)) ≤ 36/7381 := by
  have hstep : ((2-β)^2-β^2)/(2*((2-β)^2)) - ((2-β)^2-β^2)/(2*((2-β)^2+(1/6)^2))
      = ((2-β)^2-β^2)/2 * ((1/((2-β)^2)) - (1/((2-β)^2+(1/6)^2))) := by
    field_simp <;> ring
  rw [hstep]
  have hb : (0:ℝ) < 2 - β := by linarith
  have hP : (0:ℝ) < (2-β)^2 := by positivity
  have hQ : (0:ℝ) < (2-β)^2+(1/6)^2 := by positivity
  have hkey : ((2-β)^2-β^2)/2 * ((1/((2-β)^2)) - (1/((2-β)^2+(1/6)^2)))
      = ((2-β)^2-β^2)/(72*((2-β)^2)*((2-β)^2+(1/6)^2)) := by
    field_simp <;> ring
  rw [hkey]
  have h1 : (121:ℝ)/36 ≤ (2-β)^2 := by nlinarith [hβ6, sq_nonneg (2-β)]
  have h2 : (122:ℝ)/36 ≤ (2-β)^2+(1/6)^2 := by linarith [h1]
  have hPQ : (7381:ℝ)/648 ≤ ((2-β)^2)*((2-β)^2+(1/6)^2) := by
    have h := mul_le_mul h1 h2 (by norm_num) (by positivity)
    have he : (121:ℝ)/36 * (122/36) = 7381/648 := by norm_num
    rwa [he] at h
  have hD4 : (2-β)^2-β^2 ≤ 4 := by nlinarith [hβ0]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hPQ, hD4]

private lemma diff4_le {β : ℝ} (hβ0 : 0 < β) (hβ6 : β ≤ 1/6) :
    ((2-β)^2-β^2)^2/(8*((2-β)^2)^2) - ((2-β)^2-β^2)^2/(8*((2-β)^2+(1/6)^2)^2) ≤ 1/250 := by
  have hstep : ((2-β)^2-β^2)^2/(8*((2-β)^2)^2) - ((2-β)^2-β^2)^2/(8*((2-β)^2+(1/6)^2)^2)
      = ((2-β)^2-β^2)^2/8 * ((1/(((2-β)^2)^2)) - (1/(((2-β)^2+(1/6)^2)^2))) := by
    field_simp <;> ring
  rw [hstep]
  have hb : (0:ℝ) < 2 - β := by linarith
  have hP : (0:ℝ) < (2-β)^2 := by positivity
  have hQ : (0:ℝ) < (2-β)^2+(1/6)^2 := by positivity
  have hkey : ((2-β)^2-β^2)^2/8 * ((1/(((2-β)^2)^2)) - (1/(((2-β)^2+(1/6)^2)^2)))
      = ((2-β)^2-β^2)^2*(((2-β)^2)+((2-β)^2+(1/6)^2))/(288*((2-β)^2)^2*((2-β)^2+(1/6)^2)^2) := by
    field_simp <;> ring
  rw [hkey]
  have hD2 : ((2-β)^2-β^2)^2 ≤ 16 := by
    have h : (2-β)^2-β^2 ≤ 4 := by nlinarith [hβ0]
    have h0 : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith [hβ0, hβ6]
    nlinarith [h, h0]
  have hPS : (2-β)^2+((2-β)^2+(1/6)^2) ≤ 289/36 := by
    have h1 : (2-β)^2 ≤ 4 := by nlinarith [hβ0, sq_nonneg (2-β)]
    nlinarith [h1]
  have h1 : (121:ℝ)/36 ≤ (2-β)^2 := by nlinarith [hβ6, sq_nonneg (2-β)]
  have h2 : (122:ℝ)/36 ≤ (2-β)^2+(1/6)^2 := by linarith [h1]
  have hm : (7381:ℝ)/648 ≤ ((2-β)^2)*((2-β)^2+(1/6)^2) := by
    have h := mul_le_mul h1 h2 (by norm_num) (by positivity)
    have he : (121:ℝ)/36 * (122/36) = 7381/648 := by norm_num
    rwa [he] at h
  have hPQ2 : ((7381:ℝ)/648)^2 ≤ (((2-β)^2)*((2-β)^2+(1/6)^2))^2 :=
    pow_le_pow_left₀ (by norm_num) hm 2
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hD2, hPS, hPQ2]

private lemma diff5_le {β : ℝ} (hβ0 : 0 < β) (hβ6 : β ≤ 1/6) :
    ((2-β)^2-β^2)^3/(16*((2-β)^2)^3) - ((2-β)^2-β^2)^3/(16*((2-β)^2+(1/6)^2)^3) ≤ 1/250 := by
  have hstep : ((2-β)^2-β^2)^3/(16*((2-β)^2)^3) - ((2-β)^2-β^2)^3/(16*((2-β)^2+(1/6)^2)^3)
      = ((2-β)^2-β^2)^3/16 * ((1/(((2-β)^2)^3)) - (1/(((2-β)^2+(1/6)^2)^3))) := by
    field_simp <;> ring
  rw [hstep]
  have hb : (0:ℝ) < 2 - β := by linarith
  have hP : (0:ℝ) < (2-β)^2 := by positivity
  have hQ : (0:ℝ) < (2-β)^2+(1/6)^2 := by positivity
  have hkey : ((2-β)^2-β^2)^3/16 * ((1/(((2-β)^2)^3)) - (1/(((2-β)^2+(1/6)^2)^3)))
      = ((2-β)^2-β^2)^3*((((2-β)^2)^2)+((2-β)^2)*((2-β)^2+(1/6)^2)+(((2-β)^2+(1/6)^2)^2))
        /(576*(((2-β)^2)^3)*(((2-β)^2+(1/6)^2)^3)) := by
    field_simp <;> ring
  rw [hkey]
  have hD3 : ((2-β)^2-β^2)^3 ≤ 64 := by
    have h : (2-β)^2-β^2 ≤ 4 := by nlinarith [hβ0]
    have h0 : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith [hβ0, hβ6]
    nlinarith [h, h0]
  have hQle : (2-β)^2 ≤ (2-β)^2+(1/6)^2 := by linarith
  have hnum : (((2-β)^2)^2)+((2-β)^2)*((2-β)^2+(1/6)^2)+(((2-β)^2+(1/6)^2)^2)
      ≤ 3*(((2-β)^2+(1/6)^2)^2) := by nlinarith [hQle, hP, sq_nonneg ((2-β)^2+(1/6)^2)]
  have h1 : (121:ℝ)/36 ≤ (2-β)^2 := by nlinarith [hβ6, sq_nonneg (2-β)]
  have h2 : (122:ℝ)/36 ≤ (2-β)^2+(1/6)^2 := by linarith [h1]
  have hP3Q : ((121:ℝ)/36)^3 * (122/36) ≤ (((2-β)^2)^3)*((2-β)^2+(1/6)^2) := by
    have h13 : ((121:ℝ)/36)^3 ≤ ((2-β)^2)^3 := pow_le_pow_left₀ (by norm_num) h1 3
    exact mul_le_mul h13 h2 (by norm_num) (by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hD3, hnum, hP3Q, hQ]

private lemma bound_sum : (39:ℝ)/1280 + 13/185 + 36/7381 + 1/250 + 1/250 ≤ 7/50 := by
  norm_num

theorem TT_zero_sub_sixth_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ6 : β ≤ 1/6) :
    Commons.Analysis.Integral.BoxWinSB.TT β 0 - Commons.Analysis.Integral.BoxWinSB.TT β (1/6) ≤ 7/50 := by
  rw [TT_zero_eq β, TT_sixth_eq β]
  have h1 := diff1_le hβ6
  have h2 := diff2_le hβ0
  have h3 := diff3_le hβ0 hβ6
  have h4 := diff4_le hβ0 hβ6
  have h5 := diff5_le hβ0 hβ6
  linarith [h1, h2, h3, h4, h5, bound_sum]

end Commons.Analysis.Integral
