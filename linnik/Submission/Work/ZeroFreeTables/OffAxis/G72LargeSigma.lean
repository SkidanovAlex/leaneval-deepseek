import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72TrigBound
import Submission.Work.ZeroFreeTables.OffAxis.G72RA72Bound
import Submission.Work.ZeroFreeTables.OffAxis.G72Mono

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables

/-! ## Exponential bounds

Only three numeric facts about `exp` are needed below: `e^{3/2} ≤ 4.486`, `e² ≤ 7.4` and
`e^{2s}(1-s)² ≤ 1` for `s ∈ [0,1]`. -/

/-- `exp (3/2) ≤ 4.486` (from `e³ = (e^{3/2})²` and `e < 2.72`). -/
lemma G72_exp_three_halves : Real.exp ((3:ℝ)/2) ≤ 4.486 := by
  have hsq : (Real.exp ((3:ℝ)/2))^2 = Real.exp 3 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have h3 : Real.exp (3:ℝ) ≤ 20.124 := by
    have he : Real.exp (3:ℝ) = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    rw [he]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1:ℝ)]
  have hpos : 0 < Real.exp ((3:ℝ)/2) := Real.exp_pos _
  have hx : (Real.exp ((3:ℝ)/2))^2 ≤ ((4.486:ℝ))^2 := by linarith only [hsq, h3]
  have := abs_le_of_sq_le_sq hx (by norm_num : (0:ℝ) ≤ 4.486)
  rwa [abs_of_pos hpos] at this

/-- `exp 2 ≤ 7.4`. -/
lemma G72_exp_two : Real.exp (2:ℝ) ≤ 7.4 := by
  have he : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [he]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1:ℝ)]

/-- `e^{2s}(1-s)² ≤ 1` on `[0,1]` (from `1-s ≤ e^{-s}`). -/
lemma G72_exp_mul_sq_le_one (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (2*s) * (1-s)^2 ≤ 1 := by
  have h1 : 1 - s ≤ Real.exp (-s) := by
    have := Real.add_one_le_exp (-s)
    linarith
  have h2 : 0 ≤ 1 - s := by linarith
  have h3 : (1-s)^2 ≤ (Real.exp (-s))^2 := pow_le_pow_left₀ h2 h1 2
  have h4 : (Real.exp (-s))^2 = Real.exp (-(2*s)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h5 : Real.exp (2*s) * Real.exp (-(2*s)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc Real.exp (2*s) * (1-s)^2
      ≤ Real.exp (2*s) * (Real.exp (-s))^2 :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp (2*s) * Real.exp (-(2*s)) := by rw [h4]
    _ = 1 := h5

/-! ## The three case bounds for the `s`-dependence -/

/-- Case `s ≤ 1/2`: the `s`-part is at most `4·2.72(1+σ²)/σ⁶ ≤ 1/10`. -/
lemma G72_caseA (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hr : (0:ℝ) < s^2 + σ^2 := by positivity
  have hexp : Real.exp (2*s) ≤ 2.72 := by
    have hle : 2*s ≤ 1 := by linarith
    have h := (Real.exp_le_exp).mpr hle
    linarith [Real.exp_one_lt_d9]
  have hnum : (1-s)^2 + σ^2 ≤ 1 + σ^2 := by nlinarith only [hs0, hs1]
  have hden : σ^6 ≤ (s^2+σ^2)^3 := by
    have h : σ^2 ≤ s^2 + σ^2 := by linarith only [sq_nonneg s]
    calc σ^6 = (σ^2)^3 := by ring
      _ ≤ (s^2+σ^2)^3 := pow_le_pow_left₀ (by positivity) h 3
  have h1 : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 4*2.72*(1+σ^2)/σ^6 := by
    have hr3 : (0:ℝ) < (s^2+σ^2)^3 := by positivity
    have hiff : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 4*2.72*(1+σ^2)/σ^6
        ↔ 4*Real.exp (2*s)*((1-s)^2+σ^2) * σ^6 ≤ 4*2.72*(1+σ^2) * (s^2+σ^2)^3 :=
      div_le_div_iff₀ hr3 hσ6
    rw [hiff]
    have ha : 4*Real.exp (2*s)*((1-s)^2+σ^2) ≤ 4*2.72*(1+σ^2) := by
      have h4 : 4*Real.exp (2*s) ≤ 4*2.72 := by linarith only [hexp]
      exact mul_le_mul h4 hnum (by positivity) (by norm_num)
    calc 4*Real.exp (2*s)*((1-s)^2+σ^2)*σ^6
        ≤ 4*2.72*(1+σ^2)*σ^6 := mul_le_mul_of_nonneg_right ha (by positivity)
      _ ≤ 4*2.72*(1+σ^2)*(s^2+σ^2)^3 := mul_le_mul_of_nonneg_left hden (by positivity)
  have h2 : 4*2.72*(1+σ^2)/σ^6 ≤ 1/10 := by
    rw [div_le_iff₀ hσ6]
    have hA : 10.88*(1+σ^2) ≤ 11.72*σ^2 := by linarith only [hσ2]
    have hB : (11.72:ℝ) ≤ (1/10)*σ^4 := by linarith only [hσ4]
    nlinarith only [hA, hB, sq_nonneg σ, hσ2]
  have hmain : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := le_trans h1 h2
  rw [show (-16*s/(15*(s^2+σ^2))) = -(16*s/(15*(s^2+σ^2))) by ring]
  have hdrop : -(16*s/(15*(s^2+σ^2))) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3
      ≤ 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 := by
    have hh : (0:ℝ) ≤ 16*s/(15*(s^2+σ^2)) := by positivity
    linarith
  linarith only [hdrop, hmain]

/-- Case `1/2 ≤ s ≤ 3/4`. -/
lemma G72_caseB (s σ : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 3/4) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hr : (0:ℝ) < s^2 + σ^2 := by positivity
  have hs0le : 0 ≤ s := by linarith
  have hs1le : s ≤ 1 := by linarith
  have hexp : Real.exp (2*s) ≤ 4.486 := by
    have hle : 2*s ≤ 3/2 := by linarith
    calc Real.exp (2*s) ≤ Real.exp ((3:ℝ)/2) := (Real.exp_le_exp).mpr hle
      _ ≤ 4.486 := G72_exp_three_halves
  have hsplit : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3
      = 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 + 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 := by
    ring
  rw [hsplit]
  rw [show (-16*s/(15*(s^2+σ^2))) = -(16*s/(15*(s^2+σ^2))) by ring]
  have hA : -(16*s/(15*(s^2+σ^2))) ≤ -(8/(15*(1+σ^2))) := by
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : s^2+σ^2 ≤ 2*s*(1+σ^2) := by nlinarith only [hs0, hs1, hσ2]
    linarith only [h3]
  have hB : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6 := by
    have hm : Real.exp (2*s)*(1-s)^2 ≤ 1 := G72_exp_mul_sq_le_one s hs0le hs1le
    have hden : σ^6 ≤ (s^2+σ^2)^3 := by
      have h : σ^2 ≤ s^2 + σ^2 := by linarith only [sq_nonneg s]
      calc σ^6 = (σ^2)^3 := by ring
        _ ≤ (s^2+σ^2)^3 := pow_le_pow_left₀ (by positivity) h 3
    have hr3 : (0:ℝ) < (s^2+σ^2)^3 := by positivity
    have hiff : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6
        ↔ 4*Real.exp (2*s)*(1-s)^2 * σ^6 ≤ 4 * (s^2+σ^2)^3 :=
      div_le_div_iff₀ hr3 hσ6
    rw [hiff]
    linarith only [mul_le_mul_of_nonneg_right hm hσ6.le, hden]
  have hC : 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 ≤ 17.944/(σ^2*(σ^2+3/4)) := by
    have hr1 : (0:ℝ) < 1/4 + σ^2 := by positivity
    have h1 : 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 ≤ 4*4.486*σ^2/(1/4+σ^2)^3 := by
      have hr3 : (0:ℝ) < (s^2+σ^2)^3 := by positivity
      have hr1c : (0:ℝ) < (1/4+σ^2)^3 := by positivity
      have hiff : 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 ≤ 4*4.486*σ^2/(1/4+σ^2)^3
          ↔ 4*Real.exp (2*s)*σ^2 * (1/4+σ^2)^3 ≤ 4*4.486*σ^2 * (s^2+σ^2)^3 :=
        div_le_div_iff₀ hr3 hr1c
      rw [hiff]
      have hden : (1/4+σ^2)^3 ≤ (s^2+σ^2)^3 := by
        have h : 1/4 + σ^2 ≤ s^2 + σ^2 := by nlinarith only [hs0]
        exact pow_le_pow_left₀ (by positivity) h 3
      have ha : 4*Real.exp (2*s)*σ^2 ≤ 4*4.486*σ^2 := by
        have h4 : 4*Real.exp (2*s) ≤ 4*4.486 := by linarith only [hexp]
        exact mul_le_mul h4 le_rfl (by positivity) (by norm_num)
      calc 4*Real.exp (2*s)*σ^2*(1/4+σ^2)^3
          ≤ 4*4.486*σ^2*(1/4+σ^2)^3 := mul_le_mul_of_nonneg_right ha (by positivity)
        _ ≤ 4*4.486*σ^2*(s^2+σ^2)^3 := mul_le_mul_of_nonneg_left hden (by positivity)
    have h2 : 4*4.486*σ^2/(1/4+σ^2)^3 ≤ 17.944/(σ^2*(σ^2+3/4)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith only [sq_nonneg σ]
    linarith
  have hb1 : 17.944/(σ^2*(σ^2+3/4)) ≤ (17.944/(324/25+3/4))/σ^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hσ2, sq_nonneg σ]
  have hb2 : 4/σ^6 ≤ (4/(324/25)^2)/σ^2 := by
    rw [div_le_div_iff₀ hσ6 (by positivity)]
    nlinarith only [hσ4, sq_nonneg σ, hσ2]
  have hb3 : -(8/(15*(1+σ^2))) ≤ -(((8/15)*(324/349))/σ^2) := by
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [hσ2]
  have hinv : 1/σ^2 ≤ 25/324 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hσ2]
  have hcomb : (17.944/(324/25+3/4))/σ^2 + (4/(324/25)^2)/σ^2 + (-(((8/15)*(324/349))/σ^2))
      = ((17.944:ℝ)/(324/25+3/4) + 4/(324/25)^2 - (8/15)*(324/349))/σ^2 := by ring
  have hfin : -(8/(15*(1+σ^2))) + (4/σ^6 + 17.944/(σ^2*(σ^2+3/4))) ≤ 1/10 := by
    have hK : ((17.944:ℝ)/(324/25+3/4) + 4/(324/25)^2 - (8/15)*(324/349)) ≤ (324/25)/10 := by
      norm_num
    have hfin2 : ((17.944:ℝ)/(324/25+3/4) + 4/(324/25)^2 - (8/15)*(324/349))/σ^2 ≤ 1/10 := by
      calc ((17.944:ℝ)/(324/25+3/4) + 4/(324/25)^2 - (8/15)*(324/349))/σ^2
          = ((17.944:ℝ)/(324/25+3/4) + 4/(324/25)^2 - (8/15)*(324/349)) * (1/σ^2) := by ring
        _ ≤ ((324/25)/10) * (25/324) := mul_le_mul hK hinv (by positivity) (by norm_num)
        _ = 1/10 := by norm_num
    linarith only [hb1, hb2, hb3, hcomb, hfin2]
  have hsum1 : -(16*s/(15*(s^2+σ^2)))
        + (4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 + 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3)
      ≤ -(8/(15*(1+σ^2))) + (4/σ^6 + 17.944/(σ^2*(σ^2+3/4))) :=
    add_le_add hA (add_le_add hB hC)
  linarith only [hsum1, hfin]

/-- Case `3/4 ≤ s ≤ 1`. -/
lemma G72_caseC (s σ : ℝ) (hs0 : 3/4 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hr : (0:ℝ) < s^2 + σ^2 := by positivity
  have hs0le : 0 ≤ s := by linarith
  have hsplit : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3
      = 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 + 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 := by
    ring
  rw [hsplit]
  rw [show (-16*s/(15*(s^2+σ^2))) = -(16*s/(15*(s^2+σ^2))) by ring]
  have hA : -(16*s/(15*(s^2+σ^2))) ≤ -(12/(15*(1+σ^2))) := by
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 3*(s^2+σ^2) ≤ 4*s*(1+σ^2) := by nlinarith only [hs0, hs1, hσ2]
    linarith only [h3]
  have hB : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6 := by
    have hm : Real.exp (2*s)*(1-s)^2 ≤ 1 := G72_exp_mul_sq_le_one s hs0le hs1
    have hden : σ^6 ≤ (s^2+σ^2)^3 := by
      have h : σ^2 ≤ s^2 + σ^2 := by linarith only [sq_nonneg s]
      calc σ^6 = (σ^2)^3 := by ring
        _ ≤ (s^2+σ^2)^3 := pow_le_pow_left₀ (by positivity) h 3
    have hr3 : (0:ℝ) < (s^2+σ^2)^3 := by positivity
    have hiff : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6
        ↔ 4*Real.exp (2*s)*(1-s)^2 * σ^6 ≤ 4 * (s^2+σ^2)^3 :=
      div_le_div_iff₀ hr3 hσ6
    rw [hiff]
    linarith only [mul_le_mul_of_nonneg_right hm hσ6.le, hden]
  have hC : 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 ≤ 29.6/(σ^4+3*σ^2) := by
    have hmono : 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 ≤ 4*Real.exp (2:ℝ)*σ^2/(1+σ^2)^3 :=
      G72Mono s σ hs0 hs1 hσ
    have h2 : 4*Real.exp (2:ℝ)*σ^2/(1+σ^2)^3 ≤ 29.6/(σ^4+3*σ^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have he2 : 4*Real.exp (2:ℝ) ≤ 29.6 := by
        have h := G72_exp_two
        linarith
      nlinarith [he2, sq_nonneg σ]
    linarith
  have hb1 : 29.6/(σ^4+3*σ^2) ≤ (29.6/(324/25+3))/σ^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hσ2, sq_nonneg σ]
  have hb2 : 4/σ^6 ≤ (4/(324/25)^2)/σ^2 := by
    rw [div_le_div_iff₀ hσ6 (by positivity)]
    nlinarith only [hσ4, sq_nonneg σ, hσ2]
  have hb3 : -(12/(15*(1+σ^2))) ≤ -(((4/5)*(324/349))/σ^2) := by
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [hσ2]
  have hinv : 1/σ^2 ≤ 25/324 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hσ2]
  have hcomb : (29.6/(324/25+3))/σ^2 + (4/(324/25)^2)/σ^2 + (-(((4/5)*(324/349))/σ^2))
      = ((29.6:ℝ)/(324/25+3) + 4/(324/25)^2 - (4/5)*(324/349))/σ^2 := by ring
  have hfin : -(12/(15*(1+σ^2))) + (4/σ^6 + 29.6/(σ^4+3*σ^2)) ≤ 1/10 := by
    have hK : ((29.6:ℝ)/(324/25+3) + 4/(324/25)^2 - (4/5)*(324/349)) ≤ (324/25)/10 := by
      norm_num
    have hfin2 : ((29.6:ℝ)/(324/25+3) + 4/(324/25)^2 - (4/5)*(324/349))/σ^2 ≤ 1/10 := by
      calc ((29.6:ℝ)/(324/25+3) + 4/(324/25)^2 - (4/5)*(324/349))/σ^2
          = ((29.6:ℝ)/(324/25+3) + 4/(324/25)^2 - (4/5)*(324/349)) * (1/σ^2) := by ring
        _ ≤ ((324/25)/10) * (25/324) := mul_le_mul hK hinv (by positivity) (by norm_num)
        _ = 1/10 := by norm_num
    linarith only [hb1, hb2, hb3, hcomb, hfin2]
  have hsum1 : -(16*s/(15*(s^2+σ^2)))
        + (4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 + 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3)
      ≤ -(12/(15*(1+σ^2))) + (4/σ^6 + 29.6/(σ^4+3*σ^2)) :=
    add_le_add hA (add_le_add hB hC)
  linarith only [hsum1, hfin]

/-- **The `s`-dependent part is at most `1/10`.** -/
lemma G72_LHS_le (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  rcases le_or_gt s (1/2) with h | h
  · exact G72_caseA s σ hs0 h hσ
  rcases le_or_gt s (3/4) with h2 | h2
  · exact G72_caseB s σ (le_of_lt h) h2 hσ
  · exact G72_caseC s σ (le_of_lt h2) hs1 hσ

/-- The `s`-independent tail: `4/σ⁴ - 12/σ⁶ + 16/σ⁵ ≤ 11/210`. -/
lemma G72_tail (σ : ℝ) (hσ : (36:ℝ)/10 ≤ σ) : 4/σ^4 - 12/σ^6 + 16/σ^5 ≤ 11/210 := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hmain : 4*σ^2 + 16*σ - 12 ≤ (11/210)*σ^6 := by
    have h16 : 16*σ ≤ (40/9)*σ^2 := by nlinarith only [hσ, hσ0]
    have h4 : (76/9 : ℝ) ≤ (11/210)*σ^4 := by linarith only [hσ4]
    nlinarith only [h16, h4, sq_nonneg σ, hσ0, hσ2, hσ4]
  have h2 : (4*σ^2 - 12 + 16*σ)/σ^6 ≤ 11/210 := by
    rw [div_le_iff₀ hσ6]
    linarith only [hmain]
  have h3 : 4/σ^4 - 12/σ^6 + 16/σ^5 = (4*σ^2 - 12 + 16*σ)/σ^6 := by
    field_simp
  linarith only [h2, h3]

/-! ## The main theorem -/

theorem G72LargeSigma (hcf : ∀ w : ℂ, w ≠ 0 → Work.ZeroFreeTables.G72 w
      = Work.ZeroFreeTables.OffAxis.A72 w + Complex.exp (-2*w) * Work.ZeroFreeTables.OffAxis.B72 w)
    (him : ∀ t : ℝ, 0 ≤ (Work.ZeroFreeTables.G72 ((t : ℂ) * Complex.I)).re)
    (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    Work.ZeroFreeTables.OffAxis.Isub s σ ≤ 16/105 := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hρ : s^2 + σ^2 ≠ 0 := by positivity
  have hlhs : -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 :=
    G72_LHS_le s σ hs0 hs1 hσ
  have hra : RA72 s σ ≤ -16*s/(15*(s^2+σ^2)) + 4/σ^4 + 4/σ^6 :=
    G72RA72Bound s σ hs0 hs1 hσ
  have htail : 4/σ^4 - 12/σ^6 + 16/σ^5 ≤ 11/210 := G72_tail σ hσ
  have htrig : Real.cos (2*σ)*(Real.exp (2*s)*RB72 s σ - 8*(σ^2-1)/σ^6)
      + Real.sin (2*σ)*(Real.exp (2*s)*RI72 s σ + 16/σ^5)
      ≤ 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 + 8*(σ^2-1)/σ^6 + 16/σ^5 := by
    have hsplit : Real.cos (2*σ)*(Real.exp (2*s)*RB72 s σ - 8*(σ^2-1)/σ^6)
        + Real.sin (2*σ)*(Real.exp (2*s)*RI72 s σ + 16/σ^5)
        = Real.exp (2*s)*(Real.cos (2*σ)*RB72 s σ + Real.sin (2*σ)*RI72 s σ)
          - (8*(σ^2-1)/σ^6)*Real.cos (2*σ) + (16/σ^5)*Real.sin (2*σ) := by ring
    rw [hsplit]
    have hmain : Real.exp (2*s)*(Real.cos (2*σ)*RB72 s σ + Real.sin (2*σ)*RI72 s σ)
        ≤ 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 := by
      have hb := G72TrigBound s σ
      have h1 : Real.cos (2*σ)*RB72 s σ + Real.sin (2*σ)*RI72 s σ
          ≤ 4*((1-s)^2+σ^2)/(s^2+σ^2)^3 := le_trans (le_abs_self _) hb
      calc Real.exp (2*s)*(Real.cos (2*σ)*RB72 s σ + Real.sin (2*σ)*RI72 s σ)
          ≤ Real.exp (2*s)*(4*((1-s)^2+σ^2)/(s^2+σ^2)^3) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 := by ring
    have ha : (0:ℝ) ≤ 8*(σ^2-1)/σ^6 := by
      have h1 : (1:ℝ) ≤ σ^2 := by nlinarith only [hσ]
      positivity
    have hc : -(8*(σ^2-1)/σ^6)*Real.cos (2*σ) ≤ 8*(σ^2-1)/σ^6 := by
      have h1 := Real.neg_one_le_cos (2*σ)
      nlinarith only [ha, h1]
    have hs : (16/σ^5)*Real.sin (2*σ) ≤ 16/σ^5 := by
      have h1 := Real.sin_le_one (2*σ)
      have h2 : (0:ℝ) ≤ 16/σ^5 := by positivity
      nlinarith only [h1, h2]
    linarith
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have hkey : (-16*s/(15*(s^2+σ^2)) + 4/σ^4 + 4/σ^6) - 2*(4/σ^4 + 4/σ^6)
      + (4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 + 8*(σ^2-1)/σ^6 + 16/σ^5)
      = (-16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3)
        + (4/σ^4 - 12/σ^6 + 16/σ^5) := by
    field_simp
    ring
  rw [Isub_eq_closed hσne hρ]
  have step1 : ((RA72 s σ - 2*(4/σ^4 + 4/σ^6))
        + Real.cos (2*σ)*(Real.exp (2*s)*RB72 s σ - 8*(σ^2-1)/σ^6))
        + Real.sin (2*σ)*(Real.exp (2*s)*RI72 s σ + 16/σ^5)
      ≤ ((-16*s/(15*(s^2+σ^2)) + 4/σ^4 + 4/σ^6) - 2*(4/σ^4 + 4/σ^6))
        + (4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 + 8*(σ^2-1)/σ^6 + 16/σ^5) := by
    linarith only [hra, htrig]
  linarith only [step1, hkey, hlhs, htail]

end Work.ZeroFreeTables.OffAxis
