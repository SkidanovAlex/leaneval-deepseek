import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.OffAxis.G72Defs
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72SmallS
import Submission.Work.ZeroFreeTables.OffAxis.G72B2Cells
import Submission.Work.ZeroFreeTables.OffAxis.G72GridMain

noncomputable section

namespace Work.OffAxis

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-!
# `TF72Num103a`: Heath-Brown's (10.8) at `lam = 6/7`, in the `tf72Fc` normalisation

We prove `Re F_{6/7}(-a+im) - 2 Re F_{6/7}(im) ≤ 16/105` for `0 ≤ a ≤ 6/7` and all real `m`.

Via `tf72Fc_scale` (`F_lam z = F_1 (z/lam)`) and `tf72Fc 1 = G72` this is the statement
`Isub s σ ≤ 16/105` (`s = 7a/6 ∈ [0,1]`, `σ = 7m/6`) for `G72 w = ∫₀² e^{-wy} g72 y dy`,
`g72 y = (1/30)(2-y)³(4+6y+y²)`.  That statement is proved in two regimes:

* `σ ≤ 18/5`: `G72SmallS` (`s ≤ 7/25`), the `F`-method cells `B2cell_1 … B2cell_8` (`σ ≤ 51/20`,
  resp. `σ ≤ 18/5` for `s ≥ 7/10`) and the grid `grid_main` (`51/20 ≤ σ ≤ 18/5`);
* `σ ≥ 18/5`: the closed form `Isub = RA72 + e^{2s}(cos 2σ · RB72 + sin 2σ · RI72) - 2 Re G72(iσ)`
  (`Isub_eq_closed`, `G72_re_closed_zero`), the rational bound `RA72Bound72`, the modulus bound
  `TrigBound72` and the two elementary estimates `LHSle72`, `tail72`.

The five lemmas `RA72Bound72`, `TrigBound72`, `Mono72`, `LHSle72` (with its case lemmas
`LHSleA/B/C`) and `tail72` are scale-free and self-contained: they are exactly the missing
ingredients of the `sigma >= 18/5` branch of `Work.ZeroFreeTables.OffAxis.G72_ten_eight`
(the `sorry`-free statement equivalent to `TF72Num103a`); the grid/cell modules
(`G72SmallS`, `G72B2Cells`, `G72GridMain`) supply the complementary compact region.
-/

/-! ## Elementary exponential estimates -/

/-- `exp 2 ≤ 7.4`. -/
lemma exp_two_le : Real.exp (2:ℝ) ≤ 7.4 := by
  have h1 : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [h1]
  nlinarith only [Real.exp_one_lt_d9, Real.exp_pos (1:ℝ)]

/-- `exp (3/2) ≤ 4.486`. -/
lemma exp_three_halves_le : Real.exp ((3:ℝ)/2) ≤ 4.486 := by
  have hsq : (Real.exp ((3:ℝ)/2))^2 = Real.exp 3 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h3 : Real.exp (3:ℝ) ≤ 20.124 := by
    have he : Real.exp (3:ℝ) = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    rw [he]
    nlinarith only [Real.exp_one_lt_d9, Real.exp_pos (1:ℝ)]
  have hpos : 0 < Real.exp ((3:ℝ)/2) := Real.exp_pos _
  have hx : (Real.exp ((3:ℝ)/2))^2 ≤ ((4.486:ℝ))^2 := by linarith only [hsq, h3]
  have := abs_le_of_sq_le_sq hx (by norm_num : (0:ℝ) ≤ 4.486)
  rwa [abs_of_pos hpos] at this

/-- `e^{2s}(1-s)^2 ≤ 1` on `[0,1]` (from `1-s ≤ e^{-s}`). -/
lemma exp_mul_sq_le_one (s : ℝ) (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (2*s) * (1-s)^2 ≤ 1 := by
  have h1 : 1 - s ≤ Real.exp (-s) := by
    have := Real.add_one_le_exp (-s)
    linarith only [this]
  have h2 : 0 ≤ 1 - s := by linarith only [hs1]
  have h3 : (1-s)^2 ≤ (Real.exp (-s))^2 := pow_le_pow_left₀ h2 h1 2
  have h4 : (Real.exp (-s))^2 = Real.exp (-(2*s)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (2*s) * Real.exp (-(2*s)) = 1 := by
    rw [← Real.exp_add]; norm_num
  calc Real.exp (2*s) * (1-s)^2
      ≤ Real.exp (2*s) * (Real.exp (-s))^2 :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp (2*s) * Real.exp (-(2*s)) := by rw [h4]
    _ = 1 := h5

/-- **Monotonicity in `s` of `4 e^{2s}σ²/(s²+σ²)³` at `σ ≥ 18/5`** (used in case `s ≥ 3/4`
of `LHSle72`). -/
lemma Mono72 (s σ : ℝ) (hs : (3:ℝ)/4 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    4 * Real.exp (2*s) * σ^2 / (s^2 + σ^2)^3 ≤ 4 * Real.exp (2:ℝ) * σ^2 / (1 + σ^2)^3 := by
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hrn : 0 < s^2 + σ^2 := by positivity
  have hr1 : 0 < 1 + σ^2 := by positivity
  have hd1 : (0:ℝ) < (s^2+σ^2)^3 := by positivity
  have hd2 : (0:ℝ) < (1+σ^2)^3 := by positivity
  have hu : (1+σ^2)/(s^2+σ^2) = 1 + (1-s^2)/(s^2+σ^2) := by field_simp; ring
  have hwle : (1-s^2)/(s^2+σ^2) ≤ (2/3)*(1-s) := by
    rw [div_le_iff₀ hrn]
    have h2 : 3*(1+s) ≤ 2*(s^2+σ^2) := by nlinarith only [hs1, hσ]
    nlinarith only [hs1, h2]
  have hle1 : 1 + (1-s^2)/(s^2+σ^2) ≤ Real.exp ((2/3)*(1-s)) := by
    have h := Real.add_one_le_exp ((1-s^2)/(s^2+σ^2))
    have h2 := Real.exp_le_exp.mpr hwle
    linarith only [h, h2]
  have hu3 : ((1+σ^2)/(s^2+σ^2))^3 ≤ Real.exp (2:ℝ)/Real.exp (2*s) := by
    rw [hu]
    calc (1 + (1-s^2)/(s^2+σ^2))^3
        ≤ (Real.exp ((2/3)*(1-s)))^3 := pow_le_pow_left₀ (by rw [← hu]; positivity) hle1 3
      _ = Real.exp (((3:ℕ):ℝ)*((2/3)*(1-s))) := (Real.exp_nat_mul ((2/3)*(1-s)) 3).symm
      _ = Real.exp (2 - 2*s) := by
            rw [show ((3:ℕ):ℝ)*((2/3)*(1-s)) = 2 - 2*s by push_cast; ring]
      _ = Real.exp (2:ℝ)/Real.exp (2*s) := Real.exp_sub 2 (2*s)
  have hcube : (1+σ^2)^3/(s^2+σ^2)^3 ≤ Real.exp (2:ℝ)/Real.exp (2*s) := by
    simpa [div_pow] using hu3
  have h4 : (1+σ^2)^3 ≤ (Real.exp (2:ℝ)/Real.exp (2*s)) * (s^2+σ^2)^3 :=
    (div_le_iff₀ hd1).mp hcube
  have h5 : Real.exp (2*s) * (Real.exp (2:ℝ)/Real.exp (2*s)) = Real.exp (2:ℝ) := by
    field_simp
  have hkey : Real.exp (2*s) * (1+σ^2)^3 ≤ Real.exp (2:ℝ) * (s^2+σ^2)^3 := by
    have hmult := mul_le_mul_of_nonneg_left h4 (Real.exp_pos (2*s)).le
    have heq : Real.exp (2*s) * ((Real.exp (2:ℝ)/Real.exp (2*s)) * (s^2+σ^2)^3)
        = Real.exp (2:ℝ) * (s^2+σ^2)^3 := by rw [← mul_assoc, h5]
    linarith only [hmult, heq]
  have hfin : 4 * σ^2 * (Real.exp (2*s) * (1+σ^2)^3)
      ≤ 4 * σ^2 * (Real.exp (2:ℝ) * (s^2+σ^2)^3) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  rw [div_le_div_iff₀ hd1 hd2]
  linarith only [hfin]

lemma LHSleA (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  have hσ0 : (0:ℝ) < σ := by linarith only [hσ]
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hr : (0:ℝ) < s^2 + σ^2 := by positivity
  have hexp : Real.exp (2*s) ≤ 2.72 := by
    have hle : 2*s ≤ 1 := by linarith only [hs1]
    have h := (Real.exp_le_exp).mpr hle
    linarith only [Real.exp_one_lt_d9, h]
  have hnum : (1-s)^2 + σ^2 ≤ 1 + σ^2 := by nlinarith only [hs0, hs1]
  have hden : σ^6 ≤ (s^2+σ^2)^3 := by
    have h : σ^2 ≤ s^2 + σ^2 := by nlinarith only []
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
    nlinarith only [hA, hB, sq_nonneg σ, hσ2, hσ4]
  have hmain : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := le_trans h1 h2
  rw [show (-16*s/(15*(s^2+σ^2))) = -(16*s/(15*(s^2+σ^2))) by ring]
  have hdrop : -(16*s/(15*(s^2+σ^2))) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3
      ≤ 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 := by
    have hh : (0:ℝ) ≤ 16*s/(15*(s^2+σ^2)) := by positivity
    linarith only [hh]
  linarith only [hdrop, hmain, h1, h2]

/-- Case `1/2 ≤ s ≤ 3/4`. -/
lemma LHSleB (s σ : ℝ) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 3/4) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  have hσ0 : (0:ℝ) < σ := by linarith only [hσ]
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hr : (0:ℝ) < s^2 + σ^2 := by positivity
  have hs0le : 0 ≤ s := by linarith only [hs0]
  have hs1le : s ≤ 1 := by linarith only [hs1]
  have hexp : Real.exp (2*s) ≤ 4.486 := by
    have hle : 2*s ≤ 3/2 := by linarith only [hs1]
    calc Real.exp (2*s) ≤ Real.exp ((3:ℝ)/2) := (Real.exp_le_exp).mpr hle
      _ ≤ 4.486 := exp_three_halves_le
  have hsplit : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3
      = 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 + 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 := by
    ring
  rw [hsplit]
  rw [show (-16*s/(15*(s^2+σ^2))) = -(16*s/(15*(s^2+σ^2))) by ring]
  have hA : -(16*s/(15*(s^2+σ^2))) ≤ -(8/(15*(1+σ^2))) := by
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : s^2+σ^2 ≤ 2*s*(1+σ^2) := by nlinarith only [hs0, hs1]
    linarith only [h3]
  have hB : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6 := by
    have hm : Real.exp (2*s)*(1-s)^2 ≤ 1 := exp_mul_sq_le_one s hs0le hs1le
    have hden : σ^6 ≤ (s^2+σ^2)^3 := by
      have h : σ^2 ≤ s^2 + σ^2 := by nlinarith only []
      calc σ^6 = (σ^2)^3 := by ring
        _ ≤ (s^2+σ^2)^3 := pow_le_pow_left₀ (by positivity) h 3
    have hr3 : (0:ℝ) < (s^2+σ^2)^3 := by positivity
    have hiff : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6
        ↔ 4*Real.exp (2*s)*(1-s)^2 * σ^6 ≤ 4 * (s^2+σ^2)^3 :=
      div_le_div_iff₀ hr3 hσ6
    rw [hiff]
    nlinarith only [hm, hden, hσ6]
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
      linarith only [sq_nonneg σ, hσ2]
    linarith only [h1, h2]
  have hb1 : 17.944/(σ^2*(σ^2+3/4)) ≤ (17.944/(324/25+3/4))/σ^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hσ2]
  have hb2 : 4/σ^6 ≤ (4/(324/25)^2)/σ^2 := by
    rw [div_le_div_iff₀ hσ6 (by positivity)]
    nlinarith only [hσ4, sq_nonneg σ]
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
  linarith only [hsum1, hfin, hA, hB, hC]

/-- Case `3/4 ≤ s ≤ 1`. -/
lemma LHSleC (s σ : ℝ) (hs0 : 3/4 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  have hσ0 : (0:ℝ) < σ := by linarith only [hσ]
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hr : (0:ℝ) < s^2 + σ^2 := by positivity
  have hs0le : 0 ≤ s := by linarith only [hs0]
  have hsplit : 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3
      = 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 + 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 := by
    ring
  rw [hsplit]
  rw [show (-16*s/(15*(s^2+σ^2))) = -(16*s/(15*(s^2+σ^2))) by ring]
  have hA : -(16*s/(15*(s^2+σ^2))) ≤ -(12/(15*(1+σ^2))) := by
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 3*(s^2+σ^2) ≤ 4*s*(1+σ^2) := by nlinarith only [hs0, hs1]
    linarith only [h3]
  have hB : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6 := by
    have hm : Real.exp (2*s)*(1-s)^2 ≤ 1 := exp_mul_sq_le_one s hs0le hs1
    have hden : σ^6 ≤ (s^2+σ^2)^3 := by
      have h : σ^2 ≤ s^2 + σ^2 := by nlinarith only [hs0]
      calc σ^6 = (σ^2)^3 := by ring
        _ ≤ (s^2+σ^2)^3 := pow_le_pow_left₀ (by positivity) h 3
    have hr3 : (0:ℝ) < (s^2+σ^2)^3 := by positivity
    have hiff : 4*Real.exp (2*s)*(1-s)^2/(s^2+σ^2)^3 ≤ 4/σ^6
        ↔ 4*Real.exp (2*s)*(1-s)^2 * σ^6 ≤ 4 * (s^2+σ^2)^3 :=
      div_le_div_iff₀ hr3 hσ6
    rw [hiff]
    nlinarith only [hm, hden, hσ6]
  have hC : 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 ≤ 29.6/(σ^4+3*σ^2) := by
    have hmono : 4*Real.exp (2*s)*σ^2/(s^2+σ^2)^3 ≤ 4*Real.exp (2:ℝ)*σ^2/(1+σ^2)^3 :=
      Mono72 s σ hs0 hs1 hσ
    have h2 : 4*Real.exp (2:ℝ)*σ^2/(1+σ^2)^3 ≤ 29.6/(σ^4+3*σ^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have he2 : 4*Real.exp (2:ℝ) ≤ 29.6 := by
        have h := exp_two_le
        linarith only [h]
      nlinarith only [he2, sq_nonneg σ, hσ2, hσ4, hσ6]
    linarith only [hmono, h2]
  have hb1 : 29.6/(σ^4+3*σ^2) ≤ (29.6/(324/25+3))/σ^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hσ2]
  have hb2 : 4/σ^6 ≤ (4/(324/25)^2)/σ^2 := by
    rw [div_le_div_iff₀ hσ6 (by positivity)]
    nlinarith only [hσ4, sq_nonneg σ]
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
  linarith only [hsum1, hfin, hA, hB, hC]

/-- **The `s`-dependent part is at most `1/10`.** -/
lemma LHSle72 (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 := by
  rcases le_or_gt s (1/2) with h | h
  · exact LHSleA s σ hs0 h hσ
  rcases le_or_gt s (3/4) with h2 | h2
  · exact LHSleB s σ (le_of_lt h) h2 hσ
  · exact LHSleC s σ (le_of_lt h2) hs1 hσ

/-- The `s`-independent tail: `4/σ⁴ - 12/σ⁶ + 16/σ⁵ ≤ 11/210` for `σ ≥ 18/5`. -/
lemma tail72 (σ : ℝ) (hσ : (36:ℝ)/10 ≤ σ) : 4/σ^4 - 12/σ^6 + 16/σ^5 ≤ 11/210 := by
  have hσ0 : (0:ℝ) < σ := by linarith only [hσ]
  have hσ2 : (324/25 : ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hσ4 : (324/25 : ℝ)^2 ≤ σ^4 := by nlinarith only [hσ2]
  have hσ6 : (0:ℝ) < σ^6 := by positivity
  have hmain : 4*σ^2 + 16*σ - 12 ≤ (11/210)*σ^6 := by
    have h16 : 16*σ ≤ (40/9)*σ^2 := by nlinarith only [hσ2, hσ]
    have h4 : (76/9 : ℝ) ≤ (11/210)*σ^4 := by linarith only [hσ4]
    nlinarith only [h16, h4, sq_nonneg σ, hσ0, hσ2, hσ4]
  have h2 : (4*σ^2 - 12 + 16*σ)/σ^6 ≤ 11/210 := by
    rw [div_le_iff₀ hσ6]
    linarith only [hmain]
  have h3 : 4/σ^4 - 12/σ^6 + 16/σ^5 = (4*σ^2 - 12 + 16*σ)/σ^6 := by
    field_simp
  linarith only [h2, h3]

/-! ## The rational bound on `RA72` -/

/-- **`RA72` bound** (`σ ≥ 18/5`): the `s²`, `s⁴`, `s⁶` corrections to the leading term
`-16s/(15(s²+σ²))` are at most `4/σ⁴ + 4/σ⁶`. -/
theorem RA72Bound72 (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    RA72 s σ ≤ -16*s/(15*(s^2+σ^2)) + 4/σ^4 + 4/σ^6 := by
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hs2 : s^2 ≤ 1 := by nlinarith only [hs1, hs0]
  have hσ2 : (324/25:ℝ) ≤ σ^2 := by nlinarith only [hσ]
  have hA : (0:ℝ) ≤ (8/3)*(3*s*σ^2 - s^3)/(s^2+σ^2)^3 := by
    have h : 0 ≤ 3*s*σ^2 - s^3 := by nlinarith
    positivity
  have hB : 4*(s^4 - 6*s^2*σ^2 + σ^4)/(s^2+σ^2)^4 ≤ 4/σ^4 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (s^2+σ^2)^4) (by positivity : (0:ℝ) < σ^4)]
    have h1 : s^4 - 6*s^2*σ^2 + σ^4 ≤ σ^4 := by nlinarith only [hs2, hσ2]
    have h2 : σ^4 * σ^4 ≤ (s^2+σ^2)^4 := by
      have h3 : σ^2 ≤ s^2+σ^2 := by nlinarith only []
      calc σ^4*σ^4 = (σ^2)^4 := by ring
        _ ≤ (s^2+σ^2)^4 := pow_le_pow_left₀ (by positivity) h3 4
    have h4 : (s^4 - 6*s^2*σ^2 + σ^4)*σ^4 ≤ (s^2+σ^2)^4 :=
      le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) h2
    linarith only [h4]
  have hC : -(4/σ^6) ≤ 4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)/(s^2+σ^2)^6 := by
    by_cases hNC : (0:ℝ) ≤ s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6
    · have h1 : (0:ℝ) ≤ 4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)/(s^2+σ^2)^6 := by positivity
      have h2 : (0:ℝ) ≤ 4/σ^6 := by positivity
      linarith only [h1, h2]
    · have hNC' : s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6 < 0 := lt_of_not_ge hNC
      have hquad : 0 ≤ 15*σ^4 - 15*s^2*σ^2 + s^4 := by
        have hu : 0 ≤ 15*σ^2*(σ^2 - s^2) := mul_nonneg (by positivity) (by linarith only [hs2, hσ2])
        nlinarith only [hu, hσ2, hs2]
      have hN : -σ^6 ≤ s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6 := by
        have hp : 0 ≤ s^2 * (15*σ^4 - 15*s^2*σ^2 + s^4) := mul_nonneg (sq_nonneg s) hquad
        linarith only [hp]
      have h4 : (0:ℝ) ≤ (s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)*σ^6 + (s^2+σ^2)^6 := by
        have h5 : -σ^12 ≤ (s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)*σ^6 := by
          have := mul_le_mul_of_nonneg_right hN (by positivity : (0:ℝ) ≤ σ^6)
          linarith only [this]
        have h6 : σ^12 ≤ (s^2+σ^2)^6 := by
          have h3 : σ^2 ≤ s^2+σ^2 := by nlinarith only []
          calc σ^12 = (σ^2)^6 := by ring
            _ ≤ (s^2+σ^2)^6 := pow_le_pow_left₀ (by positivity) h3 6
        linarith only [h5, h6]
      have key : -(4/σ^6) * (s^2+σ^2)^6
          ≤ 4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6) := by
        have h5 : -4*(s^2+σ^2)^6/σ^6 ≤ 4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < σ^6)]
          linarith only [h4]
        calc -(4/σ^6) * (s^2+σ^2)^6 = -4*(s^2+σ^2)^6/σ^6 := by ring
          _ ≤ 4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6) := h5
      exact (le_div_iff₀ (by positivity : (0:ℝ) < (s^2+σ^2)^6)).mpr key
  simp only [RA72]
  linarith only [hA, hB, hC]

/-! ## The modulus bound for the exponential part -/

/-- **`|cos 2σ · RB72 + sin 2σ · RI72| ≤ 4((1-s)²+σ²)/(s²+σ²)³`**, i.e. the modulus of
`B72(-s+iσ) = 4(1-s+iσ)²/(-s+iσ)⁶`. -/
theorem TrigBound72 (s σ : ℝ) :
    |Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ|
      ≤ 4 * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3 := by
  have hRHSnn : 0 ≤ 4 * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3 := by positivity
  refine abs_le_of_sq_le_sq ?_ hRHSnn
  have hcs : (Real.cos (2*σ))^2 + (Real.sin (2*σ))^2 = 1 := Real.cos_sq_add_sin_sq (2*σ)
  have h1 : (Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ)^2
      ≤ RB72 s σ^2 + RI72 s σ^2 := by
    nlinarith only [sq_nonneg (Real.sin (2*σ) * RB72 s σ - Real.cos (2*σ) * RI72 s σ), hcs]
  have h2 : RB72 s σ^2 + RI72 s σ^2 = (4 * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3)^2 := by
    rcases eq_or_ne (s^2+σ^2) 0 with h0 | h0
    · have hs : s = 0 := by nlinarith only [sq_nonneg s, sq_nonneg σ, h0]
      have hσ : σ = 0 := by nlinarith only [sq_nonneg s, sq_nonneg σ, h0]
      subst hs; subst hσ; norm_num [RB72, RI72]
    · simp only [RB72, RI72]; field_simp; ring
  linarith only [h1, h2]
theorem LargeSigma72 (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    Work.ZeroFreeTables.OffAxis.Isub s σ ≤ 16/105 := by
  have hσ0 : (0:ℝ) < σ := by linarith only [hσ]
  have hρ : s^2 + σ^2 ≠ 0 := by positivity
  have hlhs : -16*s/(15*(s^2+σ^2)) + 4*Real.exp (2*s)*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 1/10 :=
    LHSle72 s σ hs0 hs1 hσ
  have hra : RA72 s σ ≤ -16*s/(15*(s^2+σ^2)) + 4/σ^4 + 4/σ^6 :=
    RA72Bound72 s σ hs0 hs1 hσ
  have htail : 4/σ^4 - 12/σ^6 + 16/σ^5 ≤ 11/210 := tail72 σ hσ
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
      have hb := TrigBound72 s σ
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
    linarith only [hmain, hc, hs]
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
  linarith only [step1, hkey, hlhs, htail, hra, htrig]


/-! ## Assembly: `Isub s σ ≤ 16/105` for all `s ∈ [0,1]` and all `σ` -/

/-- **`Isub s σ ≤ 16/105` for `0 ≤ s ≤ 1`, `σ ≥ 0`.**  For `σ ≥ 18/5` this is `LargeSigma72`;
below that, `G72SmallS` (`s ≤ 7/25`), the eight `F`-method cells (`σ ≤ 51/20`, and `σ ≤ 18/5`
for `s ≥ 7/10`) and the grid `grid_main` (`51/20 ≤ σ ≤ 18/5`, `s ≤ 73/100`) cover the whole
square. -/
theorem Isub_le_nonneg (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : 0 ≤ σ) :
    Isub s σ ≤ 16/105 := by
  by_cases h36 : (36:ℝ)/10 ≤ σ
  · exact LargeSigma72 s σ hs0 hs1 h36
  · have h36' : σ < 36/10 := lt_of_not_ge h36
    have hσ18 : σ ≤ 18/5 := by norm_num at h36' ⊢; linarith only [h36]
    rcases le_or_gt s (7/25) with h | h
    · exact G72SmallS s σ hs0 h hσ
    · have h725 : 7/25 ≤ s := le_of_lt h
      rcases le_or_gt s (7/10) with h2 | h2
      · by_cases h255 : σ ≤ 51/20
        · rcases le_or_gt s (3/10) with h3 | h3
          · exact B2cell_1 s σ h725 h3 hσ h255
          · have h310 : 3/10 ≤ s := le_of_lt h3
            rcases le_or_gt s (7/20) with h4 | h4
            · exact B2cell_2 s σ h310 h4 hσ h255
            · have h720 : 7/20 ≤ s := le_of_lt h4
              rcases le_or_gt s (1/2) with h5 | h5
              · exact B2cell_3 s σ h720 h5 hσ h255
              · have h12 : 1/2 ≤ s := le_of_lt h5
                rcases le_or_gt s (3/5) with h6 | h6
                · exact B2cell_4 s σ h12 h6 hσ h255
                · exact B2cell_5 s σ (le_of_lt h6) h2 hσ h255
        · have h255' : 51/20 ≤ σ := le_of_lt (lt_of_not_ge h255)
          exact grid_main s σ h725 (by linarith only [h2]) h255' hσ18
      · have h710 : 7/10 ≤ s := le_of_lt h2
        rcases le_or_gt s (4/5) with h3 | h3
        · exact B2cell_6 s σ h710 h3 hσ hσ18
        · have h45 : 4/5 ≤ s := le_of_lt h3
          rcases le_or_gt s (9/10) with h4 | h4
          · exact B2cell_7 s σ h45 h4 hσ hσ18
          · exact B2cell_8 s σ (le_of_lt h4) (by linarith only [hs1]) hσ hσ18

/-- `Isub s ·` is even. -/
lemma Isub_even (s σ : ℝ) : Isub s (-σ) = Isub s σ := by
  rw [Isub_eq_integral, Isub_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  show (Real.exp (s*y) - 2) * Real.cos ((-σ)*y) * g72 y
      = (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y
  rw [neg_mul, Real.cos_neg]

/-- **`Isub s σ ≤ 16/105` for `0 ≤ s ≤ 1` and every real `σ`.** -/
theorem Isub_le_all (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Isub s σ ≤ 16/105 := by
  rcases le_or_gt 0 σ with h | h
  · exact Isub_le_nonneg s σ hs0 hs1 h
  · have h2 : Isub s σ = Isub s (-σ) := (Isub_even s σ).symm
    rw [h2]
    exact Isub_le_nonneg s (-σ) hs0 hs1 (by linarith only [h])

/-! ## Transfer to the `tf72Fc` normalisation -/

/-- `tf72Fc 1 = G72`, i.e. `∫₀² e^{-wy} f_1(y) dy = ∫₀² e^{-wy} g72(y) dy`. -/
theorem tf72Fc_one_eq_G72 (w : ℂ) : tf72Fc 1 w = G72 w := by
  have hpt : ∀ t ∈ Set.uIcc (0:ℝ) 2, tf72f 1 t = g72 t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht
    have ht' : t ∈ Set.Icc (0:ℝ) (2/1) := by simpa using ht
    rw [tf72f_eq_poly 1 (by norm_num) t ht']
    simp only [Work.ZeroFreeTables.g72]
    ring
  unfold tf72Fc G72
  rw [show (2:ℝ)/1 = 2 by norm_num]
  apply intervalIntegral.integral_congr
  intro t ht
  show Complex.exp (-(w * (t:ℂ))) * ((tf72f 1 t : ℝ) : ℂ)
      = Complex.exp (-(w * (t:ℂ))) * ((g72 t : ℝ) : ℂ)
  rw [hpt t ht]

theorem TF72Num103a :
    ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 →
      (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re
        - 2 * (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) ((m : ℂ) * Complex.I)).re ≤ 16/105 := by
  intro a m ha ham
  have hs : ((((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I) / (((6:ℝ)/7 : ℝ)))
      = ((-(7*a/6) : ℝ) : ℂ) + ((7*m/6 : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  have hs2 : (((m : ℂ) * Complex.I) / (((6:ℝ)/7 : ℝ)))
      = (((7*m/6 : ℝ)) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [tf72Fc_scale ((6:ℝ)/7) (by norm_num) (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I),
      tf72Fc_scale ((6:ℝ)/7) (by norm_num) ((m : ℂ) * Complex.I), hs, hs2,
      tf72Fc_one_eq_G72, tf72Fc_one_eq_G72]
  change Isub (7*a/6) (7*m/6) ≤ 16/105
  exact Isub_le_all (7*a/6) (7*m/6) (by linarith only [ha]) (by linarith only [ham])

end Work.OffAxis
