import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72TrigBound
import Submission.Work.OffAxis.Tf72One.exp_bounds

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-! ## A crude bound for `Re G72` off the axis

This file proves `Re G72(-s+iσ) ≤ 1/10` for `0 ≤ s ≤ 17/16` and `σ ≥ 5`, by splitting the closed
form `G72ReClosed0` into its rational part (`RA72`, estimated term by term) and its oscillatory
part (bounded by `G72TrigBound` together with `exp (17/8) ≤ 42/5`). -/

/-- `σ⁶ ≤ (s²+σ²)³`. -/
private lemma pow_six_le (s σ : ℝ) : σ^6 ≤ (s^2+σ^2)^3 := by
  have hρ3 : (s^2+σ^2)^3 = s^6 + 3*s^4*σ^2 + 3*s^2*σ^4 + σ^6 := by ring
  rw [hρ3]
  linarith [show (0:ℝ) ≤ 3*s^4*σ^2 by positivity, show (0:ℝ) ≤ 3*s^2*σ^4 by positivity,
    show (0:ℝ) ≤ s^6 by positivity]

/-- The rational part of `Re G72(-s+iσ)` is `≤ 4/σ⁴ + 60/σ⁶` for `0 ≤ s ≤ 17/16` and `σ ≥ 5`.

The first two summands of `RA72` are non-positive (using `3σ² ≥ s²`), the third is at most
`4/(s²+σ²)² ≤ 4/σ⁴` (its numerator is at most `(s²+σ²)²`) and the fourth is at most
`60/(s²+σ²)³ ≤ 60/σ⁶` (its numerator is at most `15(s²+σ²)³`). -/
private lemma RA72_le_crude (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (hσ : 5 ≤ σ) :
    RA72 s σ ≤ 4/σ^4 + 60/σ^6 := by
  have hT1 : -16*s/(15*(s^2+σ^2)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity
  have hT2 : 0 ≤ (8/3)*(3*s*σ^2 - s^3)/(s^2+σ^2)^3 := by
    apply div_nonneg
    · apply mul_nonneg (by norm_num)
      have h : 0 ≤ 3*σ^2 - s^2 := by nlinarith
      have h2 : 0 ≤ s*(3*σ^2 - s^2) := mul_nonneg hs0 h
      nlinarith [h2]
    · positivity
  have hT3 : 4*(s^4 - 6*s^2*σ^2 + σ^4)/(s^2+σ^2)^4 ≤ 4/σ^4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key : 4*(s^2+σ^2)^4 - 4*(s^4 - 6*s^2*σ^2 + σ^4)*σ^4
        = 4*(s^8 + 4*s^6*σ^2 + 5*s^4*σ^4 + 10*s^2*σ^6) := by ring
    have hpos : 0 ≤ 4*(s^8 + 4*s^6*σ^2 + 5*s^4*σ^4 + 10*s^2*σ^6) := by positivity
    linarith [key, hpos]
  have hT4 : -(4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)/(s^2+σ^2)^6) ≤ 60/σ^6 := by
    rw [← neg_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hP : -(15*(s^2+σ^2)^3) ≤ s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6 := by
      have key : 15*(s^2+σ^2)^3 + (s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)
          = 16*s^6 + 30*s^4*σ^2 + 60*s^2*σ^4 + 14*σ^6 := by ring
      have hpos : 0 ≤ 16*s^6 + 30*s^4*σ^2 + 60*s^2*σ^4 + 14*σ^6 := by positivity
      linarith [key, hpos]
    have h1 : -(4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)) ≤ 60*(s^2+σ^2)^3 := by
      linarith [hP]
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ σ^6 by positivity)
    have h3 : 60*(s^2+σ^2)^3*σ^6 ≤ 60*(s^2+σ^2)^6 := by
      have hρ3 : (0:ℝ) ≤ (s^2+σ^2)^3 := by positivity
      nlinarith [pow_six_le s σ, hρ3]
    linarith [h2, h3]
  unfold RA72
  linarith [hT1, hT2, hT3, hT4]

/-- `exp (17/8) ≤ 42/5`. -/
private lemma exp_17_8_le : Real.exp ((17:ℝ)/8) ≤ 42/5 := by
  obtain ⟨_,_,_,_,_,_,_,_,h9⟩ := exp_bounds
  linarith

/-- The oscillatory part of `Re G72(-s+iσ)`, multiplied by `e^{2s}`, is at most
`(42/5)(4/σ⁴ + 4/σ⁶)`: use `|cos·RB72 + sin·RI72| ≤ 4((1-s)²+σ²)/(s²+σ²)³`,
`(1-s)² ≤ 1`, `(s²+σ²)³ ≥ σ⁶` and `e^{2s} ≤ e^{17/8} ≤ 42/5`. -/
private lemma exp_trig_le (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (hσ : 5 ≤ σ) :
    Real.exp (2*s) * (Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ)
      ≤ (42/5) * (4/σ^4 + 4/σ^6) := by
  have htri : Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ
      ≤ 4*((1-s)^2+σ^2)/(s^2+σ^2)^3 := le_trans (le_abs_self _) (G72TrigBound s σ)
  have hexp0 : 0 ≤ Real.exp (2*s) := (Real.exp_pos _).le
  have hexp : Real.exp (2*s) ≤ 42/5 := by
    have h1 : 2*s ≤ 17/8 := by linarith
    exact le_trans (Real.exp_le_exp.mpr h1) exp_17_8_le
  have hT0 : 0 ≤ 4*((1-s)^2+σ^2)/(s^2+σ^2)^3 := by positivity
  have hstep1 : Real.exp (2*s) * (Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ)
      ≤ Real.exp (2*s) * (4*((1-s)^2+σ^2)/(s^2+σ^2)^3) :=
    mul_le_mul_of_nonneg_left htri hexp0
  have hstep2 : Real.exp (2*s) * (4*((1-s)^2+σ^2)/(s^2+σ^2)^3)
      ≤ (42/5) * (4*((1-s)^2+σ^2)/(s^2+σ^2)^3) :=
    mul_le_mul_of_nonneg_right hexp hT0
  have hsq : (1-s)^2 ≤ 1 := by nlinarith [hs0, hs1]
  have hstep3 : 4*((1-s)^2+σ^2)/(s^2+σ^2)^3 ≤ 4*(1+σ^2)/σ^6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 4*((1-s)^2+σ^2)*σ^6 ≤ 4*(1+σ^2)*σ^6 := by
      have h := mul_le_mul_of_nonneg_right (show (1-s)^2+σ^2 ≤ 1+σ^2 by linarith)
        (show (0:ℝ) ≤ σ^6 by positivity)
      nlinarith [h]
    have h2 : 4*(1+σ^2)*σ^6 ≤ 4*(1+σ^2)*(s^2+σ^2)^3 := by
      have h := mul_le_mul_of_nonneg_left (pow_six_le s σ)
        (show (0:ℝ) ≤ 4*(1+σ^2) by positivity)
      nlinarith [h]
    exact le_trans h1 h2
  have hstep3' : 4*(1+σ^2)/σ^6 = 4/σ^4 + 4/σ^6 := by
    have hσne : σ ≠ 0 := by positivity
    field_simp
    ring
  have hstep4 : (42/5) * (4*((1-s)^2+σ^2)/(s^2+σ^2)^3) ≤ (42/5)*(4/σ^4 + 4/σ^6) := by
    have h := mul_le_mul_of_nonneg_left hstep3 (show (0:ℝ) ≤ 42/5 by norm_num)
    rwa [hstep3'] at h
  exact le_trans hstep1 (le_trans hstep2 hstep4)

/-- Crude large-`σ` bound for the real part of the Laplace transform: for `0 ≤ s ≤ 17/16` and
`σ ≥ 5`, `Re G72(-s+iσ) ≤ 1/10`.  Route: `G72_eq_closed` writes `G72 w = A72 w + e^{-2w}B72 w` with
`A72 w = (1/30)(32/w - 80/w³ + 120/w⁴ - 120/w⁶)` and `B72 w = 4(1+w)²/w⁶`; the two leading terms of
`Re A72(-s+iσ)` are non-positive (`-16s/(15(s²+σ²))` and `-(8/3)(3sσ²-s³)/(s²+σ²)³`), the remaining
two are bounded by `4/(s²+σ²)² + 60/(s²+σ²)³ ≤ 4/σ⁴ + 60/σ⁶`, and
`e^{2s}|B72(-s+iσ)| ≤ e^{17/8}·4(1+σ²)/σ⁶ ≤ 33.5/σ⁴ + 33.5/σ⁶`.  At `σ = 5` the total
`37.5/σ⁴ + 93.5/σ⁶ = 0.066 < 1/10`, and it decreases in `σ`. -/
theorem R_le_crude (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (hσ : 5 ≤ σ) :
    (Work.ZeroFreeTables.G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re ≤ 1/10 := by
  have hσ0 : 0 < σ := by linarith
  have hρ : s^2 + σ^2 ≠ 0 := ne_of_gt (by positivity)
  rw [G72ReClosed0 hρ]
  have hfin : (188/5)/σ^4 + (468/5)/σ^6 ≤ 1/10 := by
    have h4 : (625:ℝ) ≤ σ^4 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hσ 4
      norm_num at h
      exact h
    have h6 : (15625:ℝ) ≤ σ^6 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hσ 6
      norm_num at h
      exact h
    have h1 : (188/5)/σ^4 ≤ (188/5)/625 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
    have h2 : (468/5)/σ^6 ≤ (468/5)/15625 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h6
    have h3 : (188/5)/625 + (468/5)/15625 ≤ 1/10 := by norm_num
    linarith
  have hmid : (4/σ^4 + 60/σ^6) + (42/5)*(4/σ^4+4/σ^6) ≤ 1/10 := by
    have he : (4/σ^4 + 60/σ^6) + (42/5)*(4/σ^4+4/σ^6) = (188/5)/σ^4 + (468/5)/σ^6 := by
      have hσne : σ ≠ 0 := ne_of_gt hσ0
      field_simp
      ring
    rw [he]
    exact hfin
  exact le_trans (add_le_add (RA72_le_crude s σ hs0 hs1 hσ) (exp_trig_le s σ hs0 hs1 hσ)) hmid

end Work.OffAxis.Tf72One
