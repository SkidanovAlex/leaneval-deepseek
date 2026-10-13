import Mathlib
import Submission.Work.WilkiesH.Interp.V2master.Basic

namespace Work.WilkiesH.Interp.V2master

open Work.WilkiesH.Interp

lemma log_dV_le (μ g H : ℕ)
    (hyb : ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) + 1 ≤
      25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
        (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) /
          ((Work.WilkiesH.Interp.V2master.rhoN μ g H : ℕ) : ℝ))) :
    Real.log ((((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ)) + 1) ≤
      16 + ((μ:ℝ)+1)^2 + Real.log ((g:ℝ)+1)
        + (μ:ℝ) * Real.log (((Work.WilkiesH.Interp.V2master.rhoN μ g H : ℕ) : ℝ)) := by
  -- positivity of the two parameters
  have hR1 : (1:ℝ) ≤ ((rhoN μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_rhoN μ g H
  have hRp : (0:ℝ) < ((rhoN μ g H : ℕ) : ℝ) := by linarith
  have hFp : (0:ℝ) < (((μ + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (μ + 1)
  have hg0 : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g
  -- nonvanishing facts used by `Real.log_mul`
  have hne25 : (25:ℝ) ≠ 0 := by norm_num
  have hneF : (((μ + 1).factorial : ℕ) : ℝ) ≠ 0 := ne_of_gt hFp
  have hne8g9 : (8 * (g : ℝ) + 9) ≠ 0 := by linarith
  have hneRpow : ((rhoN μ g H : ℕ) : ℝ) ^ μ ≠ 0 := ne_of_gt (pow_pos hRp μ)
  have hne1 : (25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hne25 hneF) hne8g9
  have hne2 : (25 * (((μ + 1).factorial : ℕ) : ℝ)) ≠ 0 := mul_ne_zero hne25 hneF
  -- `bV μ g H = (rhoN μ g H)^(μ+1)`, hence `bV/rhoN = (rhoN)^μ`
  have hbpow : ((bV μ g H : ℕ) : ℝ) = ((rhoN μ g H : ℕ) : ℝ) ^ (μ+1) := by
    simp only [bV_eq_rhoN, Nat.cast_pow]
  have hdiv : ((bV μ g H : ℕ) : ℝ) / ((rhoN μ g H : ℕ) : ℝ)
      = ((rhoN μ g H : ℕ) : ℝ) ^ μ := by
    rw [hbpow, pow_succ, mul_div_cancel_right₀ _ (ne_of_gt hRp)]
  -- numerical bounds on the logarithmic constants
  have hlog25 : Real.log 25 ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5)
    have h25 : Real.log (25:ℝ) = 2 * Real.log 5 := by
      rw [show (25:ℝ) = 5^2 by norm_num, Real.log_pow]; norm_num
    rw [h25]; linarith
  have hlog8g9 : Real.log (8 * (g : ℝ) + 9) ≤ 4 + Real.log ((g:ℝ)+1) := by
    have hg1 : (0:ℝ) < (g:ℝ)+1 := by linarith
    have hle : 8 * (g:ℝ) + 9 ≤ 9 * ((g:ℝ)+1) := by linarith
    have hpos : (0:ℝ) < 8 * (g:ℝ) + 9 := by linarith
    have hmono := Real.log_le_log hpos hle
    have h9mul : Real.log (9 * ((g:ℝ)+1)) = Real.log 9 + Real.log ((g:ℝ)+1) :=
      Real.log_mul (by norm_num) (ne_of_gt hg1)
    rw [h9mul] at hmono
    have h9 : Real.log (9:ℝ) ≤ 4 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
      have h9' : Real.log (9:ℝ) = 2 * Real.log 3 := by
        rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]; norm_num
      rw [h9']; linarith
    linarith
  have hlogfact : Real.log (((μ + 1).factorial : ℕ) : ℝ) ≤ ((μ:ℝ)+1)^2 := by
    have hfac : (((μ + 1).factorial : ℕ) : ℝ) ≤ ((μ:ℝ)+1)^(μ+1) := by
      have h := Nat.factorial_le_pow (μ+1)
      have h2 : (((μ+1)^(μ+1) : ℕ) : ℝ) = ((μ:ℝ)+1)^(μ+1) := by push_cast; ring
      calc (((μ + 1).factorial : ℕ) : ℝ) ≤ (((μ+1)^(μ+1) : ℕ) : ℝ) := by exact_mod_cast h
        _ = ((μ:ℝ)+1)^(μ+1) := h2
    have hpos : (0:ℝ) < (((μ + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (μ+1)
    have hmono := Real.log_le_log hpos hfac
    rw [Real.log_pow] at hmono
    push_cast at hmono
    have hμ1 : (0:ℝ) ≤ (μ:ℝ)+1 := by
      have h : (0:ℝ) ≤ (μ:ℝ) := Nat.cast_nonneg μ
      linarith
    have hlogμ1 : Real.log ((μ:ℝ)+1) ≤ (μ:ℝ)+1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (μ:ℝ)+1 by
        have h : (0:ℝ) ≤ (μ:ℝ) := Nat.cast_nonneg μ
        linarith)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlogμ1 hμ1
    calc Real.log (((μ + 1).factorial : ℕ) : ℝ) ≤ ((μ:ℝ)+1) * Real.log ((μ:ℝ)+1) := hmono
      _ ≤ ((μ:ℝ)+1) * ((μ:ℝ)+1) := hmul
      _ = ((μ:ℝ)+1)^2 := by ring
  -- replace `bV/rhoN` by `(rhoN)^μ` in the hypothesis
  have hyb' : ((dV μ g (bV μ g H) : ℕ) : ℝ) + 1 ≤
      25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
        (((rhoN μ g H : ℕ) : ℝ) ^ μ) := by
    calc ((dV μ g (bV μ g H) : ℕ) : ℝ) + 1
        ≤ 25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
            (((bV μ g H : ℕ) : ℝ) / ((rhoN μ g H : ℕ) : ℝ)) := hyb
      _ = 25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
            (((rhoN μ g H : ℕ) : ℝ) ^ μ) := by rw [hdiv]
  have hdpos : (0:ℝ) < ((dV μ g (bV μ g H) : ℕ) : ℝ) + 1 := by
    have h : (0:ℝ) ≤ ((dV μ g (bV μ g H) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  -- take logarithms
  have hstep1 : Real.log ((((dV μ g (bV μ g H) : ℕ) : ℝ)) + 1) ≤
      Real.log (25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
        (((rhoN μ g H : ℕ) : ℝ) ^ μ)) :=
    Real.log_le_log hdpos hyb'
  have hA : Real.log (25 * (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) *
        (((rhoN μ g H : ℕ) : ℝ) ^ μ))
      = Real.log 25 + Real.log (((μ + 1).factorial : ℕ) : ℝ) + Real.log (8 * (g : ℝ) + 9)
        + (μ:ℝ) * Real.log (((rhoN μ g H : ℕ) : ℝ)) := by
    rw [Real.log_mul hne1 hneRpow, Real.log_mul hne2 hne8g9, Real.log_mul hne25 hneF,
      Real.log_pow]
  rw [hA] at hstep1
  linarith [hstep1, hlog25, hlog8g9, hlogfact]

end Work.WilkiesH.Interp.V2master
