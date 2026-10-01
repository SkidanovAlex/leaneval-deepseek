import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.abs_log_norm_Gamma_sub_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_abs_sq_half

open Complex
open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

private lemma exp_abs_le_exp_add (x : ℝ) :
    Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

private lemma exp_pi_abs_le_two_cosh (v : ℝ) :
    Real.exp (Real.pi * |v|) ≤ 2 * Real.cosh (Real.pi * v) := by
  have hx := exp_abs_le_exp_add (Real.pi * v)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hx
  rw [Real.cosh_eq]
  rw [show 2 * ((Real.exp (Real.pi * v) + Real.exp (-(Real.pi * v))) / 2)
        = Real.exp (Real.pi * v) + Real.exp (-(Real.pi * v)) by ring]
  exact hx

private lemma Gamma_half_vertical_le (v : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|) := by
  have harg : ((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I = (1 / 2 : ℂ) + I * (v : ℂ) := by
    push_cast
    ring
  rw [harg]
  set B : ℝ := ‖Complex.Gamma ((1 / 2 : ℂ) + I * (v : ℂ))‖ with hBdef
  have hsq : B ^ 2 = Real.pi / Real.cosh (Real.pi * v) := by
    rw [hBdef]
    exact gamma_abs_sq_half v
  have hhalf_pos : 0 < Real.exp (Real.pi * |v|) / 2 := by positivity
  have hle1 : Real.exp (Real.pi * |v|) / 2 ≤ Real.cosh (Real.pi * v) := by
    have h := exp_pi_abs_le_two_cosh v
    linarith
  have heq : Real.pi / (Real.exp (Real.pi * |v|) / 2) = 2 * Real.pi * Real.exp (-(Real.pi * |v|)) := by
    rw [Real.exp_neg]
    field_simp
  have hBsq_le : B ^ 2 ≤ 2 * Real.pi * Real.exp (-(Real.pi * |v|)) := by
    rw [hsq]
    exact le_trans (div_le_div_of_nonneg_left Real.pi_pos.le hhalf_pos hle1) (le_of_eq heq)
  have hRsq : (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|)) ^ 2
      = 2 * Real.pi * Real.exp (-(Real.pi * |v|)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        ← Real.exp_nat_mul (-(Real.pi / 2) * |v|) 2]
    congr 1
    ring_nf
  have hBnonneg : 0 ≤ B := norm_nonneg _
  have hRnonneg : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|) := by positivity
  calc B = Real.sqrt (B ^ 2) := (Real.sqrt_sq hBnonneg).symm
    _ ≤ Real.sqrt ((Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hRsq]
          exact hBsq_le
    _ = Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|) := Real.sqrt_sq hRnonneg

private lemma Gamma_ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  linarith

theorem Gamma_vertical_upper_uniform_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ (u v : ℝ), (1 : ℝ) / 2 ≤ u → u ≤ 2 →
      ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ≤
        C * (1 + |v|) ^ (u - 1 / 2) * Real.exp (-(Real.pi / 2) * |v|) := by
  refine ⟨Real.exp ((1 / 2) * Real.log (2 * Real.pi) + (3 / 2) * (Real.log 2 + 2)),
    Real.exp_pos _, ?_⟩
  intro u v hu1 hu2
  have hu8 : u ≤ 8 := le_trans hu2 (by norm_num)
  have hreA : ((u : ℂ) + (v : ℂ) * I).re = u := by simp
  have hreB : (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I).re = 1 / 2 := by simp
  have hApos : 0 < ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact Gamma_ne_zero_of_re_pos (by rw [hreA]; linarith)
  have hBpos : 0 < ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact Gamma_ne_zero_of_re_pos (by rw [hreB]; norm_num)
  -- increment along a vertical line
  have hAincr : Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ +
        (u - 1 / 2) * (Real.log (2 + |v|) + 2) := by
    have h := abs_log_norm_Gamma_sub_le (1 / 2) u v le_rfl hu1 hu8
    have h' := le_abs_self (Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ -
      Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖)
    linarith
  -- critical-line bound
  have hBincr : Real.log ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (1 / 2) * Real.log (2 * Real.pi) + (-(Real.pi / 2)) * |v| := by
    have h1 := Real.log_le_log hBpos (Gamma_half_vertical_le v)
    rw [Real.log_mul (Real.sqrt_pos.mpr (by positivity)).ne' (Real.exp_ne_zero _),
        Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.log_exp] at h1
    linarith
  -- logarithm growth of the polynomial factor
  have hlog2v : Real.log (2 + |v|) ≤ Real.log 2 + Real.log (1 + |v|) := by
    have hle : 2 + |v| ≤ 2 * (1 + |v|) := by
      have : (0 : ℝ) ≤ |v| := abs_nonneg v
      linarith
    calc Real.log (2 + |v|) ≤ Real.log (2 * (1 + |v|)) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log 2 + Real.log (1 + |v|) :=
          Real.log_mul (by norm_num) (by positivity)
  have hR : (u - 1 / 2) * (Real.log (2 + |v|) + 2) ≤
      Real.log (1 + |v|) * (u - 1 / 2) + (3 / 2) * (Real.log 2 + 2) := by
    have hu_half : 0 ≤ u - 1 / 2 := by linarith
    have hlog22 : 0 ≤ Real.log 2 + 2 := by
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    have hstep1 : (u - 1 / 2) * (Real.log (2 + |v|) + 2) ≤
        (u - 1 / 2) * (Real.log 2 + Real.log (1 + |v|) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hlog2v]) hu_half
    have hstep2a : (u - 1 / 2) * (Real.log 2 + 2) ≤ (3 / 2) * (Real.log 2 + 2) :=
      mul_le_mul_of_nonneg_right (by linarith : u - 1 / 2 ≤ 3 / 2) hlog22
    nlinarith [hstep1, hstep2a]
  -- combine in log form
  have hkey : Real.log ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ≤
      ((1 / 2) * Real.log (2 * Real.pi) + (3 / 2) * (Real.log 2 + 2)) +
        (Real.log (1 + |v|) * (u - 1 / 2) + (-(Real.pi / 2)) * |v|) := by
    linarith [hAincr, hBincr, hR]
  have hmain : ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp (((1 / 2) * Real.log (2 * Real.pi) + (3 / 2) * (Real.log 2 + 2)) +
        (Real.log (1 + |v|) * (u - 1 / 2) + (-(Real.pi / 2)) * |v|)) := by
    rw [← Real.exp_log hApos]
    exact Real.exp_le_exp.mpr hkey
  refine le_trans hmain (le_of_eq ?_)
  rw [Real.exp_add ((1 / 2) * Real.log (2 * Real.pi) + (3 / 2) * (Real.log 2 + 2))
        (Real.log (1 + |v|) * (u - 1 / 2) + (-(Real.pi / 2)) * |v|)]
  rw [Real.exp_add (Real.log (1 + |v|) * (u - 1 / 2)) ((-(Real.pi / 2)) * |v|)]
  rw [← Real.rpow_def_of_pos (x := 1 + |v|) (by positivity) (u - 1 / 2)]
  ring

end Commons.Analysis.SpecialFunctions.Gamma
