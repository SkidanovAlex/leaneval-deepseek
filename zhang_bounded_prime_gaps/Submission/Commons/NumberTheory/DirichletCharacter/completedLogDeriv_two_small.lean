import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_le_small
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ### Tight gamma-factor bound on the line `Re s = 2`

This refines `norm_logDeriv_Gammaℝ_le` (additive constant `8` inside the logarithm, obtained
from `digamma_vertical_bound`) to the mid-strip digamma bound
`Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le`, whose additive constant is `2`.
For `s = x + iy` with `x ∈ [1, 16]` we have `s/2 = (x/2) + i(y/2)` with `x/2 ∈ [1/2, 8]`, so
`‖digamma (s/2)‖ ≤ log (2 + |y/2|) + 2 ≤ log (2 + |y|) + 2`, and the formula
`logDeriv Γℝ s = -log π / 2 + digamma(s/2) / 2` gives the bound below. -/

lemma norm_logDeriv_Gammaℝ_le_small (x y : ℝ) (hx1 : (1 : ℝ) ≤ x) (hx2 : x ≤ 16) :
    ‖logDeriv Complex.Gammaℝ ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |y|) + 2) := by
  let s : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have hs : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have hx1' : (1 : ℝ) / 2 ≤ x / 2 := by linarith
  have hx2' : x / 2 ≤ 8 := by linarith
  have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (x / 2) (y / 2) hx1' hx2'
  have hdg' : ‖Complex.digamma (s / 2)‖ ≤ Real.log (2 + |y / 2|) + 2 := by
    rw [half_expand x y]
    exact hdg
  have hdg'' : ‖Complex.digamma (s / 2)‖ / 2 ≤ (Real.log (2 + |y|) + 2) / 2 := by
    have hlogmono : Real.log (2 + |y / 2|) ≤ Real.log (2 + |y|) := by
      apply Real.log_le_log
      · positivity
      · have hy0 : 0 ≤ |y| := abs_nonneg y
        have : |y / 2| ≤ |y| := by
          rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
          exact div_le_self hy0 (by norm_num)
        linarith
    have h1 : ‖Complex.digamma (s / 2)‖ / 2 ≤ (Real.log (2 + |y / 2|) + 2) / 2 :=
      div_le_div_of_nonneg_right hdg' (by norm_num)
    exact le_trans h1 (div_le_div_of_nonneg_right (by linarith) (by norm_num))
  have hformula := logDeriv_Gammaℝ_formula s hs
  rw [hformula]
  have hnorm1 : ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ ≤ Real.log Real.pi / 2 := by
    have hlogpi_nonneg : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hlogR : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      simpa using (Complex.ofReal_log (x := Real.pi) (by positivity : 0 ≤ Real.pi)).symm
    rw [hlogR]
    rw [norm_div]
    rw [norm_neg]
    rw [Complex.norm_of_nonneg hlogpi_nonneg]
    norm_num
  have hnorm2 : ‖(Complex.digamma (s / 2) / 2 : ℂ)‖ ≤ (Real.log (2 + |y|) + 2) / 2 := by
    rw [norm_div]
    have this : ‖Complex.digamma (s / 2)‖ / ‖(2 : ℂ)‖ ≤ (Real.log (2 + |y|) + 2) / 2 := by
      norm_num
      exact hdg''
    simpa using this
  calc
    ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 : ℂ)‖
        ≤ ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ + ‖(Complex.digamma (s / 2) / 2 : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |y|) + 2) / 2 := add_le_add hnorm1 hnorm2
    _ = Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |y|) + 2) := by ring

/-- Tight bound for the logarithmic derivative of the gamma factor of `χ` on the line
`Re s = 2`: `‖logDeriv (gammaFactor χ) (2+iT)‖ ≤ (log π)/2 + (1/2)·(log(2+|T|) + 2)`.

This is the even/odd case split of `norm_logDeriv_Gammaℝ_le_small` at `x = 2` / `x = 3`. -/
lemma norm_logDeriv_gammaFactor_le_small {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : ℝ) :
    ‖logDeriv (gammaFactor χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext z
      exact hE.gammaFactor_def z
    have hb : ‖logDeriv Complex.Gammaℝ s‖ ≤
        Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := by
      have := norm_logDeriv_Gammaℝ_le_small 2 T (by norm_num) (by norm_num)
      simpa [s] using this
    simpa [hfun] using hb
  · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      exact hO.gammaFactor_def z
    have hsr : s.re = 2 := by
      dsimp [s]
      simp
    have hs1b : 0 < (s + 1).re := by
      have hre : (s + 1).re = s.re + 1 := by simp [Complex.add_re]
      rw [hre, hsr]
      norm_num
    have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) := differentiableAt_Gammaℝ (s + 1) hs1b
      have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
      have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
      rw [hder] at h
      simpa [Function.comp_def, mul_comm] using h
    have hb : ‖logDeriv Complex.Gammaℝ (s + 1)‖ ≤
        Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := by
      have hS : s + 1 = (3 : ℂ) + Complex.I * (T : ℂ) := by
        dsimp [s]
        ring
      rw [hS]
      exact norm_logDeriv_Gammaℝ_le_small 3 T (by norm_num) (by norm_num)
    calc
      ‖logDeriv (gammaFactor χ) s‖ = ‖logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s‖ := by
        rw [hfun]
      _ = ‖logDeriv Complex.Gammaℝ (s + 1)‖ := by rw [hldcomp]
      _ ≤ Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := hb

/-- Tight pointwise bound for the logarithmic derivative of the completed L-function on
`Re s = 2`:

`‖logDeriv (completedLFunction χ) (2+iT)‖ ≤ (1/2)·log(2+|T|) + 5` for all real `T`, for
nontrivial `χ`.

Method (tighten `Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le`, whose
constant was 20): `logDeriv Λ = logDeriv (gammaFactor χ) + logDeriv (LFunction χ)` at `2+iT`
(`LFunction_eq_completed_div_gammaFactor` + `logDeriv_fun_mul`-style; gamma factor nonzero there).
- `‖logDeriv (LFunction χ) (2+iT)‖ ≤ 3` by
  `Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_le_small`.
- `logDeriv (gammaFactor χ) (2+iT)` is `logDeriv (Gammaℝ) (2+iT)` (even) or
  `logDeriv (Gammaℝ) (3+iT)` (odd).  With `Gammaℝ s = π^(-s/2)·Gamma(s/2)`
  (`Complex.Gammaℝ_def`), `logDeriv (Gammaℝ) s = -log π/2 + (1/2)·digamma (s/2)`, so at
  `s = (2+ε)+iT` (`ε ∈ {0,1}`) its norm is at most
  `(log π)/2 + (1/2)·(log (2+|T|/2) + 2)` by
  `Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le` at `x = (2+ε)/2 ∈ {1, 3/2}`
  (⊆ [1/2,8]) and `y = T/2` (constant 2); use `log(2+|T|/2) ≤ log(2+|T|)` to get the final
  `(1/2)·log(2+|T|)` with additive `(log π)/2 + 1 + 3 ≤ 5`. -/
theorem completedLogDeriv_two_small {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (T : ℝ) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      (1 / 2) * Real.log (2 + |T|) + 5 := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hsre : 0 < s.re := by
    dsimp [s]
    simp
  have hLs0 : DirichletCharacter.LFunction χ s ≠ 0 := by
    have hlow : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
      simpa [s] using L_lower_re_two_explicit χ hχ T
    have hpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt hpos)
  have hdec := logDeriv_completedLFunction_eq_add χ hχ s hsre hLs0
  have hnormL : ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 3 := by
    rw [logDeriv_apply]
    dsimp [s]
    exact logDeriv_L_two_le_small χ hχ T
  have hnormG : ‖logDeriv (gammaFactor χ) s‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := by
    simpa [s] using norm_logDeriv_gammaFactor_le_small χ T
  have hpi_le_two : Real.log Real.pi ≤ 2 := by
    have hmono : Real.log Real.pi ≤ Real.log (4 : ℝ) := by
      apply Real.log_le_log
      · exact Real.pi_pos
      · exact le_of_lt Real.pi_lt_four
    calc
      Real.log Real.pi ≤ Real.log (4 : ℝ) := hmono
      _ = 2 * Real.log (2 : ℝ) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        rw [Real.log_pow]
        norm_num
      _ ≤ 2 := by
        have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
          linarith
        nlinarith
  have hfin : 3 + (Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2)) ≤
      (1 / 2) * Real.log (2 + |T|) + 5 := by
    nlinarith [hpi_le_two]
  have hnorm : ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖ ≤
      (1 / 2) * Real.log (2 + |T|) + 5 := by
    rw [hdec]
    exact le_trans (norm_add_le _ _) (le_trans (add_le_add hnormL hnormG) hfin)
  simpa [s] using hnorm

end Commons.NumberTheory.DirichletCharacter
