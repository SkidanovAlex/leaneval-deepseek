import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_le_small
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Tight pointwise bounds for logarithmic derivatives of completed L-functions

Helpers for the main theorem `completedLogDeriv_neg_one_small`, mirroring the
arguments of `Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le`
but with the tighter `digamma_mid_strip_le` (constant 2) and the sharp bound
`logDeriv_L_two_le_small` (constant 3), to obtain constant `5` instead of `20`.
-/

/-- Sharpened version of `norm_logDeriv_Gammaℝ_le`: for `1 ≤ x ≤ 16` and all real `y`,
`‖logDeriv Gammaℝ (x + iy)‖ ≤ (log π)/2 + (1/2)·(log (2 + |y|) + 2)`.

The proof is identical to `norm_logDeriv_Gammaℝ_le` except that the digamma estimate
`digamma_vertical_bound` (constant 8) is replaced by `digamma_mid_strip_le` (constant 2),
valid since `x/2 ∈ [1/2, 8]` whenever `1 ≤ x ≤ 16`. -/
private lemma norm_logDeriv_Gammaℝ_small_aux (x y : ℝ) (hx1 : (1 : ℝ) ≤ x) (hx2 : x ≤ 16) :
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
    have : ‖Complex.digamma (s / 2)‖ / ‖(2 : ℂ)‖ ≤ (Real.log (2 + |y|) + 2) / 2 := by
      norm_num
      exact hdg''
    simpa using this
  calc
    ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 : ℂ)‖
        ≤ ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ + ‖(Complex.digamma (s / 2) / 2 : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |y|) + 2) / 2 := add_le_add hnorm1 hnorm2
    _ = Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |y|) + 2) := by ring

/-- Sharpened version of `norm_logDeriv_gammaFactor_le`, using
`norm_logDeriv_Gammaℝ_small_aux` in place of `norm_logDeriv_Gammaℝ_le`:
`‖logDeriv (gammaFactor χ) (2 + iT)‖ ≤ (log π)/2 + (1/2)·(log (2 + |T|) + 2)`. -/
private lemma norm_logDeriv_gammaFactor_small_aux {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖logDeriv (gammaFactor χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext z
      exact hE.gammaFactor_def z
    have hb : ‖logDeriv Complex.Gammaℝ s‖ ≤
        Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := by
      have := norm_logDeriv_Gammaℝ_small_aux 2 T (by norm_num) (by norm_num)
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
      exact norm_logDeriv_Gammaℝ_small_aux 3 T (by norm_num) (by norm_num)
    calc
      ‖logDeriv (gammaFactor χ) s‖ = ‖logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s‖ := by
        rw [hfun]
      _ = ‖logDeriv Complex.Gammaℝ (s + 1)‖ := by rw [hldcomp]
      _ ≤ Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2) := hb

/-- Tight pointwise bound on the line `Re s = 2` with constant `5`:
`‖logDeriv (completedLFunction χ) (2+iT)‖ ≤ (1/2)·log (2 + |T|) + 5` for nontrivial `χ`.

Method (tighten `completedLogDeriv_two_le`, whose constant was 20): decompose
`logDeriv Λ = logDeriv L + logDeriv γ` (`logDeriv_completedLFunction_eq_add`, gamma factor
nonzero by `L_lower_re_two_explicit`), bound `‖logDeriv L‖ ≤ 3` by `logDeriv_L_two_le_small`,
and bound `‖logDeriv γ‖ ≤ (log π)/2 + (1/2)·(log (2+|T|) + 2)` by
`norm_logDeriv_gammaFactor_small_aux`.  Adding gives `(1/2)·log(2+|T|) + (log π)/2 + 4 ≤
(1/2)·log(2+|T|) + 5` since `log π ≤ 2`. -/
private lemma completedLogDeriv_two_small_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (T : ℝ) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      (1 / 2) * Real.log (2 + |T|) + 5 := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hsre : 0 < s.re := by
    dsimp [s]
    simp
  have hLs0 : DirichletCharacter.LFunction χ s ≠ 0 := by
    have hnorm : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
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
    simpa [s] using norm_logDeriv_gammaFactor_small_aux χ T
  have hnorm : ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖ ≤
      3 + (Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2)) := by
    rw [hdec]
    exact le_trans (norm_add_le _ _) (add_le_add hnormL hnormG)
  have hpi : Real.log Real.pi ≤ 2 := by
    have hle4 : Real.log Real.pi ≤ Real.log (4 : ℝ) :=
      Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    calc
      Real.log Real.pi ≤ Real.log (4 : ℝ) := hle4
      _ = 2 * Real.log (2 : ℝ) := Real.log_four_eq
      _ ≤ 2 := by nlinarith [Real.log_two_lt_d9]
  have hfin : 3 + (Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |T|) + 2)) ≤
      (1 / 2) * Real.log (2 + |T|) + 5 := by
    nlinarith
  simpa [s] using le_trans hnorm hfin

/-- Tight pointwise bound for the logarithmic derivative of the completed L-function on
`Re s = -1`:

`‖logDeriv (completedLFunction χ) (-1+iT)‖ ≤ log N + (1/2)·log(2+|T|) + 5` for all real `T`,
for primitive nontrivial `χ`.

Method: apply `Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe` at `s = -1+iT`
(hypotheses discharge by `zerosInStrip` exactly as in
`Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_le`, whose constant was 20),
giving `logDeriv Λ(χ)(-1+iT) = -log N - logDeriv Λ(χ⁻¹)(2-iT)`; then bound the second term by
the tight Re=2 bound for `χ⁻¹` (`completedLogDeriv_two_small_aux`): `‖logDeriv Λ(χ⁻¹)(2-iT)‖ ≤
(1/2)·log(2+|T|) + 5`, and use the triangle inequality. -/
theorem completedLogDeriv_neg_one_small {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T|) + 5 := by
  set s : ℂ := (-1 : ℂ) + Complex.I * (T : ℂ) with hsdef
  have hsre : s.re = -1 := by
    simp [hsdef]
  -- χ⁻¹ is nontrivial
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  -- `completedLFunction χ s ≠ 0`: a zero at Re s = -1 would lie outside the critical strip.
  have hΛ : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro hz
    have hstrip := zerosInStrip χ hχ hχprim s hz
    have hlt : (0 : ℝ) < (-1 : ℝ) := by simpa [hsre] using hstrip.1
    exact (not_lt_of_ge (by norm_num : (-1 : ℝ) ≤ 0)) hlt
  -- `completedLFunction χ⁻¹ (1 - s) ≠ 0`: Re (1 - s) = 2 ≥ 1, and nontrivial L-functions
  -- do not vanish on Re s ≥ 1 (quotient by the nonzero gamma factor).
  have hre1s : 1 ≤ (1 - s : ℂ).re := by
    rw [Complex.sub_re, hsre]
    norm_num
  have hw0 : (1 : ℂ) - s ≠ 0 := by
    intro hz
    have hle : (1 : ℝ) ≤ 0 := by
      simpa [hz] using hre1s
    norm_num at hle
  have hΛc : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
    intro hz
    have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹)
      (1 - s) (Or.inl hw0)
    have hL : DirichletCharacter.LFunction (χ⁻¹) (1 - s) = 0 := by
      rw [hdiv, hz]
      simp
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ⁻¹) (Or.inl hχinv) hre1s) hL
  -- The functional equation in log-derivative form
  have hfe := completedLogDeriv_fe χ hχprim s hΛ hΛc
  -- Bound the second summand using the tight Re = 2 bound at `-T`
  have hb2 : ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹))
        ((2 : ℂ) + Complex.I * ((-T : ℝ) : ℂ))‖ ≤
      (1 / 2) * Real.log (2 + |(-T : ℝ)|) + 5 := by
    exact completedLogDeriv_two_small_aux (χ := χ⁻¹) hχinv (-T)
  have harg : (2 : ℂ) + Complex.I * ((-T : ℝ) : ℂ) = (1 : ℂ) - s := by
    simp [hsdef]
    ring
  have hb2' : ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)‖ ≤
      (1 / 2) * Real.log (2 + |T|) + 5 := by
    rw [harg] at hb2
    simpa [abs_neg] using hb2
  -- log N ≥ 0, hence ‖-((log N : ℝ) : ℂ)‖ = log N
  have hN1 : 1 ≤ (N : ℝ) := by
    have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1nat : 1 ≤ N := by omega
    exact_mod_cast hN1nat
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hnorm1 : ‖-((Real.log (N : ℝ) : ℂ))‖ ≤ Real.log (N : ℝ) := by
    rw [norm_neg, Complex.norm_of_nonneg hlogN_nonneg]
  -- triangle inequality
  have hmain : ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖ ≤
      Real.log (N : ℝ) + ((1 / 2) * Real.log (2 + |T|) + 5) := by
    calc
      ‖logDeriv (DirichletCharacter.completedLFunction χ) s‖
          = ‖-((Real.log (N : ℝ) : ℂ)) -
                logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)‖ := by
              rw [hfe]
      _ ≤ ‖-((Real.log (N : ℝ) : ℂ))‖ +
            ‖logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s)‖ := by
            simpa [sub_eq_add_neg, norm_neg] using
              (norm_add_le (-((Real.log (N : ℝ) : ℂ)))
                (-(logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) ((1 : ℂ) - s))))
      _ ≤ Real.log (N : ℝ) + ((1 / 2) * Real.log (2 + |T|) + 5) := by
            exact add_le_add hnorm1 hb2'
  simpa [hsdef, add_assoc] using hmain

end Commons.NumberTheory.DirichletCharacter
