import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole

open Complex DirichletCharacter MeasureTheory intervalIntegral
open scoped Real Topology

set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Horizontal bound for the logarithmic derivative of the Archimedean gamma factor

We prove that for every Dirichlet character `χ` modulo `N` the integral of
`‖logDeriv (gammaFactor χ)(x ± iT)‖` over `x ∈ [-1/2, 2]` is `O(log (N (T+3)))`, uniformly
in `T ≥ 2`.

The pointwise input is the classical (pseudo-)functional equation for the gamma factor:
for `z` not a pole of `Γℝ`,

  `logDeriv Γℝ z = -log π / 2 + ψ(z/2)/2`

(`ψ` the digamma function).  On the strip `Re z ∈ [-1/2, 3]` with `|Im z| ≥ 2` this reduces
the bound to a digamma estimate in the region `Re w ∈ [-1/4, 3/2]`, `|Im w| ≥ 1`, which we
obtain from the mid-strip estimate `digamma_mid_strip_le` by shifting once
(`ψ(w) = ψ(w+1) - 1/w`).
-/

private lemma norm_log_Gammaℝ_eq : ‖Complex.log (Real.pi : ℂ)‖ = Real.log Real.pi := by
  rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
  exact Complex.norm_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))

/-! ## A digamma bound on the strip `Re w ∈ [-1/4, 3/2]` -/

/-- For `Re w ∈ [-1/4, 3/2]` and `|Im w| ≥ 1` we have `‖ψ(w)‖ ≤ log (2 + |Im w|) + 4`. -/
private lemma digamma_norm_le_strip (w : ℂ) (hw1 : -(1 / 4 : ℝ) ≤ w.re) (hw2 : w.re ≤ 3 / 2)
    (hwi : 1 ≤ |w.im|) : ‖Complex.digamma w‖ ≤ Real.log (2 + |w.im|) + 4 := by
  by_cases hmid : (1 / 2 : ℝ) ≤ w.re
  · have hd := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le w.re w.im hmid
      (by linarith)
    have heq : ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I = w := by
      apply Complex.ext <;> simp
    rw [heq] at hd
    linarith
  · simp only [not_le] at hmid
    have hwne : ∀ m : ℕ, w ≠ -(m : ℂ) := by
      intro m hm
      have him : w.im = 0 := by rw [hm]; simp
      rw [him] at hwi
      simp only [abs_zero] at hwi
      linarith
    have hw1ne : ∀ m : ℕ, w + 1 ≠ -(m : ℂ) := by
      intro m hm
      have him : (w + 1).im = 0 := by rw [hm]; simp
      simp only [Complex.add_im, Complex.one_im, add_zero] at him
      rw [him] at hwi
      simp only [abs_zero] at hwi
      linarith
    have hr1 := Complex.digamma_apply_add_one w hwne
    have hr2 := Complex.digamma_apply_add_one (w + 1) hw1ne
    have hr2' : Complex.digamma (w + 2) = Complex.digamma (w + 1) + (w + 1)⁻¹ := by
      have h := hr2
      rwa [show w + 1 + 1 = w + 2 by ring] at h
    have hshift : Complex.digamma w = Complex.digamma (w + 2) - (w + 1)⁻¹ - w⁻¹ := by
      rw [hr2', hr1]; ring
    have harg : w + 2 = (((w.re + 2 : ℝ)) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hmidb : ‖Complex.digamma (w + 2)‖ ≤ Real.log (2 + |w.im|) + 2 := by
      rw [harg]
      exact Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le (w.re + 2) w.im
        (by linarith) (by linarith)
    have hinvw : ‖w⁻¹‖ ≤ 1 := by
      have h1 : (1 : ℝ) ≤ ‖w‖ := le_trans hwi (Complex.abs_im_le_norm w)
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h1
    have hinvw1 : ‖(w + 1)⁻¹‖ ≤ 1 := by
      have him1 : (w + 1).im = w.im := by simp
      have h1 : (1 : ℝ) ≤ ‖w + 1‖ := by
        have h := Complex.abs_im_le_norm (w + 1)
        rw [him1] at h
        exact le_trans hwi h
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h1
    calc ‖Complex.digamma w‖ = ‖Complex.digamma (w + 2) - (w + 1)⁻¹ - w⁻¹‖ := by rw [hshift]
      _ ≤ ‖Complex.digamma (w + 2)‖ + ‖(w + 1)⁻¹‖ + ‖w⁻¹‖ := by
            have h1 : ‖Complex.digamma (w + 2) - (w + 1)⁻¹ - w⁻¹‖ ≤
                ‖Complex.digamma (w + 2) - (w + 1)⁻¹‖ + ‖w⁻¹‖ := norm_sub_le _ _
            have h2 : ‖Complex.digamma (w + 2) - (w + 1)⁻¹‖ ≤
                ‖Complex.digamma (w + 2)‖ + ‖(w + 1)⁻¹‖ := norm_sub_le _ _
            linarith
      _ ≤ Real.log (2 + |w.im|) + 2 + 1 + 1 := by linarith
      _ = Real.log (2 + |w.im|) + 4 := by ring

/-! ## The bound for `Γℝ` and for the gamma factor -/

/-- `‖logDeriv Γℝ z‖ ≤ 4 log(|Im z| + 3)` on the strips `Re z ∈ [-1/2, 3]`, `|Im z| ≥ 2`. -/
private lemma GammaR_logDeriv_le (z : ℂ) (hz1 : -(1 / 2 : ℝ) ≤ z.re) (hz2 : z.re ≤ 3)
    (hzi : 2 ≤ |z.im|) :
    ‖logDeriv Complex.Gammaℝ z‖ ≤ 4 * Real.log (|z.im| + 3) := by
  have hz2ne : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have him : (z / 2).im = 0 := by rw [hm]; simp
    rw [im_div_two] at him
    have hz0 : z.im = 0 := by linarith
    rw [hz0] at hzi
    simp only [abs_zero] at hzi
    linarith
  have hform := Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole z hz2ne
  have hw1 : -(1 / 4 : ℝ) ≤ (z / 2).re := by rw [re_div_two]; linarith
  have hw2 : (z / 2).re ≤ 3 / 2 := by rw [re_div_two]; linarith
  have hwi : 1 ≤ |(z / 2).im| := by
    rw [im_div_two, abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith
  have hdig := digamma_norm_le_strip (z / 2) hw1 hw2 hwi
  have hlogdiv : Real.log (2 + |(z / 2).im|) ≤ Real.log (|z.im| + 3) := by
    apply Real.log_le_log (by positivity)
    rw [im_div_two, abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [abs_nonneg z.im]
  have hnorm1 : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, norm_log_Gammaℝ_eq]
    norm_num
  have hpi : Real.log Real.pi / 2 ≤ 1 := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlep : Real.log Real.pi ≤ 2 * Real.log 2 := by
      rw [← hlog4]
      exact Real.log_le_log (by positivity) (by linarith [Real.pi_lt_four])
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  have hlogt : (1 : ℝ) ≤ Real.log (|z.im| + 3) := by
    have h5 : (5 : ℝ) ≤ |z.im| + 3 := by linarith
    have he : Real.exp 1 ≤ 5 := by
      have := Real.exp_one_lt_d9
      linarith
    have hlog5 : (1 : ℝ) ≤ Real.log 5 := by
      rw [Real.le_log_iff_exp_le (show (0 : ℝ) < 5 by norm_num)]
      exact he
    exact le_trans hlog5 (Real.log_le_log (show (0 : ℝ) < 5 by norm_num) h5)
  rw [hform]
  have hb : ‖-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2‖ ≤
      Real.log Real.pi / 2 + (Real.log (|z.im| + 3) + 4) / 2 := by
    refine le_trans (norm_add_le _ _) ?_
    rw [hnorm1]
    have hd2 : ‖Complex.digamma (z / 2) / 2‖ ≤ (Real.log (|z.im| + 3) + 4) / 2 := by
      rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      exact div_le_div_of_nonneg_right (le_trans hdig (by linarith [hlogdiv])) (by norm_num)
    linarith
  refine le_trans hb ?_
  nlinarith [hpi, hlogt]

/-- `‖logDeriv (gammaFactor χ) z‖ ≤ 4 log(|Im z| + 3)` for `Re z ∈ [-1/2, 2]`, `|Im z| ≥ 2`. -/
private lemma gammaFactor_logDeriv_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ)
    (hz1 : -(1 / 2 : ℝ) ≤ z.re) (hz2 : z.re ≤ 2) (hzi : 2 ≤ |z.im|) :
    ‖logDeriv (DirichletCharacter.gammaFactor χ) z‖ ≤ 4 * Real.log (|z.im| + 3) := by
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    rw [hfun]
    exact GammaR_logDeriv_le z hz1 (by linarith) hzi
  · have hfun : DirichletCharacter.gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) :=
      funext hO.gammaFactor_def
    rw [hfun]
    have hld : logDeriv (fun w : ℂ => Complex.Gammaℝ (w + 1)) z =
        logDeriv Complex.Gammaℝ (z + 1) := by
      have hre1 : 0 < (z + 1).re := by
        rw [Complex.add_re]; simp; linarith
      have hf : DifferentiableAt ℂ Complex.Gammaℝ (z + 1) := differentiableAt_Gammaℝ (z + 1) hre1
      have hg : DifferentiableAt ℂ (fun w : ℂ => w + 1) z := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun w : ℂ => w + 1) (x := z) hf hg
      have hder : deriv (fun w : ℂ => w + 1) z = 1 := by simp
      rw [hder, mul_one] at h
      simpa [Function.comp_def] using h
    rw [hld]
    have h1 : -(1 / 2 : ℝ) ≤ (z + 1).re := by rw [Complex.add_re]; simp; linarith
    have h2 : (z + 1).re ≤ 3 := by rw [Complex.add_re]; simp; linarith
    have h3 : 2 ≤ |(z + 1).im| := by rw [Complex.add_im]; simp; exact hzi
    have := GammaR_logDeriv_le (z + 1) h1 h2 h3
    simpa using this

/-! ## The integral bound -/

/-- For `|v| ≥ 2`, the integral over `x ∈ [-1/2, 2]` of the logarithmic derivative of the
gamma factor at `x + i v` is at most `10 log(|v| + 3)`. -/
private lemma horizontal_integral_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {v : ℝ} (hv : 2 ≤ |v|) :
    (∫ x : ℝ in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) ≤ 10 * Real.log (|v| + 3) := by
  have hab : (-1 / 2 : ℝ) ≤ 2 := by norm_num
  have hnn : 0 ≤ ∫ x : ℝ in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
      ((x : ℂ) + (v : ℂ) * Complex.I)‖ :=
    intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
  have hbound : ∀ x : ℝ, x ∈ Set.uIoc (-1 / 2) 2 →
      ‖‖logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖‖
        ≤ 4 * Real.log (|v| + 3) := by
    intro x hx
    have hx1 : -(1 / 2 : ℝ) ≤ x := by
      rcases Set.mem_uIoc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith
    have hx2 : x ≤ 2 := by
      rcases Set.mem_uIoc.mp hx with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2
      · linarith
    have hzre : ((x : ℂ) + (v : ℂ) * Complex.I).re = x := by simp
    have hzim : ((x : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h := gammaFactor_logDeriv_le χ ((x : ℂ) + (v : ℂ) * Complex.I)
      (by rw [hzre]; exact hx1) (by rw [hzre]; exact hx2) (by rw [hzim]; exact hv)
    rwa [hzim] at h
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 / 2 : ℝ)) (b := 2)
    (C := 4 * Real.log (|v| + 3))
    (f := fun x : ℝ => ‖logDeriv (DirichletCharacter.gammaFactor χ)
      ((x : ℂ) + (v : ℂ) * Complex.I)‖) hbound
  have heq : (∫ x : ℝ in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
      ((x : ℂ) + (v : ℂ) * Complex.I)‖) =
      ‖∫ x : ℝ in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
      ((x : ℂ) + (v : ℂ) * Complex.I)‖‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [heq]
  calc ‖∫ x : ℝ in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖‖
      ≤ (4 * Real.log (|v| + 3)) * |2 - (-1 / 2)| := hnorm
    _ = 10 * Real.log (|v| + 3) := by
        have h52 : |(2 : ℝ) - (-1 / 2)| = 5 / 2 := by norm_num
        rw [h52]; ring

/-! ## Main theorem -/

theorem horizontalGamma_logDeriv_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ((∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
            ((x : ℂ) + (T : ℂ) * Complex.I)‖) ≤ C * Real.log (N * (T + 3))) ∧
      ((∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
            ((x : ℂ) - (T : ℂ) * Complex.I)‖) ≤ C * Real.log (N * (T + 3))) := by
  refine ⟨10, by norm_num, fun T hT => ⟨?_, ?_⟩⟩
  · have hv : 2 ≤ |T| := by rw [abs_of_nonneg (by linarith)]; exact hT
    have h1 := horizontal_integral_le χ (v := T) hv
    have hN : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
    have hlog2 : Real.log (T + 3) ≤ Real.log ((N : ℝ) * (T + 3)) := by
      apply Real.log_le_log (by linarith)
      nlinarith
    calc (∫ x : ℝ in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
          ((x : ℂ) + (T : ℂ) * Complex.I)‖)
        ≤ 10 * Real.log (|T| + 3) := h1
      _ = 10 * Real.log (T + 3) := by rw [abs_of_nonneg (by linarith)]
      _ ≤ 10 * Real.log ((N : ℝ) * (T + 3)) := by linarith
  · have hv : 2 ≤ |-T| := by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hT
    have h1 := horizontal_integral_le χ (v := -T) hv
    have harg : ∀ x : ℝ, (x : ℂ) - (T : ℂ) * Complex.I = (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
      intro x; push_cast; ring
    have hfun : (fun x : ℝ => ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((x : ℂ) - (T : ℂ) * Complex.I)‖) =
        (fun x : ℝ => ‖logDeriv (DirichletCharacter.gammaFactor χ)
        ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖) := by
      funext x; rw [harg x]
    rw [hfun]
    have hN : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
    have hlog2 : Real.log (T + 3) ≤ Real.log ((N : ℝ) * (T + 3)) := by
      apply Real.log_le_log (by linarith)
      nlinarith
    calc (∫ x : ℝ in (-1 / 2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ)
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖)
        ≤ 10 * Real.log (|-T| + 3) := h1
      _ = 10 * Real.log (T + 3) := by rw [abs_neg, abs_of_nonneg (by linarith)]
      _ ≤ 10 * Real.log ((N : ℝ) * (T + 3)) := by linarith

end Commons.NumberTheory.DirichletCharacter
