import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.horizontalGamma_logDeriv_bound
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.Analysis.Integral.norm_intervalIntegral_mul_le_gen

open Complex DirichletCharacter MeasureTheory intervalIntegral Filter
open scoped Real Topology

set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Horizontal integrals of `(logDeriv (gammaFactor χ)) · Φ`

This file proves `horizontal_logDeriv_gammaFactor_tendsto_gen`: for a function `Φ` decaying
like `M / (1 + ‖u‖ ^ 2)` in the closed half plane `Re u ≤ B ⊆ [-1/2, 2]`, the integrals of
`logDeriv (gammaFactor χ)(x ± iT) · Φ(x ± iT)` over `x ∈ [A, B]` tend to `0` as `T → ∞`.

The proof uses only a *pointwise* bound for the logarithmic derivative of the gamma factor on
the strip `Re s ∈ [-1/2, 2]`, namely `‖logDeriv (gammaFactor χ) z‖ ≤ 4 log(|Im z| + 3)`
(proved below from the digamma estimate `digamma_mid_strip_le`), together with
`intervalIntegral.norm_integral_le_of_norm_le_const`.  Combined with `‖Φ(x + iv)‖ ≤
M / (1 + v ^ 2)` this gives the bound
`‖∫_{A}^{B} (logDeriv (gammaFactor χ)) Φ‖ ≤ (4 log(|v|+3)) · (M/(1+v²)) · |B - A|`,
which is `O(log |v| / |v|²) = o(1)`.
-/

/-! ## A digamma bound on the strip `Re w ∈ [-1/4, 3/2]` -/

private lemma norm_log_GammaR_eq : ‖Complex.log (Real.pi : ℂ)‖ = Real.log Real.pi := by
  rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
  exact Complex.norm_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))

private lemma digamma_strip_bound (w : ℂ) (hw1 : -(1 / 4 : ℝ) ≤ w.re) (hw2 : w.re ≤ 3 / 2)
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
  have hdig := digamma_strip_bound (z / 2) hw1 hw2 hwi
  have hlogdiv : Real.log (2 + |(z / 2).im|) ≤ Real.log (|z.im| + 3) := by
    apply Real.log_le_log (by positivity)
    rw [im_div_two, abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [abs_nonneg z.im]
  have hnorm1 : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, norm_log_GammaR_eq]
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

/-- Pointwise bound for the logarithmic derivative of the gamma factor of a Dirichlet
character on the strip `Re z ∈ [-1/2, 2]`, `|Im z| ≥ 2`. -/
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

/-! ## The main theorem -/

/-- If `|v| ≥ 2`, the horizontal integral of `(logDeriv (gammaFactor χ)) · Φ` at height `v` is
at most `(4 log(|v|+3)) · (M/(1+v²)) · |B - A|`. -/
private lemma norm_horizontal_integral_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {A B M : ℝ} (hA : -(1 / 2 : ℝ) ≤ A) (hAB : A ≤ B) (hB2 : B ≤ 2) (hM : 0 ≤ M)
    {Φ : ℂ → ℂ} (hΦb : ∀ u : ℂ, u.re ≤ B → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2))
    {v : ℝ} (hv : 2 ≤ |v|) :
    ‖∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I) *
          Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (4 * Real.log (|v| + 3)) * (M / (1 + v ^ 2)) * |B - A| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [Set.uIoc_of_le hAB] at hx
  obtain ⟨hxA, hxB⟩ := hx
  have hre : (((x : ℂ) + (v : ℂ) * Complex.I)).re = x := by simp
  have him : (((x : ℂ) + (v : ℂ) * Complex.I)).im = v := by simp
  rw [norm_mul]
  have hF : ‖logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      4 * Real.log (|v| + 3) := by
    have h := gammaFactor_logDeriv_le χ ((x : ℂ) + (v : ℂ) * Complex.I)
      (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hv)
    simpa [him] using h
  have hPhi : ‖Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤ M / (1 + v ^ 2) := by
    have h1 := hΦb _ (by rw [hre]; exact hxB)
    have h2 : v ^ 2 ≤ ‖((x : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 := by
      have h := Complex.abs_im_le_norm ((x : ℂ) + (v : ℂ) * Complex.I)
      rw [him] at h
      nlinarith [sq_abs v, abs_nonneg v, norm_nonneg ((x : ℂ) + (v : ℂ) * Complex.I)]
    exact le_trans h1 (div_le_div_of_nonneg_left hM (by positivity) (by linarith))
  refine mul_le_mul hF hPhi (norm_nonneg _) ?_
  have h1 : (1 : ℝ) ≤ |v| + 3 := by linarith [abs_nonneg v]
  have h2 := Real.log_nonneg h1
  linarith

/-- The explicit bound of `norm_horizontal_integral_le` is dominated by `16 M |B - A| / |v|`. -/
private lemma bound_le_dom {M U v : ℝ} (hM : 0 ≤ M) (hU : 0 ≤ U) (hv : 2 ≤ |v|) :
    (4 * Real.log (|v| + 3)) * (M / (1 + v ^ 2)) * U ≤ 16 * M * U * |v|⁻¹ := by
  have hvpos : (0 : ℝ) < |v| := by linarith
  have hlog : Real.log (|v| + 3) ≤ |v| + 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < |v| + 3 by linarith)
    linarith
  have hfrac : (|v| + 3) / (1 + v ^ 2) ≤ 4 * |v|⁻¹ := by
    have hden : (0 : ℝ) < 1 + v ^ 2 := by positivity
    have hkey : (|v| + 3) * |v| ≤ 4 * (1 + v ^ 2) := by
      have h2 : |v| ≤ |v| ^ 2 := by nlinarith [hv]
      have h3 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
      nlinarith [h2, h3]
    rw [div_le_iff₀ hden]
    have hstep : |v| + 3 = (|v| + 3) * |v| * |v|⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hvpos), mul_one]
    rw [hstep]
    calc (|v| + 3) * |v| * |v|⁻¹ ≤ (4 * (1 + v ^ 2)) * |v|⁻¹ :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 4 * |v|⁻¹ * (1 + v ^ 2) := by ring
  have hstep1 : (4 * Real.log (|v| + 3)) * (M / (1 + v ^ 2)) * U ≤
      (4 * (|v| + 3)) * (M / (1 + v ^ 2)) * U := by
    have h4 : 4 * Real.log (|v| + 3) ≤ 4 * (|v| + 3) := by linarith
    have h5 : (0 : ℝ) ≤ M / (1 + v ^ 2) := div_nonneg hM (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 h5) hU
  calc (4 * Real.log (|v| + 3)) * (M / (1 + v ^ 2)) * U
      ≤ (4 * (|v| + 3)) * (M / (1 + v ^ 2)) * U := hstep1
    _ = 4 * M * U * ((|v| + 3) / (1 + v ^ 2)) := by ring
    _ ≤ 4 * M * U * (4 * |v|⁻¹) := by
        exact mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 16 * M * U * |v|⁻¹ := by ring

/-- The bound `(4 log(|v|+3)) · (M/(1+v²)) · U` tends to `0` along any filter in which
`|v| ≥ 2` eventually and `16 M U / |v| → 0`. -/
private lemma tendsto_bound_le {M U : ℝ} (hM : 0 ≤ M) (hU : 0 ≤ U) {l : Filter ℝ}
    (hl : ∀ᶠ v in l, 2 ≤ |v|)
    (hdom : Tendsto (fun v : ℝ => 16 * M * U * |v|⁻¹) l (nhds 0)) :
    Tendsto (fun v : ℝ => (4 * Real.log (|v| + 3)) * (M / (1 + v ^ 2)) * U) l (nhds 0) := by
  refine squeeze_zero' (g := fun v : ℝ => 16 * M * U * |v|⁻¹) ?_ ?_ hdom
  · filter_upwards with v
    have hlog : 0 ≤ Real.log (|v| + 3) := Real.log_nonneg (by linarith [abs_nonneg v])
    have hdiv : 0 ≤ M / (1 + v ^ 2) := div_nonneg hM (by positivity)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlog) hdiv) hU
  · filter_upwards [hl] with v hv
    exact bound_le_dom hM hU hv

/-- The horizontal integral at height `v` tends to `0` along a filter where `|v| ≥ 2` eventually
and the explicit bound tends to `0`. -/
private lemma tendsto_horizontal_integral {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {A B M : ℝ} (hA : -(1 / 2 : ℝ) ≤ A) (hAB : A ≤ B) (hB2 : B ≤ 2) (hM : 0 ≤ M)
    {Φ : ℂ → ℂ} (hΦb : ∀ u : ℂ, u.re ≤ B → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2)) {l : Filter ℝ}
    (hl : ∀ᶠ v in l, 2 ≤ |v|)
    (hlim : Tendsto (fun v : ℝ => (4 * Real.log (|v| + 3)) * (M / (1 + v ^ 2)) * |B - A|)
      l (nhds 0)) :
    Tendsto (fun v : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I) *
          Φ ((x : ℂ) + (v : ℂ) * Complex.I)) l (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (f := fun v : ℝ => ‖∫ x : ℝ in A..B,
      logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I) *
        Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖) ?_ ?_ hlim
  · filter_upwards with v
    exact norm_nonneg _
  · filter_upwards [hl] with v hv
    exact norm_horizontal_integral_le χ hA hAB hB2 hM hΦb hv

theorem horizontal_logDeriv_gammaFactor_tendsto_gen {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {A B : ℝ} (hA : -(1/2 : ℝ) ≤ A) (hAB : A ≤ B) (hB2 : B ≤ 2)
    {Φ : ℂ → ℂ} (hΦdiff : Differentiable ℂ Φ) {M : ℝ} (hM : 0 ≤ M)
    (hΦb : ∀ u : ℂ, u.re ≤ B → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2)) :
    (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (T : ℂ) * Complex.I) *
          Φ ((x : ℂ) + (T : ℂ) * Complex.I)) Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) - (T : ℂ) * Complex.I) *
          Φ ((x : ℂ) - (T : ℂ) * Complex.I)) Filter.atTop (nhds 0)) := by
  have hU : (0 : ℝ) ≤ |B - A| := abs_nonneg _
  have hl_top : ∀ᶠ v : ℝ in atTop, 2 ≤ |v| := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with v hv
    rw [abs_of_nonneg (by linarith)]
    exact hv
  have hl_bot : ∀ᶠ v : ℝ in atBot, 2 ≤ |v| := by
    filter_upwards [eventually_le_atBot (-2 : ℝ)] with v hv
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hdom_top : Tendsto (fun v : ℝ => 16 * M * |B - A| * |v|⁻¹) atTop (nhds 0) := by
    have h1 : Tendsto (fun v : ℝ => |v|⁻¹) atTop (nhds 0) :=
      (tendsto_abs_atTop_atTop (G := ℝ)).inv_tendsto_atTop
    simpa using h1.const_mul (16 * M * |B - A|)
  have hdom_bot : Tendsto (fun v : ℝ => 16 * M * |B - A| * |v|⁻¹) atBot (nhds 0) := by
    have h1 : Tendsto (fun v : ℝ => |v|⁻¹) atBot (nhds 0) :=
      (tendsto_abs_atBot_atTop (G := ℝ)).inv_tendsto_atTop
    simpa using h1.const_mul (16 * M * |B - A|)
  have hTop : Tendsto (fun v : ℝ => ∫ x : ℝ in A..B,
      logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I) *
        Φ ((x : ℂ) + (v : ℂ) * Complex.I)) atTop (nhds 0) :=
    tendsto_horizontal_integral χ hA hAB hB2 hM hΦb hl_top
      (tendsto_bound_le hM hU hl_top hdom_top)
  have hBot : Tendsto (fun v : ℝ => ∫ x : ℝ in A..B,
      logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + (v : ℂ) * Complex.I) *
        Φ ((x : ℂ) + (v : ℂ) * Complex.I)) atBot (nhds 0) :=
    tendsto_horizontal_integral χ hA hAB hB2 hM hΦb hl_bot
      (tendsto_bound_le hM hU hl_bot hdom_bot)
  constructor
  · simpa using hTop
  · have hcomp : Tendsto (fun T : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) *
          Φ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) atTop (nhds 0) := by
      exact hBot.comp tendsto_neg_atTop_atBot
    have hfe : (fun T : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) - (T : ℂ) * Complex.I) *
          Φ ((x : ℂ) - (T : ℂ) * Complex.I))
        = (fun T : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.gammaFactor χ) ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) *
          Φ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
      funext T
      apply intervalIntegral.integral_congr
      intro x _
      have hcast : (x : ℂ) - (T : ℂ) * Complex.I = (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      simp only [hcast]
    rw [hfe]
    exact hcomp

end Commons.NumberTheory.DirichletCharacter
