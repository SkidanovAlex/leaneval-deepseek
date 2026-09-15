import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedL_fe_transfer
import Submission.Commons.NumberTheory.DirichletCharacter.leftHalf_avg.logDeriv_completedL_eq_add_re_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.isPrimitive_inv
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_ge_three_halves_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_lim_log_sub_sum_inv

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ## Norms of `sin`/`cos` at a point with real part `±π/4` -/

private lemma normSq_sin_ofReal_add_I (x y : ℝ) :
    Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)) =
      Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [show ((Real.sin x : ℝ) : ℂ) * ((Real.cosh y : ℝ) : ℂ)
        + ((Real.cos x : ℝ) : ℂ) * ((Real.sinh y : ℝ) : ℂ) * Complex.I
      = ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.normSq_add_mul_I]
  nlinarith [Real.cosh_sq y, Real.sin_sq_add_cos_sq x]

private lemma normSq_cos_ofReal_add_I (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)) =
      Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [show ((Real.cos x : ℝ) : ℂ) * ((Real.cosh y : ℝ) : ℂ)
        - ((Real.sin x : ℝ) : ℂ) * ((Real.sinh y : ℝ) : ℂ) * Complex.I
      = ((Real.cos x * Real.cosh y : ℝ) : ℂ) + ((-(Real.sin x * Real.sinh y) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.normSq_add_mul_I]
  nlinarith [Real.cosh_sq y, Real.sin_sq_add_cos_sq x]

private lemma sqrt_two_div_two_sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `(x + iy) / 2 = (x/2) + i(y/2)`, with the halves kept as real casts. -/
private lemma div_two_add_I (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * Complex.I) / 2 =
      ((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.div_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.normSq_apply] <;> ring

/-- `((x + iy) + 1) / 2 = ((x+1)/2) + i(y/2)`, with the halves kept as real casts. -/
private lemma add_one_div_two_add_I (x y : ℝ) :
    (((x : ℂ) + (y : ℂ) * Complex.I) + 1) / 2 =
      (((x + 1) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.div_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.normSq_apply] <;> ring

/-! ## The reflection formula for the digamma function -/

/-- Reflection formula for the digamma function: for `z` which is not a pole of `Γ` and
whose reflexion `1 - z` is also not a pole,
`ψ(z) - ψ(1 - z) = -π · cot(π z)`. -/
private lemma digamma_sub_digamma_one_sub (z : ℂ) (hz : ∀ m : ℕ, z ≠ -(m : ℂ))
    (hz1 : ∀ m : ℕ, 1 - z ≠ -(m : ℂ)) :
    Complex.digamma z - Complex.digamma (1 - z) =
      -((Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * z) /
        Complex.sin ((Real.pi : ℂ) * z))) := by
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro h
    have hL : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz
    have hR : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero hz1
    have hprod := Complex.Gamma_mul_Gamma_one_sub z
    rw [h, div_zero] at hprod
    exact mul_ne_zero hL hR hprod
  have hfun : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w)) =
      (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by
    funext w
    exact Complex.Gamma_mul_Gamma_one_sub w
  have h1 : logDeriv (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w)) z =
      Complex.digamma z - Complex.digamma (1 - z) := by
    have hd1 : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hz
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) z := by
      have : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
      exact (Complex.differentiableAt_Gamma (1 - z) hz1).comp z this
    have hmul := logDeriv_mul (x := z) (f := Complex.Gamma)
      (g := fun w : ℂ => Complex.Gamma (1 - w))
      (Complex.Gamma_ne_zero hz) (Complex.Gamma_ne_zero hz1) hd1 hd2
    have hcomp : logDeriv (fun w : ℂ => Complex.Gamma (1 - w)) z =
        -Complex.digamma (1 - z) := by
      have h := logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ => 1 - w) (x := z)
        (Complex.differentiableAt_Gamma (1 - z) hz1) (by fun_prop)
      have hder : deriv (fun w : ℂ => 1 - w) z = -1 := by simp [deriv_const_sub_id]
      rw [hder] at h
      rw [Function.comp_def] at h
      rw [h, Complex.digamma_def]
      ring
    rw [hcomp] at hmul
    rw [hmul, Complex.digamma_def]
    ring
  have h2 : logDeriv (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) z =
      -((Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * z) /
        Complex.sin ((Real.pi : ℂ) * z))) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hd1 : DifferentiableAt ℂ (fun _ : ℂ => (Real.pi : ℂ)) z := differentiableAt_const _
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z :=
      differentiableAt_sin.comp z (by fun_prop)
    have hdiv := logDeriv_div (x := z) (f := fun _ : ℂ => (Real.pi : ℂ))
      (g := fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) hpi hsin hd1 hd2
    have hlogs : logDeriv (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z =
        (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * z) /
          Complex.sin ((Real.pi : ℂ) * z)) := by
      have h := logDeriv_comp (f := Complex.sin) (g := fun w : ℂ => (Real.pi : ℂ) * w) (x := z)
        differentiableAt_sin (by fun_prop)
      have hder : deriv (fun w : ℂ => (Real.pi : ℂ) * w) z = (Real.pi : ℂ) := by simp
      rw [hder] at h
      rw [Function.comp_def] at h
      rw [h, logDeriv_apply, Complex.deriv_sin]
      ring
    have hlogc : logDeriv (fun _ : ℂ => (Real.pi : ℂ)) z = 0 := by
      simp [logDeriv_apply]
    rw [hlogc, hlogs] at hdiv
    rw [hdiv]
    ring
  rw [← h1, ← h2]
  exact congrArg (fun f : ℂ → ℂ => logDeriv f z) hfun

/-! ## The digamma function at `-1/4 + i T/2` -/

private lemma sqrt2_div_two_sq' : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := sqrt_two_div_two_sq

/-- Bound for the digamma function at the point `-1/4 + iT/2`, obtained from the reflection
formula `ψ(w) = ψ(1-w) - π cot(πw)` with `1 - w = 5/4 - iT/2` in the right half-strip, and
`‖cot(πw)‖ = 1` because `Re w = -1/4` is a zero of `sin² - cos²`. -/
private lemma digamma_neg_quarter_bound (T : ℝ) :
    ‖Complex.digamma (-(1 / 4 : ℂ) + (T : ℂ) * Complex.I / 2)‖ ≤
      Real.log (2 + |T|) + 12 := by
  set w : ℂ := -(1 / 4 : ℂ) + (T : ℂ) * Complex.I / 2 with hw
  have hwre : w.re = -(1 / 4 : ℝ) := by
    rw [hw]; simp [Complex.add_re, Complex.mul_re]
  have hwne : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m hm
    have h2 : (m : ℝ) = 1 / 4 := by
      have := congrArg Complex.re hm
      rw [hwre] at this
      simp at this
      linarith
    have h4 : ((4 * m : ℕ) : ℝ) = 1 := by
      have : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
      rw [this, h2]; norm_num
    have h4' : 4 * m = 1 := by exact_mod_cast h4
    omega
  have hcwre : (1 - w).re = (5 / 4 : ℝ) := by
    rw [hw]; simp [Complex.add_re, Complex.mul_re]; norm_num
  have hcwne : ∀ m : ℕ, 1 - w ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg Complex.re hm
    rw [hcwre] at this
    simp at this
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have harg : (Real.pi : ℂ) * w =
      ((-(Real.pi / 4) : ℝ) : ℂ) + (((Real.pi * T / 2) : ℝ) : ℂ) * Complex.I := by
    rw [hw]; push_cast; ring
  have hsinsq : Complex.normSq (Complex.sin ((Real.pi : ℂ) * w)) =
      (Real.sin (Real.pi / 4)) ^ 2 + Real.sinh (Real.pi * T / 2) ^ 2 := by
    rw [harg, normSq_sin_ofReal_add_I, Real.sin_neg, neg_sq]
  have hcossq : Complex.normSq (Complex.cos ((Real.pi : ℂ) * w)) =
      (Real.cos (Real.pi / 4)) ^ 2 + Real.sinh (Real.pi * T / 2) ^ 2 := by
    rw [harg, normSq_cos_ofReal_add_I, Real.cos_neg]
  have hsinne : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro h
    have h0 : Complex.normSq (Complex.sin ((Real.pi : ℂ) * w)) = 0 := by
      rw [h]; simp [Complex.normSq]
    rw [hsinsq, Real.sin_pi_div_four, sqrt_two_div_two_sq] at h0
    nlinarith [sq_nonneg (Real.sinh (Real.pi * T / 2))]
  have hcot : ‖Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w)‖ = 1 := by
    rw [norm_div]
    have heq : ‖Complex.cos ((Real.pi : ℂ) * w)‖ = ‖Complex.sin ((Real.pi : ℂ) * w)‖ := by
      have hsq : ‖Complex.sin ((Real.pi : ℂ) * w)‖ ^ 2 =
          ‖Complex.cos ((Real.pi : ℂ) * w)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hsinsq, hcossq,
          Real.sin_pi_div_four, Real.cos_pi_div_four]
      nlinarith [norm_nonneg (Complex.sin ((Real.pi : ℂ) * w)),
        norm_nonneg (Complex.cos ((Real.pi : ℂ) * w))]
    rw [heq, div_self (norm_ne_zero_iff.mpr hsinne)]
  have href := digamma_sub_digamma_one_sub w hwne hcwne
  have hpsi : Complex.digamma w = Complex.digamma (1 - w) -
      (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w)) := by
    linear_combination (norm := ring) href
  have h1w : 1 - w = ((5 / 4 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I := by
    rw [hw]; push_cast; ring
  have hdg : ‖Complex.digamma (1 - w)‖ ≤ Real.log (2 + |T|) + 8 := by
    rw [h1w]
    have hb := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      (5 / 4) (-(T / 2)) (by norm_num) (by norm_num)
    have hlog : Real.log (2 + |-(T / 2)|) ≤ Real.log (2 + |T|) := by
      apply Real.log_le_log (by positivity)
      have h1 : |-(T / 2)| ≤ |T| := by
        rw [abs_neg, abs_div]
        have h2 : |(2 : ℝ)| = 2 := by norm_num
        rw [h2]
        have := abs_nonneg T
        linarith
      linarith
    linarith
  have hpinorm : ‖(Real.pi : ℂ) *
      (Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w))‖ = Real.pi := by
    rw [norm_mul, hcot, mul_one]
    simpa using Complex.norm_of_nonneg (le_of_lt Real.pi_pos)
  calc ‖Complex.digamma w‖
      = ‖Complex.digamma (1 - w) -
          (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w))‖ := by
        rw [hpsi]
    _ ≤ ‖Complex.digamma (1 - w)‖ +
          ‖(Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w))‖ :=
        norm_sub_le _ _
    _ ≤ (Real.log (2 + |T|) + 8) + Real.pi := by rw [hpinorm]; linarith
    _ ≤ Real.log (2 + |T|) + 12 := by linarith [Real.pi_lt_four]

/-! ## The logarithmic derivative of `Γℝ` away from its poles -/

/-- `logDeriv Γℝ z = -log π / 2 + ψ(z/2)/2` whenever `z/2` is not a pole of `Γ`
(equivalently `z` is not a non-positive even integer). -/
private lemma logDeriv_Gammaℝ_formula_off_pole (z : ℂ) (hz : ∀ m : ℕ, z / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ z =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2 := by
  let f : ℂ → ℂ := fun w => (Real.pi : ℂ) ^ (-w / 2)
  let g : ℂ → ℂ := fun w => Complex.Gamma (w / 2)
  have hc : (Real.pi : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    exact Real.pi_pos
  have hcpow_ne : ∀ w : ℂ, (Real.pi : ℂ) ^ (-w / 2) ≠ 0 := by
    intro w
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hldf : logDeriv f z = -(Complex.log (Real.pi : ℂ)) / 2 := by
    dsimp [f]
    have hinner : DifferentiableAt ℂ (fun w : ℂ => -w / 2) z := by fun_prop
    have hld := logDeriv_comp (f := fun w : ℂ => (Real.pi : ℂ) ^ w)
      (g := fun w : ℂ => -w / 2) (x := z)
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ w) (-z / 2)) hinner
    rw [Commons.Analysis.SpecialFunctions.Gamma.logDeriv_const_cpow hc] at hld
    have hder : deriv (fun w : ℂ => -w / 2) z = -((2 : ℂ)⁻¹) := by
      simp
      norm_num
    rw [hder] at hld
    rw [Function.comp_def] at hld
    calc logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z
        = Complex.log (Real.pi : ℂ) * (-((2 : ℂ)⁻¹)) := by simpa using hld
      _ = -(Complex.log (Real.pi : ℂ)) / 2 := by
            rw [div_eq_mul_inv]
            ring
  have hldg : logDeriv g z = Complex.digamma (z / 2) / 2 := by
    dsimp [g]
    have hdiv : DifferentiableAt ℂ (fun w : ℂ => w / 2) z := by fun_prop
    have hld := logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ => w / 2) (x := z)
      (Complex.differentiableAt_Gamma (z / 2) hz) hdiv
    have hder : deriv (fun w : ℂ => w / 2) z = (2 : ℂ)⁻¹ := by simp
    rw [hder] at hld
    rw [Function.comp_def] at hld
    rw [← Complex.digamma_def] at hld
    calc logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) z
        = Complex.digamma (z / 2) * ((2 : ℂ)⁻¹) := by simpa using hld
      _ = Complex.digamma (z / 2) / 2 := by simp [div_eq_mul_inv]
  have hfun : Complex.Gammaℝ =
      (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) := by
    funext w
    rw [Complex.Gammaℝ_def]
  have hldG : logDeriv Complex.Gammaℝ z =
      logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) z :=
    congrArg (fun F : ℂ → ℂ => logDeriv F z) hfun
  have hmul := logDeriv_mul (x := z) (f := f) (g := g) (hcpow_ne z)
    (Complex.Gamma_ne_zero hz)
    (by
      have hinner : DifferentiableAt ℂ (fun w : ℂ => -w / 2) z := by fun_prop
      exact hinner.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    ((Complex.differentiableAt_Gamma (z / 2) hz).comp z (by fun_prop))
  calc logDeriv Complex.Gammaℝ z
      = logDeriv (fun w : ℂ => f w * g w) z := by
          rw [hldG]
    _ = logDeriv f z + logDeriv g z := hmul
    _ = -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2 := by rw [hldf, hldg]

/-! ## Bounds for the logarithmic derivative of the gamma factor -/

private lemma norm_log_Gammaℝ_eq : ‖Complex.log (Real.pi : ℂ)‖ = Real.log Real.pi := by
  rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
  exact Complex.norm_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))

private lemma log2pi_bound : Real.log Real.pi / 2 + 6 ≤ 12 := by
  have h := Real.log_le_sub_one_of_pos Real.pi_pos
  linarith [Real.pi_lt_four]

/-- On the vertical line `Re s = -1/2` the logarithmic derivative of the gamma factor of any
Dirichlet character is `O(log(2+|T|))`: `‖logDeriv γ_χ(-1/2+iT)‖ ≤ log(2+|T|)/2 + 12`. -/
private lemma logDeriv_gammaFactor_neg_half_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖logDeriv (gammaFactor χ) ((-1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      Real.log (2 + |T|) / 2 + 12 := by
  set z : ℂ := (-1 / 2 : ℂ) + (T : ℂ) * Complex.I with hz
  have hz2 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre : (z / 2).re = -(1 / 4 : ℝ) := by
      rw [hz]
      norm_num [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.normSq_apply]
    have h2 : (m : ℝ) = 1 / 4 := by
      have := congrArg Complex.re hm
      rw [hre] at this
      simp at this
      linarith
    have h4 : ((4 * m : ℕ) : ℝ) = 1 := by
      have : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
      rw [this, h2]; norm_num
    have h4' : 4 * m = 1 := by exact_mod_cast h4
    omega
  have hz1re : (z + 1).re = (1 / 2 : ℝ) := by
    rw [hz]
    norm_num [Complex.add_re, Complex.mul_re]
  have hz1 : ∀ m : ℕ, (z + 1) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre : ((z + 1) / 2).re = (1 / 4 : ℝ) := by
      rw [hz]
      norm_num [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.normSq_apply]
    have := congrArg Complex.re hm
    rw [hre] at this
    simp at this
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hre : z.re = (-1 / 2 : ℝ) := by rw [hz]; simp
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext w; exact hE.gammaFactor_def w
    rw [hfun]
    have hform := logDeriv_Gammaℝ_formula_off_pole z hz2
    have heq : z / 2 = -(1 / 4 : ℂ) + (T : ℂ) * Complex.I / 2 := by
      rw [hz]; ring
    rw [hform, heq]
    have hdg := digamma_neg_quarter_bound T
    have hb1 : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
      rw [norm_div, norm_neg, norm_log_Gammaℝ_eq]
      norm_num
    have hb2 : ‖Complex.digamma (-(1 / 4 : ℂ) + (T : ℂ) * Complex.I / 2) / 2‖ ≤
        (Real.log (2 + |T|) + 12) / 2 := by
      rw [norm_div]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]
      linarith [hdg]
    calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (-(1 / 4 : ℂ) + (T : ℂ) * Complex.I / 2) / 2‖
        ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
          ‖Complex.digamma (-(1 / 4 : ℂ) + (T : ℂ) * Complex.I / 2) / 2‖ := norm_add_le _ _
      _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |T|) + 12) / 2 := by
            rw [hb1]; linarith
      _ ≤ Real.log (2 + |T|) / 2 + 12 := by linarith [log2pi_bound]
  · have hfun : gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) := by
      funext w; exact hO.gammaFactor_def w
    rw [hfun]
    have hz1pos : 0 < (z + 1).re := by rw [hz1re]; norm_num
    have hcomp : logDeriv (fun w : ℂ => Complex.Gammaℝ (w + 1)) z =
        logDeriv Complex.Gammaℝ (z + 1) := by
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun w : ℂ => w + 1) (x := z)
        (differentiableAt_Gammaℝ (z + 1) hz1pos) (by fun_prop)
      have hder : deriv (fun w : ℂ => w + 1) z = 1 := by simp
      rw [hder, mul_one] at h
      simpa [Function.comp_def] using h
    rw [hcomp]
    have hform := logDeriv_Gammaℝ_formula_off_pole (z + 1) hz1
    have heq : (z + 1) / 2 = ((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hz]
      apply Complex.ext <;>
        simp [Complex.div_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.normSq_apply] <;> ring
    rw [hform, heq]
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      (1 / 4) (T / 2) (by norm_num) (by norm_num)
    have hb1 : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
      rw [norm_div, norm_neg, norm_log_Gammaℝ_eq]
      norm_num
    have hb2 : ‖Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I) / 2‖ ≤
        (Real.log (2 + |T|) + 8) / 2 := by
      rw [norm_div]
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2n]
      have hlog : Real.log (2 + |T / 2|) ≤ Real.log (2 + |T|) := by
        apply Real.log_le_log (by positivity)
        have h1 : |T / 2| ≤ |T| := by
          rw [abs_div]
          have h2 : |(2 : ℝ)| = 2 := by norm_num
          rw [h2]
          have := abs_nonneg T
          linarith
        linarith
      linarith
    calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I) / 2‖
        ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
          ‖Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I) / 2‖ := norm_add_le _ _
      _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |T|) + 8) / 2 := by rw [hb1]; linarith
      _ ≤ Real.log (2 + |T|) / 2 + 12 := by linarith [log2pi_bound]

/-- The logarithmic derivative of the gamma factor is `O(log(2+|y|))` on any vertical line
`Re s ∈ [1/2, 15]`. -/
private lemma logDeriv_gammaFactor_vertical_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (x y : ℝ) (hx1 : (1 / 2 : ℝ) ≤ x) (hx2 : x ≤ 15) :
    ‖logDeriv (gammaFactor χ) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.log (2 + |y|) / 2 + 12 := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  have hzre : z.re = x := by rw [hz]; simp
  have hz2 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre : (z / 2).re = x / 2 := by
      rw [hz]
      norm_num [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.normSq_apply]
    have := congrArg Complex.re hm
    rw [hre] at this
    simp at this
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hz1re : (z + 1).re = x + 1 := by rw [hz]; simp
  have hz1 : ∀ m : ℕ, (z + 1) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre : ((z + 1) / 2).re = (x + 1) / 2 := by
      rw [hz]
      norm_num [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.normSq_apply]
    have := congrArg Complex.re hm
    rw [hre] at this
    simp at this
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hlog : Real.log (2 + |y / 2|) ≤ Real.log (2 + |y|) := by
    apply Real.log_le_log (by positivity)
    have h1 : |y / 2| ≤ |y| := by
      rw [abs_div]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      have := abs_nonneg y
      linarith
    linarith
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext w; exact hE.gammaFactor_def w
    rw [hfun]
    have hform := logDeriv_Gammaℝ_formula_off_pole z hz2
    have heq : z / 2 = ((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hz]
      exact div_two_add_I x y
    rw [hform, heq]
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      (x / 2) (y / 2) (by linarith) (by linarith)
    have hb1 : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
      rw [norm_div, norm_neg, norm_log_Gammaℝ_eq]
      norm_num
    have hb2 : ‖Complex.digamma (((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) / 2‖ ≤
        (Real.log (2 + |y|) + 8) / 2 := by
      rw [norm_div]
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2n]
      linarith [hdg, hlog]
    calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) / 2‖
        ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
          ‖Complex.digamma (((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) / 2‖ := norm_add_le _ _
      _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |y|) + 8) / 2 := by rw [hb1]; linarith
      _ ≤ Real.log (2 + |y|) / 2 + 12 := by linarith [log2pi_bound]
  · have hfun : gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) := by
      funext w; exact hO.gammaFactor_def w
    rw [hfun]
    have hz1pos : 0 < (z + 1).re := by rw [hz1re]; linarith
    have hcomp : logDeriv (fun w : ℂ => Complex.Gammaℝ (w + 1)) z =
        logDeriv Complex.Gammaℝ (z + 1) := by
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun w : ℂ => w + 1) (x := z)
        (differentiableAt_Gammaℝ (z + 1) hz1pos) (by fun_prop)
      have hder : deriv (fun w : ℂ => w + 1) z = 1 := by simp
      rw [hder, mul_one] at h
      simpa [Function.comp_def] using h
    rw [hcomp]
    have hform := logDeriv_Gammaℝ_formula_off_pole (z + 1) hz1
    have heq : (z + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hz]
      exact add_one_div_two_add_I x y
    rw [hform, heq]
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      ((x + 1) / 2) (y / 2) (by linarith) (by linarith)
    have hb1 : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
      rw [norm_div, norm_neg, norm_log_Gammaℝ_eq]
      norm_num
    have hb2 : ‖Complex.digamma ((((x + 1) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) / 2‖ ≤
        (Real.log (2 + |y|) + 8) / 2 := by
      rw [norm_div]
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2n]
      linarith [hdg, hlog]
    calc ‖-(Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma ((((x + 1) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) / 2‖
        ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
          ‖Complex.digamma ((((x + 1) / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) / 2‖ :=
          norm_add_le _ _
      _ ≤ Real.log Real.pi / 2 + (Real.log (2 + |y|) + 8) / 2 := by rw [hb1]; linarith
      _ ≤ Real.log (2 + |y|) / 2 + 12 := by linarith [log2pi_bound]

/-! ## Nonvanishing and differentiability of the gamma factor at `-1/2 + iT` -/

private lemma gammaFactor_ne_zero_at_neg_half {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    gammaFactor χ ((-1 / 2 : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
  set z : ℂ := (-1 / 2 : ℂ) + (T : ℂ) * Complex.I with hz
  rcases χ.even_or_odd with hE | hO
  · rw [hE.gammaFactor_def]
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre := congrArg Complex.re hn
    rw [hz] at hre
    simp at hre
    have h2 : ((2 * n : ℕ) : ℝ) = 1 / 2 := by
      push_cast
      linarith
    have h4 : ((4 * n : ℕ) : ℝ) = 1 := by
      have : ((4 * n : ℕ) : ℝ) = 2 * ((2 * n : ℕ) : ℝ) := by push_cast; ring
      rw [this, h2]; norm_num
    have h4' : 4 * n = 1 := by exact_mod_cast h4
    omega
  · rw [hO.gammaFactor_def]
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre := congrArg Complex.re hn
    rw [hz] at hre
    simp at hre
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

private lemma differentiableAt_gammaFactor_at_neg_half {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    DifferentiableAt ℂ (gammaFactor χ) ((-1 / 2 : ℂ) + (T : ℂ) * Complex.I) := by
  set z : ℂ := (-1 / 2 : ℂ) + (T : ℂ) * Complex.I with hz
  have hz2 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre : (z / 2).re = -(1 / 4 : ℝ) := by
      rw [hz]
      norm_num [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.normSq_apply]
    have h2 : (m : ℝ) = 1 / 4 := by
      have := congrArg Complex.re hm
      rw [hre] at this
      simp at this
      linarith
    have h4 : ((4 * m : ℕ) : ℝ) = 1 := by
      have : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
      rw [this, h2]; norm_num
    have h4' : 4 * m = 1 := by exact_mod_cast h4
    omega
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext w; exact hE.gammaFactor_def w
    rw [hfun]
    have hfun2 : Complex.Gammaℝ =
        (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) := by
      funext w; rw [Complex.Gammaℝ_def]
    rw [hfun2]
    exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -w / 2) z).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      ((Complex.differentiableAt_Gamma (z / 2) hz2).comp z (by fun_prop))
  · have hfun : gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) := by
      funext w; exact hO.gammaFactor_def w
    rw [hfun]
    have hpos : 0 < (z + 1).re := by
      rw [hz]
      norm_num [Complex.add_re, Complex.mul_re]
    exact (differentiableAt_Gammaℝ (z + 1) hpos).comp z
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w + 1) z)

/-! ## The main theorem -/

/-- Pointwise bound for the logarithmic derivative of `L(.,chi)` on the vertical line
`Re s = -1/2`, for a primitive non-trivial character: `‖L'/L(-1/2 + iT)‖ ≤ C (log N + log(2+|T|) + 1)`.

This is the input needed to bound the left-hand vertical integral after shifting the contour in
the truncated Perron formula down from `Re s = 1 + 1/log x` to `Re s = -1/2`.
Route: the functional equation transfers the point to `3/2 - iT`
(`logDeriv_completedL_fe_transfer`), where both `L'/L` and the digamma factor are bounded by
`O(log(2+|T|))`; the factor `L'/L = logDeriv (completedLFunction chi) - logDeriv (gammaFactor chi)`
converts between the completed and the ordinary log-derivative. -/
theorem logDeriv_LFunction_re_neg_half_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ,
      ‖logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        C * (Real.log (N : ℝ) + Real.log (2 + |T|) + 1) := by
  have hN1 : N ≠ 1 := by
    rintro rfl
    exact hχ (Subsingleton.elim χ 1)
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  have hχprim_inv : (χ⁻¹).IsPrimitive := isPrimitive_inv hχprim
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  refine ⟨45, by norm_num, fun T => ?_⟩
  set s : ℂ := (-1 / 2 : ℂ) + (T : ℂ) * Complex.I with hs
  have hsre : s.re = (-1 / 2 : ℝ) := by rw [hs]; simp
  have hcsre : (1 - s).re = (3 / 2 : ℝ) := by
    rw [hs]
    norm_num [Complex.add_re, Complex.mul_re]
  have hlog2 : 0 ≤ Real.log (2 + |T|) := Real.log_nonneg (by linarith [abs_nonneg T])
  by_cases hLs : DirichletCharacter.LFunction χ s = 0
  · rw [logDeriv_apply, hLs, div_zero, norm_zero]
    nlinarith [hlogN, hlog2]
  · have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 := by
      intro h
      apply hLs
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1), h]
      simp
    have hLcs : DirichletCharacter.LFunction (χ⁻¹) (1 - s) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹) (Or.inl hχinv) (by rw [hcsre]; norm_num)
    have hΛcs : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
      intro h
      apply hLcs
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ⁻¹) (1 - s) (Or.inr hN1), h]
      simp
    have hγs : gammaFactor χ s ≠ 0 := by
      rw [hs]; exact gammaFactor_ne_zero_at_neg_half χ T
    have hγdiff : DifferentiableAt ℂ (gammaFactor χ) s := by
      rw [hs]; exact differentiableAt_gammaFactor_at_neg_half χ T
    have hLsplit : logDeriv (DirichletCharacter.LFunction χ) s =
        logDeriv (DirichletCharacter.completedLFunction χ) s - logDeriv (gammaFactor χ) s := by
      have hfun : DirichletCharacter.LFunction χ =
          (fun z => DirichletCharacter.completedLFunction χ z / gammaFactor χ z) := by
        funext z
        exact DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN1)
      rw [hfun]
      exact logDeriv_div (x := s) hΛs hγs
        ((differentiable_completedLFunction hχ) s) hγdiff
    have hFE : logDeriv (DirichletCharacter.completedLFunction χ) s =
        -(Real.log (N : ℝ) : ℂ) -
          logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) :=
      logDeriv_completedL_fe_transfer χ hχ hχprim s hΛs hΛcs
    have hsplit :=
      Commons.NumberTheory.DirichletCharacter.leftHalf_avg.logDeriv_completedL_eq_add_re_ge_one
        (χ⁻¹) hχinv hχprim_inv (1 - s) (by rw [hcsre]; norm_num)
    have hL1 : ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s)‖ ≤ 20 := by
      have := logDeriv_LFunction_re_ge_three_halves_bound (χ⁻¹) (s := 1 - s) (by rw [hcsre])
      simpa using this
    have hγ1 : ‖logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖ ≤ Real.log (2 + |T|) / 2 + 12 := by
      have h := logDeriv_gammaFactor_vertical_bound (χ⁻¹) (3 / 2) (-T) (by norm_num) (by norm_num)
      have hpt : ((3 / 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I = 1 - s := by
        rw [hs]; push_cast; ring
      rw [hpt] at h
      simpa using h
    have hγ0 : ‖logDeriv (gammaFactor χ) s‖ ≤ Real.log (2 + |T|) / 2 + 12 := by
      rw [hs]; exact logDeriv_gammaFactor_neg_half_bound χ T
    have hlogNeq : ‖-(Real.log (N : ℝ) : ℂ)‖ = Real.log (N : ℝ) := by
      rw [norm_neg]
      exact Complex.norm_of_nonneg hlogN
    have hkey : ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
        Real.log (N : ℝ) + 20 + (Real.log (2 + |T|) / 2 + 12) +
          (Real.log (2 + |T|) / 2 + 12) := by
      rw [hLsplit, hFE, hsplit]
      calc ‖(-(Real.log (N : ℝ) : ℂ) -
              (logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
                logDeriv (gammaFactor (χ⁻¹)) (1 - s))) - logDeriv (gammaFactor χ) s‖
          ≤ ‖-(Real.log (N : ℝ) : ℂ) -
              (logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
                logDeriv (gammaFactor (χ⁻¹)) (1 - s))‖ + ‖logDeriv (gammaFactor χ) s‖ :=
            norm_sub_le _ _
        _ ≤ (‖-(Real.log (N : ℝ) : ℂ)‖ +
              ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
                logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖) + ‖logDeriv (gammaFactor χ) s‖ := by
            gcongr
            exact norm_sub_le _ _
        _ ≤ (Real.log (N : ℝ) + (20 + (Real.log (2 + |T|) / 2 + 12))) +
              (Real.log (2 + |T|) / 2 + 12) := by
            refine add_le_add (add_le_add ?_ ?_) hγ0
            · exact le_of_eq hlogNeq
            · calc ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s) +
                    logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖
                  ≤ ‖logDeriv (DirichletCharacter.LFunction (χ⁻¹)) (1 - s)‖ +
                    ‖logDeriv (gammaFactor (χ⁻¹)) (1 - s)‖ := norm_add_le _ _
                _ ≤ 20 + (Real.log (2 + |T|) / 2 + 12) := add_le_add hL1 hγ1
        _ = Real.log (N : ℝ) + 20 + (Real.log (2 + |T|) / 2 + 12) +
              (Real.log (2 + |T|) / 2 + 12) := by ring
    have hfin : Real.log (N : ℝ) + 20 + (Real.log (2 + |T|) / 2 + 12) +
          (Real.log (2 + |T|) / 2 + 12) ≤
        45 * (Real.log (N : ℝ) + Real.log (2 + |T|) + 1) := by
      nlinarith [hlogN, hlog2]
    linarith [hkey, hfin]

end Commons.NumberTheory.DirichletCharacter
