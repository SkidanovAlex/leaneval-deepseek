/-
# `tf72Fc_imag_re_nonneg` — positivity of `Re F(iy)` for HB's test function

For Heath-Brown's test function `f = g ∗ g` of Lemma 7.2 (`testFn72_defs`) and its
Laplace transform `F z = ∫₀^{2/λ} e^{−zt} f t dt`, we prove that the transform is
non-negative on the imaginary axis:

  `0 ≤ Re F(i y)`  for every real `y` and every `λ > 0`.

This is the imaginary-axis half of Condition 2 (the real-axis half being
`TestFn_F_nonneg`), and it is what makes the `F`-inequalities of HB §§6–10 have a
sign on the critical line `Re z = 0`.

The argument is completely explicit.  Writing `c = y/λ`:

* `Re F(i y) = ∫₀^{2/λ} cos(y t) f(t) dt`;
* on `[0, 2/λ]` the test function is the polynomial `(λ/30)(2−λt)³(4+6λt+λ²t²)`,
  and the substitution `u = λ t` turns the integral into
  `(1/30) ∫₀² cos(c u) (32 − 40u² + 20u³ − u⁵) du`;
* the remaining integral evaluates (for `c ≠ 0`) to
  `240 (sin c − c cos c)² / c⁶ ≥ 0`,
  while for `c = 0` the integrand `(2−u)³(4+6u+u²)` is non-negative on `[0,2]`.

The three building blocks (`tf72Fc_imag_re_eq`, `tf72f_imag_re_reduce`,
`intCosPoly72`) are proved here from scratch.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

noncomputable section
namespace Work.ZeroFreeTables

/-! ### The closed-form integral `∫₀² cos(cu)(32 − 40u² + 20u³ − u⁵) du`

We exhibit an explicit antiderivative
`Ψ c u / c⁶ = (c sin(cu) Â(c,u) + cos(cu) B̂(c,u)) / c⁶`,
whose derivative is `c⁶ · cos(cu) · (32 − 40u² + 20u³ − u⁵)`.  All auxiliary
polynomials are `private` so as not to pollute the namespace. -/

private def tq0 (u : ℝ) : ℝ := 32 - 40*u^2 + 20*u^3 - u^5
private def tq1 (u : ℝ) : ℝ := -80*u + 60*u^2 - 5*u^4
private def tq2 (u : ℝ) : ℝ := 80 - 120*u + 20*u^3
private def tq3 (u : ℝ) : ℝ := -120 + 60*u^2
private def tq4 (u : ℝ) : ℝ := -120*u
private def tq5 (_u : ℝ) : ℝ := -120
private def te1 (u : ℝ) : ℝ := -80 + 120*u - 20*u^3

private def Ahat (c u : ℝ) : ℝ := c^4*tq0 u + c^2*tq2 u + tq4 u
private def Bhat (c u : ℝ) : ℝ := c^4*tq1 u + c^2*tq3 u + tq5 u
private def Psi (c u : ℝ) : ℝ := c*(Real.sin (c*u) * Ahat c u) + Real.cos (c*u) * Bhat c u

private lemma thd0 (u : ℝ) : HasDerivAt tq0 (tq1 u) u := by
  unfold tq0 tq1
  have h := (((hasDerivAt_const (x := u) (c := (32:ℝ))).sub
    ((hasDerivAt_pow 2 u).const_mul (40:ℝ))).add
    ((hasDerivAt_pow 3 u).const_mul (20:ℝ))).sub (hasDerivAt_pow 5 u)
  exact h.congr_deriv (by ring)

private lemma thd1 (u : ℝ) : HasDerivAt tq1 (te1 u) u := by
  unfold tq1 te1
  have h := (((hasDerivAt_id u).const_mul (-80:ℝ)).add
    ((hasDerivAt_pow 2 u).const_mul (60:ℝ))).sub ((hasDerivAt_pow 4 u).const_mul (5:ℝ))
  exact h.congr_deriv (by ring)

private lemma thd2 (u : ℝ) : HasDerivAt tq2 (tq3 u) u := by
  unfold tq2 tq3
  have h := (((hasDerivAt_const (x := u) (c := (80:ℝ))).sub
    ((hasDerivAt_id u).const_mul (120:ℝ))).add ((hasDerivAt_pow 3 u).const_mul (20:ℝ)))
  exact h.congr_deriv (by ring)

private lemma thd3 (u : ℝ) : HasDerivAt tq3 (120*u) u := by
  unfold tq3
  have h := ((hasDerivAt_const (x := u) (c := (-120:ℝ))).add
    ((hasDerivAt_pow 2 u).const_mul (60:ℝ)))
  exact h.congr_deriv (by ring)

private lemma thd4 (u : ℝ) : HasDerivAt tq4 (-120) u := by
  unfold tq4
  have h := (hasDerivAt_id u).const_mul (-120:ℝ)
  exact h.congr_deriv (by ring)

private lemma thd5 (_u : ℝ) : HasDerivAt tq5 0 _u := by
  unfold tq5; exact hasDerivAt_const _u (-120:ℝ)

/-- `Â' = B̂`. -/
private lemma hdA (c : ℝ) (u : ℝ) : HasDerivAt (Ahat c) (Bhat c u) u := by
  have h := (((thd0 u).const_mul (c^4)).add ((thd2 u).const_mul (c^2))).add (thd4 u)
  have h2 : ((fun u : ℝ => c^4 * tq0 u) + (fun u : ℝ => c^2 * tq2 u)) + tq4 = Ahat c := rfl
  rw [h2] at h
  have h3 : c^4 * tq1 u + c^2 * tq3 u + (-120) = Bhat c u := by simp [Bhat, tq5]
  rw [h3] at h
  exact h

/-- `B̂' = c⁴(−80+120u−20u³) + c²·120u`. -/
private lemma hdB (c : ℝ) (u : ℝ) : HasDerivAt (Bhat c) (c^4 * te1 u + c^2 * (120*u)) u := by
  have h := (((thd1 u).const_mul (c^4)).add ((thd3 u).const_mul (c^2))).add (thd5 u)
  have h2 : ((fun u : ℝ => c^4 * tq1 u) + (fun u : ℝ => c^2 * tq3 u)) + tq5 = Bhat c := rfl
  rw [h2] at h
  have h3 : c^4 * te1 u + c^2 * (120*u) + 0 = c^4 * te1 u + c^2 * (120*u) := by ring
  rw [h3] at h
  exact h

/-- `Ψ' = c⁶ · cos(cu) · (32 − 40u² + 20u³ − u⁵)`. -/
private lemma hdPsi (c : ℝ) (u : ℝ) :
    HasDerivAt (Psi c) (c^6 * (Real.cos (c*u) * tq0 u)) u := by
  have hS : HasDerivAt (fun u : ℝ => Real.sin (c*u)) (Real.cos (c*u) * c) u :=
    (Real.hasDerivAt_sin (c*u)).comp u (hasDerivAt_const_mul (x := u) c)
  have hC : HasDerivAt (fun u : ℝ => Real.cos (c*u)) (-(Real.sin (c*u)) * c) u :=
    (Real.hasDerivAt_cos (c*u)).comp u (hasDerivAt_const_mul (x := u) c)
  have h1 := (hS.mul (hdA c u)).const_mul c
  have h2 := hC.mul (hdB c u)
  have h := h1.add h2
  have key : HasDerivAt (Psi c) (c * (Real.cos (c*u) * c * Ahat c u + Real.sin (c*u) * Bhat c u)
      + (-(Real.sin (c*u)) * c * Bhat c u
          + Real.cos (c*u) * (c^4 * te1 u + c^2 * (120*u)))) u := h
  refine key.congr_deriv ?_
  simp only [Ahat, Bhat, te1, tq0, tq1, tq2, tq3, tq4, tq5]
  ring

/-- **The explicit integral.** For `c ≠ 0`,
`∫₀² cos(cu)(32 − 40u² + 20u³ − u⁵) du = 240 (sin c − c cos c)² / c⁶`. -/
theorem intCosPoly72 (c : ℝ) (hc : c ≠ 0) :
    ∫ u in (0:ℝ)..2, Real.cos (c*u) * (32 - 40*u^2 + 20*u^3 - u^5)
      = 240 * (Real.sin c - c * Real.cos c)^2 / c^6 := by
  have hG : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Psi c u / c^6)
      (Real.cos (c*u) * (32 - 40*u^2 + 20*u^3 - u^5)) u := by
    intro u
    have h := (hdPsi c u).div_const (c^6)
    refine h.congr_deriv ?_
    simp only [tq0]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero 6 hc)]
  have hint : IntervalIntegrable (fun u : ℝ => Real.cos (c*u) * (32 - 40*u^2 + 20*u^3 - u^5))
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => Psi c u / c^6)
    (f' := fun u : ℝ => Real.cos (c*u) * (32 - 40*u^2 + 20*u^3 - u^5))
    (fun u _ => hG u) hint]
  have hval : Psi c 2 - Psi c 0 = 240 * (Real.sin c - c * Real.cos c)^2 := by
    simp only [Psi, Ahat, Bhat, tq0, tq1, tq2, tq3, tq4, tq5, Real.sin_zero, Real.cos_zero,
      mul_zero, zero_add, one_mul]
    have h2c : c * 2 = 2 * c := by ring
    rw [h2c, Real.sin_two_mul, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq c]
  rw [div_sub_div_same, hval]

/-! ### Reduction of `Re F(iy)` to a real trigonometric integral -/

/-- On the imaginary axis the Laplace transform is the cosine integral of `f`. -/
theorem tf72Fc_imag_re_eq (lam : ℝ) (hlam : 0 < lam) (y : ℝ) :
    (tf72Fc lam ((y : ℂ) * Complex.I)).re
      = ∫ t in (0:ℝ)..(2/lam), Real.cos (y * t) * tf72f lam t := by
  have hpoint : ∀ t : ℝ,
      (Complex.exp (-(((y : ℂ) * Complex.I) * (t:ℂ))) * ((tf72f lam t : ℝ):ℂ)).re
        = Real.cos (y*t) * tf72f lam t := by
    intro t
    have hexp : Complex.exp (-(((y : ℂ) * Complex.I) * (t:ℂ)))
        = Complex.exp (((-(y*t) : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [hexp, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg, mul_zero, sub_zero]
  have hcont : ContinuousOn (fun t : ℝ => Complex.exp (-(((y : ℂ) * Complex.I) * (t:ℂ)))
      * ((tf72f lam t : ℝ):ℂ)) (Set.Icc 0 (2/lam)) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact Complex.continuous_ofReal.comp_continuousOn
        ((tf72f_cont lam hlam).mono (fun t ht => ht.1))
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (-(((y : ℂ) * Complex.I) * (t:ℂ)))
      * ((tf72f lam t : ℝ):ℂ)) MeasureTheory.volume (0:ℝ) (2/lam) :=
    hcont.intervalIntegrable_of_Icc (by positivity)
  rw [tf72Fc]
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint]
  exact intervalIntegral.integral_congr (fun t _ => hpoint t)

/-- On `[0, 2/λ]` the test function is the polynomial of Lemma 7.2; the substitution
`u = λ t` reduces the cosine integral to the canonical one on `[0,2]`. -/
theorem tf72f_imag_re_reduce (lam : ℝ) (hlam : 0 < lam) (y : ℝ) :
    (∫ t in (0:ℝ)..(2/lam), Real.cos (y * t) * tf72f lam t)
      = (1/30) * ∫ u in (0:ℝ)..2,
          Real.cos ((y/lam) * u) * (32 - 40*u^2 + 20*u^3 - u^5) := by
  have hne : lam ≠ 0 := hlam.ne'
  have hpoly : (∫ t in (0:ℝ)..(2/lam), Real.cos (y*t) * tf72f lam t)
      = ∫ t in (0:ℝ)..(2/lam),
          Real.cos (y*t) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (show (0:ℝ) ≤ 2/lam by positivity)] at ht
    rw [tf72f_eq_poly lam hlam t ht]
  rw [hpoly]
  have hsub : (∫ t in (0:ℝ)..(2/lam),
        Real.cos (y*t) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)))
      = ∫ t in (0:ℝ)..(2/lam),
          (fun u : ℝ => (lam/30)*(Real.cos ((y/lam)*u)*((2-u)^3*(4+6*u+u^2)))) (lam*t) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only []
    have hyt : (y/lam)*(lam*t) = y*t := by field_simp
    rw [hyt]
    ring
  rw [hsub]
  rw [intervalIntegral.integral_comp_mul_left
    (fun u : ℝ => (lam/30)*(Real.cos ((y/lam)*u)*((2-u)^3*(4+6*u+u^2)))) hne]
  rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  have hscal : ∀ Z : ℝ, lam⁻¹ * (lam / 30 * Z) = 1 / 30 * Z := by intro Z; field_simp
  have hX : (∫ u in (0:ℝ)..2, Real.cos ((y/lam)*u)*((2-u)^3*(4+6*u+u^2)))
      = ∫ u in (0:ℝ)..2, Real.cos ((y/lam)*u)*(32-40*u^2+20*u^3-u^5) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    ring
  rw [hscal, hX]

/-! ### The target -/

theorem tf72Fc_imag_re_nonneg (lam : ℝ) (hlam : 0 < lam) (y : ℝ) :
    0 ≤ (Work.ZeroFreeTables.tf72Fc lam ((y : ℂ) * Complex.I)).re := by
  rw [tf72Fc_imag_re_eq lam hlam y, tf72f_imag_re_reduce lam hlam y]
  by_cases hc : y/lam = 0
  · rw [hc]
    simp only [zero_mul, Real.cos_zero, one_mul]
    apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    have h : 32 - 40*u^2 + 20*u^3 - u^5 = (2-u)^3*(4+6*u+u^2) := by ring
    rw [h]
    have h1 : 0 ≤ 2-u := by linarith [hu.2]
    have h2 : (0:ℝ) ≤ 4+6*u+u^2 := by nlinarith [hu.1, sq_nonneg u]
    positivity
  · rw [intCosPoly72 (y/lam) hc]
    apply mul_nonneg (by norm_num)
    apply div_nonneg _ (by positivity)
    positivity

end Work.ZeroFreeTables
