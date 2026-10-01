/-
# `tf72_numeric_inputs` — the five numerical inputs of the `h ≥ 5` case of HB Theorem 1

`Work.ZeroFreeTables.TfNumericInputs` collects the five elementary integrals

* `∫₀^{8/3} e^{c t} f_{3/4}(t) dt` for `c = 348/1000, 82/100, 472/1000`,
* `∫₀^{8/3} e^{c t} f_{17/20}(t) dt` for `c = 348/1000` and `c = -472/1000`,

where `f_λ = tf72f λ` is the test function of HB Lemma 7.2.  Every one of them is of the shape
`∫₀^{2/λ} e^{ct} f_λ`, which is (after the substitution `u = λt`) `G(c/λ)/30` where

  `G(x) = ∫₀² g(u) e^{xu} du`,   `g(u) = (2-u)³(4+6u+u²) = 32 - 40u² + 20u³ - u⁵`

is Heath-Brown's normalised density and the factor `λ` of `f_λ = (λ/30)·…` cancels the Jacobian
(`tf72f_int_exp` below).  For `λ = 3/4` the upper limit `2/λ` is exactly `8/3`; for `λ = 17/20` it
is `40/17 ≤ 8/3` and the integrand vanishes on the remaining piece `[40/17, 8/3]` (`tf72f_supp`),
which is why the integral over `[0, 8/3]` may be truncated at `40/17`
(`intervalIntegral_eq_of_eqOn_zero`).

`tf72G_eq_exp` writes `G(x) = e^{2x}·A(x) + B(x)` with the explicit rational functions
`A(x) = 120(x-1)²/x⁶ ≥ 0` and `B(x) = -32/x + 80/x³ + 120/x⁴ - 120/x⁶`, so a one-sided rational
bound for `e^{2x}` bounds `G(x)` one-sidedly (`tf72G_le_of_exp_le`, `tf72G_ge_of_exp_ge`); the
exponential bounds are supplied by the rational Taylor estimates `exp_nat_add_frac_le/ge`
(and `Real.exp_neg` for the negative exponent `-472/425`).  Each of the five clauses is then the
explicit rational inequality printed in the corresponding `har` below, closed by `norm_num`.

This module is deliberately self-contained in its evaluation of `G` (it reproves the closed form
of `G` from the monomial integrals `integral_pow_mul_exp`), so that it depends only on
`TestFn72_defs` (through `HB95plus.Main`) and Mathlib.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB95plus.Main
import Submission.Work.ZeroFreeTables.integral_pow_mul_exp

namespace Work.ZeroFreeTables.HB95plus

open Work.ZeroFreeTables
open scoped BigOperators

noncomputable section

/-! ## The two-place evaluation `G` of HB's normalised density -/

/-- HB's normalised density evaluated against `e^{xu}`: `G(x) = ∫₀² g(u)e^{xu}du` with
`g(u) = 32 - 40u² + 20u³ - u⁵ = (2-u)³(4+6u+u²)`. -/
def tf72G (x : ℝ) : ℝ := ∫ u in (0:ℝ)..2, (32 - 40*u^2 + 20*u^3 - u^5) * Real.exp (x*u)

/-- `G` expanded by linearity into the five monomial integrals `∫₀² u^k e^{xu}du`. -/
theorem tf72G_eq_sum (x : ℝ) :
    tf72G x
      = 32 * (∫ u in (0:ℝ)..2, Real.exp (x * u))
        - 40 * (∫ u in (0:ℝ)..2, u ^ 2 * Real.exp (x * u))
        + 20 * (∫ u in (0:ℝ)..2, u ^ 3 * Real.exp (x * u))
        - (∫ u in (0:ℝ)..2, u ^ 5 * Real.exp (x * u)) := by
  unfold tf72G
  have hcongr : (∫ u in (0:ℝ)..2, (32 - 40 * u ^ 2 + 20 * u ^ 3 - u ^ 5) * Real.exp (x * u))
      = ∫ u in (0:ℝ)..2,
          (32 * Real.exp (x * u) - 40 * (u ^ 2 * Real.exp (x * u))
            + 20 * (u ^ 3 * Real.exp (x * u)) - u ^ 5 * Real.exp (x * u)) :=
    intervalIntegral.integral_congr (fun u _ => by ring)
  rw [hcongr]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable 0 2

/-- `∫₀² e^{xu}du = (e^{2x} - 1)/x` for `x ≠ 0`, the `k = 0` case of `integral_pow_mul_exp`
written in the shape needed below. -/
theorem tf72_integral_exp_mul (x : ℝ) (hx : x ≠ 0) :
    (∫ u in (0:ℝ)..2, Real.exp (x * u)) = (Real.exp (2 * x) - 1) / x := by
  have hcongr : (∫ u in (0:ℝ)..2, Real.exp (x * u))
      = ∫ u in (0:ℝ)..2, u ^ 0 * Real.exp (x * u) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp
  rw [hcongr, integral_pow_mul_exp 0 hx]
  simp [Finset.sum_range_one]
  field_simp

/-- **Closed form of `G`**: `G(x) = e^{2x}(120/x⁴ - 240/x⁵ + 120/x⁶) - 32/x + 80/x³ + 120/x⁴
- 120/x⁶` for `x ≠ 0`. -/
theorem tf72G_eq_exp (x : ℝ) (hx : x ≠ 0) :
    tf72G x = Real.exp (2 * x) * (120 / x ^ 4 - 240 / x ^ 5 + 120 / x ^ 6)
      - 32 / x + 80 / x ^ 3 + 120 / x ^ 4 - 120 / x ^ 6 := by
  rw [tf72G_eq_sum, tf72_integral_exp_mul x hx, integral_pow_mul_exp 2 hx,
    integral_pow_mul_exp 3 hx, integral_pow_mul_exp 5 hx]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num
  field_simp
  ring

/-! ## One-sided bounds on `G` from one-sided bounds on `e^{2x}` -/

/-- If `e^{2x} ≤ c` then `G(x) ≤ c·A(x) + B(x)`, where `A(x) = 120(x-1)²/x⁶ ≥ 0`. -/
theorem tf72G_le_of_exp_le {x c : ℝ} (hx : x ≠ 0) (h : Real.exp (2*x) ≤ c) :
    tf72G x ≤ c * (120 / x^4 - 240/x^5 + 120/x^6) + (-32/x + 80/x^3 + 120/x^4 - 120/x^6) := by
  have hA : 0 ≤ 120 / x^4 - 240/x^5 + 120/x^6 := by
    have he : 120 / x^4 - 240/x^5 + 120/x^6 = 120 * (x-1)^2 / x^6 := by
      field_simp
      ring
    rw [he]
    positivity
  have h1 : Real.exp (2*x) * (120 / x^4 - 240/x^5 + 120/x^6)
      ≤ c * (120 / x^4 - 240/x^5 + 120/x^6) := mul_le_mul_of_nonneg_right h hA
  calc tf72G x
      = Real.exp (2*x) * (120 / x^4 - 240/x^5 + 120/x^6)
          + (-32/x + 80/x^3 + 120/x^4 - 120/x^6) := by
        rw [tf72G_eq_exp x hx]
        ring
    _ ≤ c * (120 / x^4 - 240/x^5 + 120/x^6)
          + (-32/x + 80/x^3 + 120/x^4 - 120/x^6) := add_le_add_left h1 _

/-- If `c ≤ e^{2x}` then `c·A(x) + B(x) ≤ G(x)`, where `A(x) = 120(x-1)²/x⁶ ≥ 0`. -/
theorem tf72G_ge_of_exp_ge {x c : ℝ} (hx : x ≠ 0) (h : c ≤ Real.exp (2*x)) :
    c * (120 / x^4 - 240/x^5 + 120/x^6) + (-32/x + 80/x^3 + 120/x^4 - 120/x^6) ≤ tf72G x := by
  have hA : 0 ≤ 120 / x^4 - 240/x^5 + 120/x^6 := by
    have he : 120 / x^4 - 240/x^5 + 120/x^6 = 120 * (x-1)^2 / x^6 := by
      field_simp
      ring
    rw [he]
    positivity
  have h1 : c * (120 / x^4 - 240/x^5 + 120/x^6)
      ≤ Real.exp (2*x) * (120 / x^4 - 240/x^5 + 120/x^6) := mul_le_mul_of_nonneg_right h hA
  calc c * (120 / x^4 - 240/x^5 + 120/x^6) + (-32/x + 80/x^3 + 120/x^4 - 120/x^6)
      ≤ Real.exp (2*x) * (120 / x^4 - 240/x^5 + 120/x^6)
          + (-32/x + 80/x^3 + 120/x^4 - 120/x^6) := add_le_add_left h1 _
    _ = tf72G x := by
        rw [tf72G_eq_exp x hx]
        ring

/-! ## Rational exponential bounds -/

/-- Upper 10-digit bound for `e`. -/
theorem tf72_exp_one_upper : Real.exp 1 ≤ (2.7182818286 : ℝ) := Real.exp_one_lt_d9.le

/-- Lower 10-digit bound for `e`. -/
theorem tf72_exp_one_lower : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le

/-- Taylor upper bound for `e^r`, `0 ≤ r ≤ 1`, with nine terms. -/
theorem tf72_exp_le_taylor9 (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Real.exp r ≤ 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 + r ^ 6 / 720
      + r ^ 7 / 5040 + r ^ 8 / 40320 + r ^ 9 * (10 / 3265920) := by
  have h := Real.exp_bound' h0 h1 (n := 9) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- Taylor lower bound for `e^r`, `0 ≤ r ≤ 1`, with nine terms. -/
theorem tf72_exp_ge_taylor9 (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 + r ^ 6 / 720
      + r ^ 7 / 5040 + r ^ 8 / 40320 - r ^ 9 * (10 / 3265920) ≤ Real.exp r := by
  have habs : |r| ≤ 1 := abs_le.mpr ⟨by linarith, h1⟩
  have h := Real.exp_bound (x := r) habs (n := 9) (by norm_num)
  rw [abs_of_nonneg h0] at h
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  obtain ⟨h1', h2'⟩ := h
  linarith

/-- **Upper bound for `e^{n+r}`** (`n : ℕ`, `0 ≤ r ≤ 1`).  If the rational inequality on the
right holds, then `e^{n+r} ≤ c`; with `n`, `r`, `c` concrete this hypothesis is `norm_num`. -/
theorem tf72_exp_nat_add_frac_le (n : ℕ) {r c : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hc : (2.7182818286 : ℝ) ^ n * (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120
        + r ^ 6 / 720 + r ^ 7 / 5040 + r ^ 8 / 40320 + r ^ 9 * (10 / 3265920)) ≤ c) :
    Real.exp ((n : ℝ) + r) ≤ c := by
  have he : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) := tf72_exp_one_upper
  have ht := tf72_exp_le_taylor9 r h0 h1
  rw [Real.exp_add, show Real.exp (↑n) = Real.exp (1 : ℝ) ^ n from by
    rw [← Real.exp_nat_mul (1 : ℝ) n, mul_one]]
  refine le_trans (mul_le_mul (pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he n) ht
    (le_of_lt (Real.exp_pos r)) (pow_nonneg (by norm_num) n)) hc

/-- **Lower bound for `e^{n+r}`** (`n : ℕ`, `0 ≤ r ≤ 1`).  If the rational inequality on the
right holds, then `c ≤ e^{n+r}`. -/
theorem tf72_exp_nat_add_frac_ge (n : ℕ) {r c : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hc : c ≤ (2.7182818283 : ℝ) ^ n * (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120
        + r ^ 6 / 720 + r ^ 7 / 5040 + r ^ 8 / 40320 - r ^ 9 * (10 / 3265920))) :
    c ≤ Real.exp ((n : ℝ) + r) := by
  have he : (2.7182818283 : ℝ) ≤ Real.exp (1 : ℝ) := tf72_exp_one_lower
  have ht := tf72_exp_ge_taylor9 r h0 h1
  have hTnn : 0 ≤ 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 + r ^ 6 / 720
      + r ^ 7 / 5040 + r ^ 8 / 40320 - r ^ 9 * (10 / 3265920) := by
    have h9 : r ^ 9 ≤ 1 := by simpa using pow_le_pow_left₀ h0 h1 9
    have hrest : 0 ≤ r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 + r ^ 6 / 720
        + r ^ 7 / 5040 + r ^ 8 / 40320 := by positivity
    nlinarith [h9]
  rw [Real.exp_add, show Real.exp (↑n) = Real.exp (1 : ℝ) ^ n from by
    rw [← Real.exp_nat_mul (1 : ℝ) n, mul_one]]
  exact le_trans hc (mul_le_mul (pow_le_pow_left₀ (by norm_num) he n) ht hTnn
    (pow_nonneg (le_of_lt (Real.exp_pos 1)) n))

/-! ## The Laplace integral of `f_λ` is `G(c/λ)/30` -/

/-- **The real Laplace transform of HB Lemma 7.2's test function.**  Substituting `u = λt` in
`∫₀^{2/λ} e^{ct} f_λ(t)dt` cancels the factor `λ` of `f_λ = (λ/30)·(2-λt)³(4+6λt+λ²t²)` against
the Jacobian `1/λ` and leaves `G(c/λ)/30`. -/
theorem tf72f_int_exp (lam c : ℝ) (hlam : 0 < lam) :
    (∫ t in (0:ℝ)..(2/lam), Real.exp (c*t) * tf72f lam t) = tf72G (c/lam)/30 := by
  have hne : lam ≠ 0 := hlam.ne'
  -- on `[0, 2/λ]` the test function is the explicit polynomial of Lemma 7.2
  have hpoly : (∫ t in (0:ℝ)..(2/lam), Real.exp (c*t) * tf72f lam t)
      = ∫ t in (0:ℝ)..(2/lam),
          Real.exp (c*t) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (show (0:ℝ) ≤ 2/lam by positivity)] at ht
    rw [tf72f_eq_poly lam hlam t ht]
  rw [hpoly]
  -- write the integrand as `H (λ t)`
  have hsub : (∫ t in (0:ℝ)..(2/lam),
        Real.exp (c*t) * ((lam/30)*(2-lam*t)^3*(4+6*lam*t+lam^2*t^2)))
      = ∫ t in (0:ℝ)..(2/lam),
          (fun u : ℝ => (lam/30)*(Real.exp ((c/lam)*u)*((2-u)^3*(4+6*u+u^2)))) (lam*t) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only []
    have hzt : (c/lam)*(lam*t) = c*t := by field_simp
    rw [hzt]
    ring
  rw [hsub]
  -- substitute `u = λ t`
  rw [intervalIntegral.integral_comp_mul_left
    (fun u : ℝ => (lam/30)*(Real.exp ((c/lam)*u)*((2-u)^3*(4+6*u+u^2)))) hne]
  rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  -- identify the polynomial with HB's density `g`
  have hX : (∫ u in (0:ℝ)..2, Real.exp ((c/lam)*u)*((2-u)^3*(4+6*u+u^2)))
      = ∫ u in (0:ℝ)..2, (32 - 40*u^2 + 20*u^3 - u^5) * Real.exp ((c/lam)*u) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    ring
  rw [hX]
  unfold tf72G
  have hscal : ∀ Z : ℝ, lam⁻¹ * (lam/30 * Z) = Z/30 := by intro Z; field_simp
  rw [hscal]

/-! ## Dropping a vanishing tail of an interval integral -/

/-- If `F` vanishes on `[b,c]` then the integral over `[a,c]` may be truncated at `b`. -/
theorem intervalIntegral_eq_of_eqOn_zero {F : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcont : ContinuousOn F (Set.Icc a c)) (h0 : ∀ t ∈ Set.Icc b c, F t = 0) :
    ∫ t in a..c, F t = ∫ t in a..b, F t := by
  have hAb : ContinuousOn F (Set.Icc a b) :=
    hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hbc⟩)
  have hBc : ContinuousOn F (Set.Icc b c) :=
    hcont.mono (fun x hx => ⟨le_trans hab hx.1, hx.2⟩)
  have hA : IntervalIntegrable F MeasureTheory.volume a b := hAb.intervalIntegrable_of_Icc hab
  have hB : IntervalIntegrable F MeasureTheory.volume b c := hBc.intervalIntegrable_of_Icc hbc
  have hsplit : (∫ t in a..b, F t) + (∫ t in b..c, F t) = ∫ t in a..c, F t :=
    intervalIntegral.integral_add_adjacent_intervals hA hB
  have hzero : ∫ t in b..c, F t = 0 := by
    have hz : ∫ t in b..c, F t = ∫ t in b..c, (0:ℝ) :=
      intervalIntegral.integral_congr (fun t ht => by
        rw [Set.uIcc_of_le hbc] at ht
        exact h0 t ht)
    simpa using hz
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-! ## The five numerical clauses -/

theorem tf72_numeric_inputs : Work.ZeroFreeTables.TfNumericInputs := by
  unfold TfNumericInputs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `∫₀^{8/3} e^{0.348t} f_{3/4} ≤ 1.18`
    have h23 : (8:ℝ)/3 = 2/((3:ℝ)/4) := by norm_num
    rw [h23, tf72f_int_exp ((3:ℝ)/4) ((348:ℝ)/1000) (by norm_num)]
    rw [show ((348:ℝ)/1000)/((3:ℝ)/4) = (58:ℝ)/125 by norm_num]
    have hE : Real.exp (2 * ((58:ℝ)/125)) ≤ (25295:ℝ)/10000 := by
      rw [show 2 * ((58:ℝ)/125) = (116:ℝ)/125 by norm_num]
      have h := tf72_exp_nat_add_frac_le 0 (r := (116:ℝ)/125) (c := (25295:ℝ)/10000)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using h
    have hb := tf72G_le_of_exp_le (x := (58:ℝ)/125) (c := (25295:ℝ)/10000)
      (by norm_num) hE
    have har : (25295:ℝ)/10000
          * (120 / ((58:ℝ)/125)^4 - 240/((58:ℝ)/125)^5 + 120/((58:ℝ)/125)^6)
        + (-32/((58:ℝ)/125) + 80/((58:ℝ)/125)^3 + 120/((58:ℝ)/125)^4
            - 120/((58:ℝ)/125)^6) ≤ (118:ℝ)/100 * 30 := by norm_num
    have hstep : tf72G ((58:ℝ)/125) ≤ (118:ℝ)/100 * 30 := le_trans hb har
    linarith
  · -- `∫₀^{8/3} e^{0.82t} f_{3/4} ≤ 1.706`
    have h23 : (8:ℝ)/3 = 2/((3:ℝ)/4) := by norm_num
    rw [h23, tf72f_int_exp ((3:ℝ)/4) ((82:ℝ)/100) (by norm_num)]
    rw [show ((82:ℝ)/100)/((3:ℝ)/4) = (82:ℝ)/75 by norm_num]
    have hE : Real.exp (2 * ((82:ℝ)/75)) ≤ (8906:ℝ)/1000 := by
      rw [show 2 * ((82:ℝ)/75) = (164:ℝ)/75 by norm_num]
      have h := tf72_exp_nat_add_frac_le 2 (r := (14:ℝ)/75) (c := (8906:ℝ)/1000)
        (by norm_num) (by norm_num) (by norm_num)
      have h' : (↑(2:ℕ) : ℝ) + 14/75 = (164:ℝ)/75 := by norm_num
      rw [h'] at h
      exact h
    have hb := tf72G_le_of_exp_le (x := (82:ℝ)/75) (c := (8906:ℝ)/1000)
      (by norm_num) hE
    have har : (8906:ℝ)/1000
          * (120 / ((82:ℝ)/75)^4 - 240/((82:ℝ)/75)^5 + 120/((82:ℝ)/75)^6)
        + (-32/((82:ℝ)/75) + 80/((82:ℝ)/75)^3 + 120/((82:ℝ)/75)^4
            - 120/((82:ℝ)/75)^6) ≤ (1706:ℝ)/1000 * 30 := by norm_num
    have hstep : tf72G ((82:ℝ)/75) ≤ (1706:ℝ)/1000 * 30 := le_trans hb har
    linarith
  · -- `1262/1000 ≤ ∫₀^{8/3} e^{0.472t} f_{3/4}`
    have h23 : (8:ℝ)/3 = 2/((3:ℝ)/4) := by norm_num
    rw [h23, tf72f_int_exp ((3:ℝ)/4) ((472:ℝ)/1000) (by norm_num)]
    rw [show ((472:ℝ)/1000)/((3:ℝ)/4) = (236:ℝ)/375 by norm_num]
    have hE : (35206:ℝ)/10000 ≤ Real.exp (2 * ((236:ℝ)/375)) := by
      rw [show 2 * ((236:ℝ)/375) = (472:ℝ)/375 by norm_num]
      have h := tf72_exp_nat_add_frac_ge 1 (r := (97:ℝ)/375) (c := (35206:ℝ)/10000)
        (by norm_num) (by norm_num) (by norm_num)
      have h' : (↑(1:ℕ) : ℝ) + 97/375 = (472:ℝ)/375 := by norm_num
      rw [h'] at h
      exact h
    have hb := tf72G_ge_of_exp_ge (x := (236:ℝ)/375) (c := (35206:ℝ)/10000)
      (by norm_num) hE
    have har : (1262:ℝ)/1000 * 30
        ≤ (35206:ℝ)/10000
            * (120 / ((236:ℝ)/375)^4 - 240/((236:ℝ)/375)^5 + 120/((236:ℝ)/375)^6)
          + (-32/((236:ℝ)/375) + 80/((236:ℝ)/375)^3 + 120/((236:ℝ)/375)^4
              - 120/((236:ℝ)/375)^6) := by norm_num
    have hstep : (1262:ℝ)/1000 * 30 ≤ tf72G ((236:ℝ)/375) := le_trans har hb
    linarith
  · -- `∫₀^{8/3} e^{0.348t} f_{17/20} ≤ 11105/10000` (support truncated at `40/17`)
    show (∫ t in (0:ℝ)..(8/3), Real.exp (((348:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t)
        ≤ (11105:ℝ)/10000
    have hcont : ContinuousOn
        (fun t : ℝ => Real.exp (((348:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t)
        (Set.Icc 0 (8/3)) := by
      have hlin : Continuous (fun t : ℝ => ((348:ℝ)/1000) * t) :=
        continuous_const.mul continuous_id
      exact (Real.continuous_exp.comp hlin).continuousOn.mul
        ((tf72f_cont ((17:ℝ)/20) (by norm_num)).mono (fun t ht => ht.1))
    have hzero : ∀ t ∈ Set.Icc ((40:ℝ)/17) (8/3),
        Real.exp (((348:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t = 0 := by
      intro t ht
      have ht2 : (2:ℝ)/((17:ℝ)/20) ≤ t := by
        rw [show (2:ℝ)/((17:ℝ)/20) = (40:ℝ)/17 by norm_num]
        exact ht.1
      rw [tf72f_supp ((17:ℝ)/20) (by norm_num) t ht2, mul_zero]
    rw [intervalIntegral_eq_of_eqOn_zero (a := (0:ℝ)) (b := (40:ℝ)/17) (c := (8:ℝ)/3)
      (by norm_num) (by norm_num) hcont hzero]
    rw [show (40:ℝ)/17 = 2/((17:ℝ)/20) by norm_num,
      tf72f_int_exp ((17:ℝ)/20) ((348:ℝ)/1000) (by norm_num)]
    rw [show ((348:ℝ)/1000)/((17:ℝ)/20) = (174:ℝ)/425 by norm_num]
    have hE : Real.exp (2 * ((174:ℝ)/425)) ≤ (22678305:ℝ)/10000000 := by
      rw [show 2 * ((174:ℝ)/425) = (348:ℝ)/425 by norm_num]
      have h := tf72_exp_nat_add_frac_le 0 (r := (348:ℝ)/425) (c := (22678305:ℝ)/10000000)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using h
    have hb := tf72G_le_of_exp_le (x := (174:ℝ)/425) (c := (22678305:ℝ)/10000000)
      (by norm_num) hE
    have har : (22678305:ℝ)/10000000
          * (120 / ((174:ℝ)/425)^4 - 240/((174:ℝ)/425)^5 + 120/((174:ℝ)/425)^6)
        + (-32/((174:ℝ)/425) + 80/((174:ℝ)/425)^3 + 120/((174:ℝ)/425)^4
            - 120/((174:ℝ)/425)^6) ≤ (11105:ℝ)/10000 * 30 := by norm_num
    have hstep : tf72G ((174:ℝ)/425) ≤ (11105:ℝ)/10000 * 30 := le_trans hb har
    linarith
  · -- `68/100 ≤ ∫₀^{8/3} e^{-0.472t} f_{17/20}` (support truncated at `40/17`)
    show (68:ℝ)/100 ≤ (∫ t in (0:ℝ)..(8/3),
        Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t)
    have hcont : ContinuousOn
        (fun t : ℝ => Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t)
        (Set.Icc 0 (8/3)) := by
      have hlin : Continuous (fun t : ℝ => ((472:ℝ)/1000) * t) :=
        continuous_const.mul continuous_id
      exact (Real.continuous_exp.comp hlin.neg).continuousOn.mul
        ((tf72f_cont ((17:ℝ)/20) (by norm_num)).mono (fun t ht => ht.1))
    have hzero : ∀ t ∈ Set.Icc ((40:ℝ)/17) (8/3),
        Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t = 0 := by
      intro t ht
      have ht2 : (2:ℝ)/((17:ℝ)/20) ≤ t := by
        rw [show (2:ℝ)/((17:ℝ)/20) = (40:ℝ)/17 by norm_num]
        exact ht.1
      rw [tf72f_supp ((17:ℝ)/20) (by norm_num) t ht2, mul_zero]
    rw [intervalIntegral_eq_of_eqOn_zero (a := (0:ℝ)) (b := (40:ℝ)/17) (c := (8:ℝ)/3)
      (by norm_num) (by norm_num) hcont hzero]
    rw [show (40:ℝ)/17 = 2/((17:ℝ)/20) by norm_num]
    have hcongr : (∫ t in (0:ℝ)..(2/((17:ℝ)/20)),
          Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t)
        = ∫ t in (0:ℝ)..(2/((17:ℝ)/20)),
          Real.exp ((-(472:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [show -(((472:ℝ)/1000) * t) = (-(472:ℝ)/1000) * t by ring]
    rw [hcongr, tf72f_int_exp ((17:ℝ)/20) (-(472:ℝ)/1000) (by norm_num)]
    rw [show (-(472:ℝ)/1000)/((17:ℝ)/20) = -(236:ℝ)/425 by norm_num]
    have hexp : Real.exp ((472:ℝ)/425) ≤ (303615:ℝ)/100000 := by
      have h := tf72_exp_nat_add_frac_le 1 (r := (47:ℝ)/425) (c := (303615:ℝ)/100000)
        (by norm_num) (by norm_num) (by norm_num)
      have h' : (↑(1:ℕ) : ℝ) + 47/425 = (472:ℝ)/425 := by norm_num
      rw [h'] at h
      exact h
    have hD : (329362:ℝ)/1000000 ≤ Real.exp (2 * (-(236:ℝ)/425)) := by
      have h1 : 2 * (-(236:ℝ)/425) = -((472:ℝ)/425) := by norm_num
      have h2 : Real.exp (-((472:ℝ)/425)) = 1 / Real.exp ((472:ℝ)/425) := by
        rw [Real.exp_neg, one_div]
      rw [h1, h2]
      exact le_trans (by norm_num : (329362:ℝ)/1000000 ≤ 1 / ((303615:ℝ)/100000))
        (one_div_le_one_div_of_le (Real.exp_pos ((472:ℝ)/425)) hexp)
    have hb := tf72G_ge_of_exp_ge (x := -(236:ℝ)/425) (c := (329362:ℝ)/1000000)
      (by norm_num) hD
    have har : (68:ℝ)/100 * 30
        ≤ (329362:ℝ)/1000000
            * (120 / (-(236:ℝ)/425)^4 - 240/(-(236:ℝ)/425)^5 + 120/(-(236:ℝ)/425)^6)
          + (-32/(-(236:ℝ)/425) + 80/(-(236:ℝ)/425)^3 + 120/(-(236:ℝ)/425)^4
              - 120/(-(236:ℝ)/425)^6) := by norm_num
    have hstep : (68:ℝ)/100 * 30 ≤ tf72G (-(236:ℝ)/425) := le_trans har hb
    linarith

end

end Work.ZeroFreeTables.HB95plus
