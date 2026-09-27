import Mathlib

/-!
# The key convexity inequality of Mathlib's smooth transition function

For `x ∈ [1/2, 1]` we prove

`(2 * x - 1) * deriv Real.smoothTransition x ≤ 2 * Real.smoothTransition x - 1`,

i.e. that `β ↦ 2 * smoothTransition ((1+β)/2) - 1` is concave on `[0,1]` with value `0` at `β = 0`.

The proof is the one in the assignment docstring, made explicit:

* `deriv_smoothTransition_eq` computes the derivative of `Real.smoothTransition` from the quotient
  rule and `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul`;
* `smoothTransition_rat_ineq` is the polynomial inequality, obtained by clearing denominators and
  factorising the resulting polynomial as `(2*x-1)^3 * (3*x^2-3*x+1)`;
* `sinh_lower_bound` is the Taylor lower bound `2u + u^3/3 ≤ 2 sinh u` for `u ≥ 0`, deduced from
  the power series `Real.hasSum_sinh` and `Summable.sum_le_tsum`.

No `sorry`, no `axiom`.
-/

open Polynomial

namespace Work.Drive.N2Lead

/-- Derivative of `expNegInvGlue`, in the form used for the quotient rule.

Equivalently `deriv expNegInvGlue x = x⁻² * expNegInvGlue x`. -/
lemma deriv_expNegInvGlue (x : ℝ) :
    deriv expNegInvGlue x = x⁻¹ ^ 2 * expNegInvGlue x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  simpa using h.deriv

/-- The derivative of `Real.smoothTransition` at every real point. -/
lemma deriv_smoothTransition_eq (x : ℝ) :
    deriv Real.smoothTransition x =
      expNegInvGlue x * expNegInvGlue (1 - x) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 := by
  have hga : HasDerivAt expNegInvGlue (x⁻¹^2 * expNegInvGlue x) x := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  have hgb' : HasDerivAt expNegInvGlue ((1-x)⁻¹^2 * expNegInvGlue (1-x)) (1 - x) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) (1 - x)
  have h1 : HasDerivAt (fun y : ℝ => (1:ℝ) - y) (-1) x := by
    exact (hasDerivAt_id' x).const_sub (1:ℝ)
  have hgb : HasDerivAt (fun y => expNegInvGlue (1 - y))
      (-((1-x)⁻¹^2 * expNegInvGlue (1-x))) x := by
    have h3 := hgb'.comp x h1
    convert h3 using 1 <;> try rfl
    ring
  have hden : HasDerivAt (fun y => expNegInvGlue y + expNegInvGlue (1 - y))
      (x⁻¹^2 * expNegInvGlue x - (1-x)⁻¹^2 * expNegInvGlue (1-x)) x := by
    have h := hga.add hgb
    convert h using 1 <;> try rfl
  have hne : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 := (Real.smoothTransition.pos_denom x).ne'
  have hmain : HasDerivAt Real.smoothTransition
      (((x⁻¹^2 * expNegInvGlue x) * (expNegInvGlue x + expNegInvGlue (1 - x)) -
        expNegInvGlue x * (x⁻¹^2 * expNegInvGlue x - (1-x)⁻¹^2 * expNegInvGlue (1-x))) /
        (expNegInvGlue x + expNegInvGlue (1 - x))^2) x := by
    have h := hga.div hden hne
    convert h using 1 <;> try rfl
  rw [hmain.deriv]
  field_simp
  ring

/-- The Taylor lower bound `2*u + u^3/3 ≤ 2 * sinh u` for `u ≥ 0`, from the power series of `sinh`
(all of whose terms are nonnegative on `[0, ∞)`). -/
lemma sinh_lower_bound (u : ℝ) (hu : 0 ≤ u) : 2 * u + u ^ 3 / 3 ≤ 2 * Real.sinh u := by
  have hnonneg : ∀ n : ℕ, 0 ≤ u ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
    intro n; positivity
  have hle := (Real.hasSum_sinh u).summable.sum_le_tsum ({0, 1} : Finset ℕ) (fun n _ => hnonneg n)
  rw [(Real.hasSum_sinh u).tsum_eq] at hle
  have hkey : ((∑ i ∈ ({0, 1} : Finset ℕ), u ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)))
      = u + u^3/6 := by
    norm_num [Finset.sum_insert]
  rw [hkey] at hle
  linarith

/-- The polynomial (rational) inequality behind the convexity estimate: for `x ∈ [1/2, 1)`,
`(2x-1) * (x⁻² + (1-x)⁻²) ≤ 2 s + s^3/3` where `s = (1-x)⁻¹ - x⁻¹ = (2x-1)/(x(1-x))`.

Clearing the denominators reduces it to `(2x-1)^3 * (3x^2 - 3x + 1) ≥ 0`. -/
lemma smoothTransition_rat_ineq {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x < 1) :
    (2 * x - 1) * (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) ≤
      2 * ((1 - x)⁻¹ - x⁻¹) + ((1 - x)⁻¹ - x⁻¹) ^ 3 / 3 := by
  have hx0 : x ≠ 0 := by linarith
  have h1x0 : 1 - x ≠ 0 := by linarith
  have hs : (1-x)⁻¹ - x⁻¹ = (2*x-1)/(x*(1-x)) := by
    field_simp
    ring
  rw [hs]
  have hfac : 3*x^3*(1-x)^3 * (2*((2*x-1)/(x*(1-x))) + ((2*x-1)/(x*(1-x)))^3/3)
      - 3*x^3*(1-x)^3 * ((2*x-1) * (x⁻¹^2 + (1-x)⁻¹^2))
      = (2*x-1)^3*(3*x^2-3*x+1) := by
    field_simp
    ring
  have hnonneg : 0 ≤ (2*x-1)^3*(3*x^2-3*x+1) := by
    have hq : 0 ≤ 3*x^2-3*x+1 := by nlinarith [sq_nonneg (x - 1/2)]
    exact mul_nonneg (pow_nonneg (by linarith : 0 ≤ 2*x-1) 3) hq
  have hpos : 0 < 3*x^3*(1-x)^3 := by positivity
  nlinarith [hfac, hnonneg, hpos]

/-- **The key convexity inequality of Mathlib's smooth transition.**

For every `x ∈ [1/2, 1]`,  `(2 * x - 1) * deriv Real.smoothTransition x ≤ 2 * Real.smoothTransition x - 1`.

(Equivalently: the function `β ↦ 2 * smoothTransition ((1+β)/2) - 1` is concave on `[0,1]` with value
`0` at `β = 0`, i.e. `y ↦ 2 * smoothTransition ((y+εp)/(2*εp)) - 1` has `y * deriv ≤ value` on `y ≥ 0`.)

Proof plan. For `x ∈ (0,1)` put `a = expNegInvGlue x = exp (-1/x)`, `b = expNegInvGlue (1-x) =
exp (-1/(1-x))`, so `smoothTransition x = a / (a+b) = exp s / (1 + exp s)` and
`deriv Real.smoothTransition x = exp s / (1 + exp s)^2 * s'`, where `s = (2*x-1)/(x*(1-x))` and
`s' = 1/x^2 + 1/(1-x)^2`.  (The `s'` computation is the quotient rule
`deriv (a/(a+b)) = (a'b - ab')/(a+b)^2` together with `deriv expNegInvGlue x = x^{-2} *
expNegInvGlue x`, which is `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x`.)  Multiplying the
goal by the positive number `(1 + exp s)^2 / exp s`, the goal becomes exactly
`(2*x-1) * s' ≤ exp s - exp (-s) = 2 * sinh s`.  Now put `β = 2*x-1 ∈ [0,1)` and `q = 1-β^2`; then
`s = 4β/q` and `(2*x-1) * s' = 8β(1+β^2)/q^2`.  The Taylor lower bound `u + u^3/6 ≤ sinh u`
(valid for `u ≥ 0`; from `Real.hasSum_sinh` and `Summable.sum_le_tsum` for the Finset `{0,1}`, both
terms `u` and `u^3/6` being nonnegative) gives
`2 * sinh s ≥ 8β/q + 64β^3/(3q^3)`, and it remains to check
`8β(1+β^2)/q^2 ≤ 8β/q + 64β^3/(3q^3)`, i.e. after multiplying by `q^3`:
`8βq^2 + 64β^3/3 - 8β(1+β^2)q = 16β^3(β^2 + 1/3) ≥ 0`.  The endpoints are immediate: `x = 1/2`
gives `0 ≤ 0`, and at `x = 1` one has `smoothTransition 1 = 1` and `deriv smoothTransition 1 = 0`
(the function is constantly `1` on `[1,∞)`), giving `0 ≤ 1`. -/
theorem smoothTransition_mul_deriv_le {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (2 * x - 1) * deriv Real.smoothTransition x ≤ 2 * Real.smoothTransition x - 1 := by
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1
    rw [deriv_smoothTransition_eq, Real.smoothTransition.one]
    norm_num
  · have hx0 : (0:ℝ) < x := by linarith [hx.1]
    have h1x0 : (0:ℝ) < 1 - x := by linarith
    have hneA : expNegInvGlue x ≠ 0 := (expNegInvGlue.pos_of_pos hx0).ne'
    have hneB : expNegInvGlue (1-x) ≠ 0 := (expNegInvGlue.pos_of_pos h1x0).ne'
    have hexpA : expNegInvGlue x = Real.exp (-x⁻¹) := by
      rw [expNegInvGlue]; rw [if_neg (not_le.mpr hx0)]
    have hexpB : expNegInvGlue (1 - x) = Real.exp (-(1-x)⁻¹) := by
      rw [expNegInvGlue]; rw [if_neg (not_le.mpr h1x0)]
    have hratio : expNegInvGlue x / expNegInvGlue (1 - x) = Real.exp ((1-x)⁻¹ - x⁻¹) := by
      rw [hexpA, hexpB, ← Real.exp_sub]
      congr 1
      ring
    have hratio' : expNegInvGlue (1 - x) / expNegInvGlue x = Real.exp (-((1-x)⁻¹ - x⁻¹)) := by
      rw [hexpA, hexpB, ← Real.exp_sub]
      congr 1
      ring
    have hsinh : 2 * Real.sinh ((1-x)⁻¹ - x⁻¹)
        = expNegInvGlue x / expNegInvGlue (1 - x) - expNegInvGlue (1 - x) / expNegInvGlue x := by
      rw [Real.sinh_eq, hratio, hratio']
      ring
    have hs_form : (1-x)⁻¹ - x⁻¹ = (2*x-1)/(x*(1-x)) := by
      field_simp
      ring
    have hs_nonneg : 0 ≤ (1-x)⁻¹ - x⁻¹ := by
      rw [hs_form]
      exact div_nonneg (by linarith [hx.1]) (le_of_lt (mul_pos hx0 h1x0))
    have hkey : (2*x-1) * (x⁻¹^2 + (1-x)⁻¹^2) ≤ 2 * Real.sinh ((1-x)⁻¹ - x⁻¹) :=
      le_trans (smoothTransition_rat_ineq hx.1 h1) (sinh_lower_bound _ hs_nonneg)
    rw [deriv_smoothTransition_eq]
    change (2*x-1) * (expNegInvGlue x * expNegInvGlue (1-x) * (x⁻¹^2 + (1-x)⁻¹^2)
        / (expNegInvGlue x + expNegInvGlue (1-x))^2)
      ≤ 2 * (expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1-x))) - 1
    have hfacnonneg : 0 ≤ expNegInvGlue x * expNegInvGlue (1-x)
        / (expNegInvGlue x + expNegInvGlue (1-x))^2 := by
      have hABpos : 0 < expNegInvGlue x * expNegInvGlue (1-x) :=
        mul_pos (expNegInvGlue.pos_of_pos hx0) (expNegInvGlue.pos_of_pos h1x0)
      exact div_nonneg hABpos.le (sq_nonneg _)
    have hne : expNegInvGlue x + expNegInvGlue (1-x) ≠ 0 := (Real.smoothTransition.pos_denom x).ne'
    calc (2*x-1) * (expNegInvGlue x * expNegInvGlue (1-x) * (x⁻¹^2 + (1-x)⁻¹^2)
            / (expNegInvGlue x + expNegInvGlue (1-x))^2)
        = ((2*x-1) * (x⁻¹^2 + (1-x)⁻¹^2))
            * (expNegInvGlue x * expNegInvGlue (1-x) / (expNegInvGlue x + expNegInvGlue (1-x))^2) := by ring
      _ ≤ (2 * Real.sinh ((1-x)⁻¹ - x⁻¹))
            * (expNegInvGlue x * expNegInvGlue (1-x) / (expNegInvGlue x + expNegInvGlue (1-x))^2) :=
          mul_le_mul_of_nonneg_right hkey hfacnonneg
      _ = 2 * (expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1-x))) - 1 := by
          rw [hsinh]
          field_simp
          ring

end Work.Drive.N2Lead
