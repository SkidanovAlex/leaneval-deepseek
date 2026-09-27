import Mathlib
import Submission.Work.Drive.N2Lead.smoothTransition_mul_deriv_le

/-!
# The derivative of `Real.smoothTransition` is bounded by `2`

We prove `|deriv Real.smoothTransition x| ≤ 2` for every real `x`.

Mathlib's smooth transition function is
`Real.smoothTransition x = expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`,
so it is `0` on `(-∞, 0]`, `1` on `[1, ∞)`, increasing, and (strictly) between `0` and `1`
on `(0, 1)`.  Its derivative vanishes off `(0, 1)`, is nonnegative (monotonicity), and its
maximum on `(0, 1)` equals `2`, attained at `x = 1/2`; hence `|deriv smoothTransition| ≤ 2`.

The estimate is obtained as follows.  Writing `A = x⁻¹`, `B = (1 - x)⁻¹` for `x ∈ (0, 1)`,
the quotient rule together with `deriv expNegInvGlue y = y⁻² * expNegInvGlue y` gives

`deriv smoothTransition x = (A ^ 2 + B ^ 2) / (2 + exp (A - B) + exp (B - A))`,

where we used `A * B = A + B` (both sides equal `(x * (1 - x))⁻¹`).  It therefore suffices to
prove the two-variable inequality

`A ^ 2 + B ^ 2 ≤ 2 * (2 + exp (A - B) + exp (B - A))`   whenever `A * B = A + B`.

For this, put `s = A - B` and `m = A * B = A + B`.  Then `A ^ 2 + B ^ 2 = 2 * m + s ^ 2` and
`m ^ 2 = 4 * m + s ^ 2` (both from `(A ± B) ^ 2`).  From the quadratic lower bound
`exp t + exp (-t) ≥ 2 + t ^ 2` (i.e. `cosh t ≥ 1 + t ^ 2 / 2`, proved below from
`sinh t ≥ t` on `t ≥ 0`) we get `s ^ 2 ≤ exp (A - B) + exp (B - A) - 2`; it remains to show
`2 * m ≤ 8 + s ^ 2`, which follows from `m ^ 2 = 4 * m + s ^ 2` by splitting on `m ≤ 4`.

The quadratic exponential bound `exp t + exp (-t) - 2 = (exp (t / 2) - exp (-(t / 2))) ^ 2 =
(2 * sinh (t / 2)) ^ 2 ≥ t ^ 2` uses `Real.self_le_sinh_iff` (`t ≤ sinh t ↔ 0 ≤ t`) and
`Real.abs_sinh`.
-/

namespace Work.N2Lead

/-- The quadratic lower bound `exp t + exp (-t) ≥ 2 + t ^ 2`, equivalently `cosh t ≥ 1 + t ^ 2 / 2`.

Indeed `exp t + exp (-t) - 2 = (2 * sinh (t / 2)) ^ 2 ≥ t ^ 2`. -/
lemma sq_le_exp_add_exp_neg_sub_two (s : ℝ) :
    s ^ 2 ≤ Real.exp s + Real.exp (-s) - 2 := by
  have key : Real.exp s + Real.exp (-s) - 2 = (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 := by
    have h1 : Real.exp (s / 2) * Real.exp (s / 2) = Real.exp s := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(s / 2)) * Real.exp (-(s / 2)) = Real.exp (-s) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [sub_sq]
    nlinarith [h1, h2, h3]
  rw [key]
  have hsinh : Real.exp (s / 2) - Real.exp (-(s / 2)) = 2 * Real.sinh (s / 2) := by
    rw [Real.sinh_eq]; ring
  rw [hsinh]
  have h1 : |s / 2| ≤ |Real.sinh (s / 2)| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hsq : (s / 2) ^ 2 ≤ Real.sinh (s / 2) ^ 2 := (sq_le_sq).mpr h1
  nlinarith [hsq]

/-- The two-variable inequality behind the bound: if `A * B = A + B` then
`A ^ 2 + B ^ 2 ≤ 2 * (2 + exp (A - B) + exp (B - A))`.

(For `A = x⁻¹`, `B = (1 - x)⁻¹` the hypothesis holds, and the left-hand side over the
bracket is exactly `deriv smoothTransition x`.) -/
lemma core_ineq {A B : ℝ} (hAB : A * B = A + B) :
    A ^ 2 + B ^ 2 ≤ 2 * (2 + Real.exp (A - B) + Real.exp (B - A)) := by
  have hs : (A - B) ^ 2 ≤ Real.exp (A - B) + Real.exp (B - A) - 2 := by
    have h := sq_le_exp_add_exp_neg_sub_two (A - B)
    have h2 : Real.exp (-(A - B)) = Real.exp (B - A) := by ring_nf
    rwa [h2] at h
  have hsum : A ^ 2 + B ^ 2 = 2 * (A * B) + (A - B) ^ 2 := by nlinarith [hAB]
  have hm : (A * B) ^ 2 = 4 * (A * B) + (A - B) ^ 2 := by nlinarith [hAB]
  have hmb : 2 * (A * B) ≤ 8 + (A - B) ^ 2 := by
    rcases le_or_gt (A * B) 4 with h | h
    · nlinarith [sq_nonneg (A - B)]
    · have hpos : 0 ≤ (A * B - 2) * (A * B - 4) := mul_nonneg (by linarith) (by linarith)
      nlinarith [hm, hpos]
  nlinarith [hs, hsum, hmb]

/-- The derivative of `Real.smoothTransition` on `(0, 1)`, in the form used for the bound. -/
lemma deriv_smoothTransition_eq_frac {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    deriv Real.smoothTransition x =
      (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) /
        (2 + Real.exp (x⁻¹ - (1 - x)⁻¹) + Real.exp ((1 - x)⁻¹ - x⁻¹)) := by
  rw [Work.Drive.N2Lead.deriv_smoothTransition_eq]
  have hxA : expNegInvGlue x = Real.exp (-(x⁻¹)) := by
    rw [expNegInvGlue, if_neg (not_le.mpr h0)]
  have hxB : expNegInvGlue (1 - x) = Real.exp (-((1 - x)⁻¹)) := by
    rw [expNegInvGlue, if_neg (show ¬ (1 - x ≤ 0) by linarith)]
  rw [hxA, hxB]
  have hpq : Real.exp (-(x⁻¹)) * Real.exp (-((1 - x)⁻¹)) = Real.exp (-(x⁻¹ + (1 - x)⁻¹)) := by
    rw [← Real.exp_add]; ring_nf
  have hp : Real.exp (-(x⁻¹)) * Real.exp (-(x⁻¹)) = Real.exp (-2 * x⁻¹) := by
    rw [← Real.exp_add]; ring_nf
  have hq : Real.exp (-((1 - x)⁻¹)) * Real.exp (-((1 - x)⁻¹)) = Real.exp (-2 * (1 - x)⁻¹) := by
    rw [← Real.exp_add]; ring_nf
  have h1' : Real.exp (-(x⁻¹)) * Real.exp (-((1 - x)⁻¹)) * Real.exp (x⁻¹ - (1 - x)⁻¹)
      = Real.exp (-2 * (1 - x)⁻¹) := by
    rw [hpq, ← Real.exp_add]; ring_nf
  have h2' : Real.exp (-(x⁻¹)) * Real.exp (-((1 - x)⁻¹)) * Real.exp ((1 - x)⁻¹ - x⁻¹)
      = Real.exp (-2 * x⁻¹) := by
    rw [hpq, ← Real.exp_add]; ring_nf
  have hmain : Real.exp (-(x⁻¹)) * Real.exp (-((1 - x)⁻¹)) *
        (2 + Real.exp (x⁻¹ - (1 - x)⁻¹) + Real.exp ((1 - x)⁻¹ - x⁻¹))
      = (Real.exp (-(x⁻¹)) + Real.exp (-((1 - x)⁻¹))) ^ 2 := by
    rw [mul_add, mul_add, h1', h2']
    nlinarith [hp, hq, hpq]
  have hpne : Real.exp (-(x⁻¹)) + Real.exp (-((1 - x)⁻¹)) ≠ 0 := by positivity
  have hrne : 2 + Real.exp (x⁻¹ - (1 - x)⁻¹) + Real.exp ((1 - x)⁻¹ - x⁻¹) ≠ 0 := by positivity
  rw [div_eq_div_iff (pow_ne_zero 2 hpne) hrne]
  nlinarith [congrArg (fun t => (x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) * t) hmain]

/-- The derivative of `Real.smoothTransition` vanishes on `(-∞, 0]`. -/
lemma deriv_smoothTransition_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  rw [Work.Drive.N2Lead.deriv_smoothTransition_eq, expNegInvGlue.zero_of_nonpos hx]
  simp

/-- The derivative of `Real.smoothTransition` vanishes on `[1, ∞)`. -/
lemma deriv_smoothTransition_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rw [Work.Drive.N2Lead.deriv_smoothTransition_eq,
    expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)]
  simp

/-- The key estimate: `deriv Real.smoothTransition x ≤ 2` for `0 < x < 1`. -/
lemma deriv_smoothTransition_le_two_of_pos_of_lt_one {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    deriv Real.smoothTransition x ≤ 2 := by
  have hx0 : x ≠ 0 := ne_of_gt h0
  have hx1 : (1 : ℝ) - x ≠ 0 := by linarith
  have hAB : x⁻¹ * (1 - x)⁻¹ = x⁻¹ + (1 - x)⁻¹ := by field_simp; ring
  have hcore : x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2 ≤
      2 * (2 + Real.exp (x⁻¹ - (1 - x)⁻¹) + Real.exp ((1 - x)⁻¹ - x⁻¹)) :=
    core_ineq hAB
  rw [deriv_smoothTransition_eq_frac h0 h1,
    div_le_iff₀ (by positivity :
      (0 : ℝ) < 2 + Real.exp (x⁻¹ - (1 - x)⁻¹) + Real.exp ((1 - x)⁻¹ - x⁻¹))]
  exact hcore

theorem absDerivSmoothTransitionLeTwo (x : ℝ) : |deriv Real.smoothTransition x| ≤ 2 := by
  have hnn : 0 ≤ deriv Real.smoothTransition x :=
    Real.smoothTransition.monotone.deriv_nonneg
  rw [abs_of_nonneg hnn]
  rcases le_or_gt x 0 with hx | hx
  · rw [deriv_smoothTransition_eq_zero_of_nonpos hx]; norm_num
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [deriv_smoothTransition_eq_zero_of_one_le hx1]; norm_num
  · exact deriv_smoothTransition_le_two_of_pos_of_lt_one hx hx1

end Work.N2Lead
