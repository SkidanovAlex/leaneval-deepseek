import Mathlib

/-! Numerical/transcendental constants needed throughout the proof
(paper arXiv:1907.09464v1).  The exact rational bounds below are proved once
here and imported wherever a numeric inequality is verified:

  • log 2 ≤ 0.7                  (`Real.log_two_le_70`)
  • π ≤ 22/7                     (`Real.pi_le_22_div_7`)
  • e^x ≤ 1/(1−x) for 0 ≤ x < 1  (`Real.exp_le_inv_sub_one`)

ROUTE for `log 2 ≤ 0.7`: `log 2 ≤ 7/10` iff `2 ≤ exp (7/10)` (monotonicity,
`Real.log_le_log` / `Real.exp_le_exp`).  Prove `2 ≤ exp (7/10)` by Taylor:
`Real.exp_bound (x = 7/10) (n = 5)` gives `exp(7/10) ≥ Σ_{m<5} (7/10)^m/m! − err`
(or combine `Real.add_one_le_exp` etc.), then `norm_num`.  `(7/10 : ℝ)`.

ROUTE for `π ≤ 22/7`: classic: for `0 ≤ x ≤ 1`, `x^4 (1−x)^4 / (1+x^2) ≥ 0`, and

    ∫_0^1 x^4(1−x)^4/(1+x^2) dx = 22/7 − π

because `x^4 (1−x)^4 = (1+x^2)(x^6 − 4x^5 + 5x^4 − 4x^2 + 4) − 4` and
`∫_0^1 1/(1+x^2) dx = arctan 1 = π/4`.  Use `intervalIntegral` + `deriv_arctan`
(FTC: `intervalIntegral.integral_deriv_eq_sub`), `Real.arctan_one`,
`Real.arctan_zero`, and `norm_num` for the polynomial parts.

ROUTE for the exp bound: `Real.exp_bound` with `|x| ≤ 1`, or prove directly
`1 ≤ (1−x)·exp x` for `0 ≤ x < 1` using the series or derivatives
(`deriv` of `(1−x)·exp x` is `−x·exp x ≤ 0`, and value at 0 is 1). -/

noncomputable section
open scoped BigOperators
open MeasureTheory
open intervalIntegral

set_option autoImplicit false

namespace Submission
namespace Consts

/-- `log 2 ≤ 0.7`. -/
lemma log_two_le_70 : Real.log 2 ≤ (70 : ℝ) / 100 := by
  -- `2 ≤ exp(7/10)`: lower bound `exp x ≥ ∑_{m<7} x^m / m!` for `x ≥ 0`,
  -- and the partial sum (7 terms, m = 0..6) already exceeds `2`.
  have hx : 0 ≤ (70 : ℝ) / 100 := by norm_num
  have hsum := Real.sum_le_exp_of_nonneg hx 7
  have hle_sum : (2 : ℝ) ≤ ∑ m ∈ Finset.range 7, ((70 : ℝ) / 100) ^ m / (m.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have h2 : (2 : ℝ) ≤ Real.exp ((70 : ℝ) / 100) := le_trans hle_sum hsum
  -- `log` is the inverse of `exp` on the positives
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h2
  exact Real.exp_le_exp.mp h2

/-- `π ≤ 22/7`. -/
lemma pi_le_22_div_7 : Real.pi ≤ (22 : ℝ) / 7 := by
  -- sharp library bound `π < 3.1416` (mathlib `Real.pi_lt_d4`) implies `π < 22/7`
  exact le_of_lt (lt_trans Real.pi_lt_d4 (by norm_num : (3.1416 : ℝ) < (22 : ℝ) / 7))

/-- `exp x ≤ 1/(1−x)` for `0 ≤ x < 1`. -/
lemma exp_le_inv_sub_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  exact Real.exp_bound_div_one_sub_of_interval hx0 hx1

/-- `e^x ≤ 1 + x + x^2` for `0 ≤ x ≤ 1/2` (looser but often enough). -/
lemma exp_le_one_add_add_sq {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  -- `Real.exp_bound'` (Taylor with remainder, `n = 3`):
  -- `exp x ≤ 1 + x + x²/2 + (2/9)x³`, and for `0 ≤ x ≤ 1/2` this is `≤ 1 + x + x²`.
  have h1 : x ≤ 1 := by linarith
  have hb := Real.exp_bound' hx0 h1 (n := 3) (by norm_num)
  calc
    Real.exp x ≤ (∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ)) +
        x ^ 3 * (3 + 1) / ((3 : ℕ).factorial * 3) := hb
    _ = 1 + x + x ^ 2 / 2 + (2 / 9) * x ^ 3 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
      ring
    _ ≤ 1 + x + x ^ 2 := by
      nlinarith [sq_nonneg x, mul_nonneg hx0 (mul_nonneg hx0 hx0)]

/-- `π < 3.2` (weaker, quick corollary of `pi_le_22_div_7`). -/
lemma pi_lt_32 : Real.pi < 32 / 10 := by
  exact lt_of_le_of_lt pi_le_22_div_7 (by norm_num : (22 : ℝ) / 7 < (32 : ℝ) / 10)

end Consts
end Submission
