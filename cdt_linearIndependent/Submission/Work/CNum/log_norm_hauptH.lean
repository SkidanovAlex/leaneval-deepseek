import Mathlib
import Submission.Work.CNum.Basic

/-! # `log ‖h(q)‖` as an explicit convergent sum

For `‖q‖ ≤ 3/4` the hauptmodul `h(q) = -256 q ∏'ₙ (1 + qⁿ⁺¹)²⁴` of
`Submission.CDTPlan` satisfies

  `log ‖h(q)‖ = log 256 + log ‖q‖ + ∑' n, 24 log ‖1 + qⁿ⁺¹‖`.

This is the multiplicative-to-additive rewrite used by the certified numerics:
each factor `1 + qⁿ⁺¹` has modulus `≥ 1 - ‖q‖ⁿ⁺¹ ≥ 1/4 > 0`, so all logarithms
below are those of positive real numbers and the logarithmic series converges
geometrically.
-/

namespace Work.CNum

open scoped BigOperators

theorem log_norm_hauptH {q : ℂ} (hq : ‖q‖ ≤ 3 / 4) (hq0 : q ≠ 0) :
    Real.log ‖Submission.CDTPlan.hauptH q‖ =
      Real.log 256 + Real.log ‖q‖ + ∑' n : ℕ, 24 * Real.log ‖1 + q ^ (n + 1)‖ := by
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  -- geometric summability of the powers of `q` and of the perturbations `1 + q ^ (n+1)`
  have hqgeosum : Summable (fun n : ℕ => q ^ n) := summable_geometric_iff_norm_lt_one.mpr hq1
  have hqgeoshift : Summable (fun n : ℕ => q ^ (n + 1)) := (summable_nat_add_iff 1).2 hqgeosum
  have hgnorm : Summable (fun n : ℕ => ‖q ^ (n + 1)‖) := by
    simpa [norm_pow] using hqgeoshift.norm
  -- convergence of the logarithmic series, and of its `24`-scaled variant
  have hlogsum : Summable (fun n : ℕ => Real.log ‖1 + q ^ (n + 1)‖) :=
    hgnorm.summable_log_norm_one_add
  have hlog24sum : Summable (fun n : ℕ => Real.log (‖1 + q ^ (n + 1)‖ ^ 24)) := by
    have h := hlogsum.mul_left 24
    refine h.congr (fun n => ?_)
    rw [Real.log_pow]
    push_cast
    ring
  -- every factor has modulus at least `1 - ‖q‖ ^ (n+1) ≥ 1/4 > 0`
  have hwpos : ∀ n : ℕ, 0 < ‖1 + q ^ (n + 1)‖ := by
    intro n
    have h1 : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      calc ‖q‖ ^ (n + 1) ≤ (3 / 4 : ℝ) ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hq _
        _ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
    have h2 : (1 : ℝ) - ‖q ^ (n + 1)‖ ≤ ‖1 + q ^ (n + 1)‖ := by
      have h3 := norm_add_le (1 + q ^ (n + 1)) (-(q ^ (n + 1)))
      rw [show (1 + q ^ (n + 1)) + -(q ^ (n + 1)) = 1 by ring, norm_one, norm_neg] at h3
      linarith
    linarith
  -- the real infinite product is a positive exponential
  have hPpos : 0 < ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    have hprod := Real.rexp_tsum_eq_tprod (f := fun n : ℕ => ‖1 + q ^ (n + 1)‖ ^ 24)
      (fun n => pow_pos (hwpos n) 24) hlog24sum
    rw [← hprod]
    exact Real.exp_pos _
  -- `log` of the real infinite product is the sum of the logs
  have hlogP : Real.log (∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24) =
      ∑' n : ℕ, 24 * Real.log ‖1 + q ^ (n + 1)‖ := by
    have hprod := Real.rexp_tsum_eq_tprod (f := fun n : ℕ => ‖1 + q ^ (n + 1)‖ ^ 24)
      (fun n => pow_pos (hwpos n) 24) hlog24sum
    rw [← hprod, Real.log_exp]
    exact tsum_congr (fun n => by rw [Real.log_pow]; push_cast; ring)
  -- norm of the complex infinite product
  have hg : Multipliable (fun n : ℕ => 1 + q ^ (n + 1)) :=
    Complex.multipliable_one_add_of_summable hqgeoshift
  have hg24 : Multipliable (fun n : ℕ => (1 + q ^ (n + 1)) ^ 24) := hg.pow 24
  have hnorm_tprod : ‖∏' n : ℕ, (1 + q ^ (n + 1)) ^ 24‖ =
      ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    rw [hg24.norm_tprod]
    refine tprod_congr (fun n => ?_)
    rw [norm_pow]
  have hnormH : ‖Submission.CDTPlan.hauptH q‖ =
      256 * ‖q‖ * ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    rw [Submission.CDTPlan.hauptH]
    rw [norm_mul, norm_mul, hnorm_tprod, norm_neg, Complex.norm_ofNat]
  rw [hnormH, Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hqpos)) (ne_of_gt hPpos),
    Real.log_mul (by norm_num) (ne_of_gt hqpos), hlogP]

end Work.CNum
