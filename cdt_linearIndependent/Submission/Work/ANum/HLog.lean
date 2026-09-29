import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.CNum.log_norm_hauptH

/-! # `log ‖h(q)‖` as a convergent sum, for `‖q‖ < 1`

The hauptmodul `h(q) = -256 q ∏'ₙ (1 + qⁿ⁺¹)²⁴` of `Submission.CDTPlan` satisfies

  `log ‖h(q)‖ = log 256 + log ‖q‖ + ∑' n, 24 log ‖1 + qⁿ⁺¹‖`

for every `q` with `‖q‖ < 1`.  This is `Work.CNum.log_norm_hauptH` with the hypothesis relaxed from
`‖q‖ ≤ 3/4` to `‖q‖ < 1`: the Theorem-A image of `ψ_A` has `‖ψ_A‖ ≤ 0.7824 > 3/4`, so the sharper
constant of the `Work.CNum` version is not available here.  The proof is the same. -/

namespace Work.ANum

open scoped BigOperators

theorem log_norm_hauptH_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    Real.log ‖Submission.CDTPlan.hauptH q‖ =
      Real.log 256 + Real.log ‖q‖ + ∑' n : ℕ, 24 * Real.log ‖1 + q ^ (n + 1)‖ := by
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hqgeosum : Summable (fun n : ℕ => q ^ n) := summable_geometric_iff_norm_lt_one.mpr hq
  have hqgeoshift : Summable (fun n : ℕ => q ^ (n + 1)) := (summable_nat_add_iff 1).2 hqgeosum
  have hgnorm : Summable (fun n : ℕ => ‖q ^ (n + 1)‖) := by
    simpa [norm_pow] using hqgeoshift.norm
  have hlogsum : Summable (fun n : ℕ => Real.log ‖1 + q ^ (n + 1)‖) :=
    hgnorm.summable_log_norm_one_add
  have hlog24sum : Summable (fun n : ℕ => Real.log (‖1 + q ^ (n + 1)‖ ^ 24)) := by
    have h := hlogsum.mul_left 24
    refine h.congr (fun n => ?_)
    rw [Real.log_pow]
    push_cast
    ring
  have hwpos : ∀ n : ℕ, 0 < ‖1 + q ^ (n + 1)‖ := by
    intro n
    have h1 : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero n)
    have h2 : (1 : ℝ) - ‖q ^ (n + 1)‖ ≤ ‖1 + q ^ (n + 1)‖ := by
      have h3 := norm_add_le (1 + q ^ (n + 1)) (-(q ^ (n + 1)))
      rw [show (1 + q ^ (n + 1)) + -(q ^ (n + 1)) = 1 by ring, norm_one, norm_neg] at h3
      linarith
    linarith
  have hPpos : 0 < ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    have hprod := Real.rexp_tsum_eq_tprod (f := fun n : ℕ => ‖1 + q ^ (n + 1)‖ ^ 24)
      (fun n => pow_pos (hwpos n) 24) hlog24sum
    rw [← hprod]
    exact Real.exp_pos _
  have hlogP : Real.log (∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24) =
      ∑' n : ℕ, 24 * Real.log ‖1 + q ^ (n + 1)‖ := by
    have hprod := Real.rexp_tsum_eq_tprod (f := fun n : ℕ => ‖1 + q ^ (n + 1)‖ ^ 24)
      (fun n => pow_pos (hwpos n) 24) hlog24sum
    rw [← hprod, Real.log_exp]
    exact tsum_congr (fun n => by rw [Real.log_pow]; push_cast; ring)
  have hg : Multipliable (fun n : ℕ => 1 + q ^ (n + 1)) :=
    Complex.multipliable_one_add_of_summable hqgeoshift
  have hg24 : Multipliable (fun n : ℕ => (1 + q ^ (n + 1)) ^ 24) := hg.pow 24
  have hnorm_tprod : ‖∏' n : ℕ, (1 + q ^ (n + 1)) ^ 24‖ =
      ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    rw [hg24.norm_tprod]
    exact tprod_congr (fun n => by rw [norm_pow])
  have hnormH : ‖Submission.CDTPlan.hauptH q‖ =
      256 * ‖q‖ * ∏' n : ℕ, ‖1 + q ^ (n + 1)‖ ^ 24 := by
    rw [Submission.CDTPlan.hauptH]
    rw [norm_mul, norm_mul, hnorm_tprod, norm_neg, Complex.norm_ofNat]
  rw [hnormH, Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hqpos)) (ne_of_gt hPpos),
    Real.log_mul (by norm_num) (ne_of_gt hqpos), hlogP]

end Work.ANum
