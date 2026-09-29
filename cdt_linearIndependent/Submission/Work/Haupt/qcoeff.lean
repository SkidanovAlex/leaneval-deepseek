import Mathlib
import Submission.Work.Haupt.qp_defs

/-!
# The coefficients of Euler's `q`-exponential

For a complex number `q` we set

`qcoeff q n = q^{n(n-1)/2} / (q;q)_n`, i.e. `qhalf q n / qpNat q q n`,

the `n`-th coefficient of Euler's identity

`∏'_{n≥0} (1 + w q^n) = ∑'_{n≥0} q^{n(n-1)/2} w^n / (q;q)_n`.

The fundamental relation between consecutive coefficients is

`qcoeff q (n+1) * (1 - q^{n+1}) = qcoeff q n * q^n`,

equivalently `qcoeff q n * q^n + qcoeff q (n+1) * q^{n+1} = qcoeff q (n+1)`.
-/

open scoped BigOperators

namespace Work.Haupt

/-- The coefficients `qcoeff q n = qhalf q n / qpNat q q n` of Euler's `q`-exponential. -/
noncomputable def qcoeff (q : ℂ) (n : ℕ) : ℂ := qhalf q n / qpNat q q n

@[simp] lemma qcoeff_zero (q : ℂ) : qcoeff q 0 = 1 := by simp [qcoeff]

/-- `qcoeff q n * w^n` is the summand of the right hand side of Euler's identity,
written as in the statement. -/
lemma qcoeff_mul_pow (q w : ℂ) (n : ℕ) :
    qcoeff q n * w ^ n = qhalf q n * w ^ n / qpNat q q n := by
  rw [qcoeff, div_mul_eq_mul_div]

lemma qcoeff_rec_div {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qcoeff q (n + 1) = qcoeff q n * q ^ n / (1 - q ^ (n + 1)) := by
  have hne : qpNat q q n ≠ 0 := qpNat_self_ne_zero hq n
  have h1 : q ^ (n + 1) = q * q ^ n := pow_succ' q n
  rw [qcoeff, qcoeff, h1, qhalf_succ, qpNat_succ]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring_nf

/-- The fundamental recurrence of the coefficients. -/
lemma qcoeff_rec {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qcoeff q (n + 1) * (1 - q ^ (n + 1)) = qcoeff q n * q ^ n := by
  have hne3 : (1 - q ^ (n + 1)) ≠ 0 := by
    intro h
    have hp : q ^ (n + 1) = 1 := (sub_eq_zero.mp h).symm
    have hlt := pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
    rw [← norm_pow, hp, norm_one] at hlt
    exact lt_irrefl 1 hlt
  rw [qcoeff_rec_div hq n, div_mul_cancel₀ _ hne3]

/-- The additive form of the recurrence. -/
lemma qcoeff_rec_add {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qcoeff q n * q ^ n + qcoeff q (n + 1) * q ^ (n + 1) = qcoeff q (n + 1) := by
  have h := qcoeff_rec hq n
  linear_combination -h

end Work.Haupt
