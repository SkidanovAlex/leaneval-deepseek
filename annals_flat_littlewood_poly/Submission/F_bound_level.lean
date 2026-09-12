import Mathlib
import Submission.RSPsum_defs
import Submission.F_Psum_small
import Submission.F_Qsum_small
import Submission.F_Psum_large
import Submission.F_Qsum_large

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

/-! Level bound: for `m ≤ 2^t`, partial sums of the first `m` coefficients of `P t`
(or `Q t`) have sup-norm on the unit circle at most `4 * sqrt(2^t)`.

Proof sketch: induction on `t`.
- `t = 0`: `m ≤ 1`, direct.
- step `t+1`, `m ≤ 2^(t+1)`:
  * if `m ≤ 2^t`: use `Psum_small`, `Qsum_small` and the induction hypothesis, then
    `sqrt (2^t) ≤ sqrt (2^(t+1))`.
  * else write `m = 2^t + m'` with `0 < m' ≤ 2^t`.  Use `Psum_large` / `Qsum_large`,
    so `Psum (t+1) m = P t + X^(2^t) * Qsum t m'` (resp. with minus).  Bound its evaluation
    by `‖(P t).eval z‖ + ‖(Qsum t m').eval z‖ ≤ sqrt(2^(t+1)) + 4*sqrt(2^t)` using
    `norm_P_eval_le`, `norm_Q_eval_le` and the hypothesis, and finally show
    `sqrt (2^(t+1)) + 4 * sqrt (2^t) ≤ 4 * sqrt (2^(t+1))`.
Use `Real.sqrt_mul_self`, `Real.sq_sqrt`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul` as needed;
note `2^(t+1) = 2 * 2^t` (as reals). -/

/-- Monotonicity of `Real.sqrt` for powers of two. -/
private lemma sqrt_pow_two_mono (t : ℕ) :
    Real.sqrt ((2 : ℝ) ^ t) ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  apply Real.sqrt_le_sqrt
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) t]

/-- `sqrt (2^(t+1)) + 4 * sqrt (2^t) ≤ 4 * sqrt (2^(t+1))`. -/
private lemma sqrt_succ_add_bound (t : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (t + 1)) + 4 * Real.sqrt ((2 : ℝ) ^ t)
      ≤ 4 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  let a : ℝ := Real.sqrt ((2 : ℝ) ^ t)
  let b : ℝ := Real.sqrt ((2 : ℝ) ^ (t + 1))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : b ^ 2 = 2 * a ^ 2 := by
    dsimp [a, b]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    rw [pow_succ]
    ring
  have h43 : 4 * a ≤ 3 * b := by nlinarith
  dsimp [a, b] at h43 ⊢
  nlinarith

/-- On the unit circle, multiplication by `X^(2^t)` does not increase the norm of
the evaluation of a polynomial at `z`. -/
private lemma norm_eval_X_pow_mul_le (t : ℕ) (q : ℂ[X]) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(X ^ 2 ^ t * q).eval z‖ ≤ ‖q.eval z‖ := by
  calc
    ‖(X ^ 2 ^ t * q).eval z‖ = ‖z ^ 2 ^ t * q.eval z‖ := by
      rw [Polynomial.eval_mul]
      simp
    _ ≤ ‖z ^ 2 ^ t‖ * ‖q.eval z‖ := norm_mul_le _ _
    _ = ‖q.eval z‖ := by
      have hp : ‖z ^ 2 ^ t‖ = 1 := by
        rw [norm_pow, hz]
        simp
      rw [hp, one_mul]

lemma Psum_bound_level (t m : ℕ) (hm : m ≤ 2 ^ t) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(Psum t m).eval z‖ ≤ 4 * Real.sqrt (2 ^ t) ∧
    ‖(Qsum t m).eval z‖ ≤ 4 * Real.sqrt (2 ^ t) := by
  induction t generalizing m z with
  | zero =>
      have hm1 : m ≤ 1 := by simpa using hm
      interval_cases m
      · simp [Psum, Qsum]
      · constructor
        · rw [eval_Psum]; simp
        · rw [eval_Qsum]; simp
  | succ t ih =>
      by_cases hsmall : m ≤ 2 ^ t
      · have hPsmall : Psum (t + 1) m = Psum t m := Psum_small t m hsmall
        have hQsmall : Qsum (t + 1) m = Psum t m := Qsum_small t m hsmall
        have hPih : ‖(Psum t m).eval z‖ ≤ 4 * Real.sqrt (2 ^ t) := (ih m hsmall z hz).1
        have hmono : 4 * Real.sqrt (2 ^ t) ≤ 4 * Real.sqrt (2 ^ (t + 1)) := by
          exact mul_le_mul_of_nonneg_left (sqrt_pow_two_mono t) (by norm_num)
        constructor
        · calc
            ‖(Psum (t + 1) m).eval z‖ = ‖(Psum t m).eval z‖ := by rw [hPsmall]
            _ ≤ 4 * Real.sqrt (2 ^ t) := hPih
            _ ≤ 4 * Real.sqrt (2 ^ (t + 1)) := hmono
        · calc
            ‖(Qsum (t + 1) m).eval z‖ = ‖(Psum t m).eval z‖ := by rw [hQsmall]
            _ ≤ 4 * Real.sqrt (2 ^ t) := hPih
            _ ≤ 4 * Real.sqrt (2 ^ (t + 1)) := hmono
      · have hgt : 2 ^ t < m := by omega
        rw [pow_two_succ] at hm
        let m' := m - 2 ^ t
        have hm' : m' ≤ 2 ^ t := by dsimp [m']; omega
        have hmsplit : m = 2 ^ t + m' := by dsimp [m']; omega
        have hQih : ‖(Qsum t m').eval z‖ ≤ 4 * Real.sqrt (2 ^ t) := (ih m' hm' z hz).2
        have hnormP : ‖(P t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1)) := norm_P_eval_le t z hz
        constructor
        · calc
            ‖(Psum (t + 1) m).eval z‖
                = ‖(Psum (t + 1) (2 ^ t + m')).eval z‖ := by rw [hmsplit]
            _ = ‖(P t + X ^ 2 ^ t * Qsum t m').eval z‖ := by rw [Psum_large]
            _ ≤ ‖(P t).eval z‖ + ‖(Qsum t m').eval z‖ := by
                calc
                  ‖(P t + X ^ 2 ^ t * Qsum t m').eval z‖
                      = ‖(P t).eval z + (X ^ 2 ^ t * Qsum t m').eval z‖ := by simp
                  _ ≤ ‖(P t).eval z‖ + ‖(X ^ 2 ^ t * Qsum t m').eval z‖ := norm_add_le _ _
                  _ ≤ ‖(P t).eval z‖ + ‖(Qsum t m').eval z‖ := by
                      exact add_le_add (le_refl ‖(P t).eval z‖)
                        (norm_eval_X_pow_mul_le t (Qsum t m') z hz)
            _ ≤ Real.sqrt (2 ^ (t + 1)) + 4 * Real.sqrt (2 ^ t) := by
                exact add_le_add hnormP hQih
            _ ≤ 4 * Real.sqrt (2 ^ (t + 1)) := sqrt_succ_add_bound t
        · calc
            ‖(Qsum (t + 1) m).eval z‖
                = ‖(Qsum (t + 1) (2 ^ t + m')).eval z‖ := by rw [hmsplit]
            _ = ‖(P t - X ^ 2 ^ t * Qsum t m').eval z‖ := by rw [Qsum_large]
            _ ≤ ‖(P t).eval z‖ + ‖(Qsum t m').eval z‖ := by
                calc
                  ‖(P t - X ^ 2 ^ t * Qsum t m').eval z‖
                      = ‖(P t).eval z - (X ^ 2 ^ t * Qsum t m').eval z‖ := by simp
                  _ ≤ ‖(P t).eval z‖ + ‖(X ^ 2 ^ t * Qsum t m').eval z‖ := norm_sub_le _ _
                  _ ≤ ‖(P t).eval z‖ + ‖(Qsum t m').eval z‖ := by
                      exact add_le_add (le_refl ‖(P t).eval z‖)
                        (norm_eval_X_pow_mul_le t (Qsum t m') z hz)
            _ ≤ Real.sqrt (2 ^ (t + 1)) + 4 * Real.sqrt (2 ^ t) := by
                exact add_le_add hnormP hQih
            _ ≤ 4 * Real.sqrt (2 ^ (t + 1)) := sqrt_succ_add_bound t

end RudinShapiro
end Submission
