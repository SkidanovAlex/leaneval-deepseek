import Mathlib
import Submission.RS

/-! Endpoint values of the Rudin-Shapiro polynomials at `±1` (paper Lemma 3.9 area,
used for `Re H` near `x = 0` and `x = T·π`).  For `t = 2k` with `k ≥ 1`:
`P_t(1) = P_t(-1) = Q_t(1) = 2^k`, `Q_t(-1) = -2^k` (at `t = 0` one has
`P_0 = Q_0 = 1`, so `Q_0(-1) = 1 ≠ -2^0`; the published display omits this `k ≥ 1`
exception, which is immaterial since only odd levels are used in the paper).
For `t = 2k+1`: `P_t(1) = Q_t(-1) = 2^(k+1)`, `P_t(-1) = Q_t(1) = 0`.
`(-1 : ℂ)` denotes the complex number `-1`. -/

open scoped Polynomial
open Polynomial

namespace Submission
namespace RudinShapiro

/-! Helpers: the "double step" recurrences `t ↦ t+2` used to evaluate `P`, `Q` at
`z = ±1`.  Since `P_{t+2} = P_{t+1} + X^(2^(t+1)) Q_{t+1}` and
`Q_{t+2} = P_{t+1} - X^(2^(t+1)) Q_{t+1}`, at a point `z` with `z^(2^(t+1)) = 1`
(and also `z^(2^t) = 1` for `Q`) we get the plain doubling
`P_{t+2}(z) = 2 P_t(z)`, `Q_{t+2}(z) = 2 Q_t(z)`.  For `z = 1` this holds for
every `t`; for `z = -1` it holds once `t ≥ 1` (as then `2^t` and `2^(t+1)` are even). -/

/-- `2^t` is even once `t ≥ 1`. -/
private lemma even_two_pow {t : ℕ} (ht : 1 ≤ t) : Even (2 ^ t) := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  rw [hu, pow_succ, mul_comm]
  exact even_two_mul (2 ^ u)

/-- `(-1)^(2^t) = 1` once `t ≥ 1` (then `2^t` is even). -/
private lemma neg_one_pow_two_pow {t : ℕ} (ht : 1 ≤ t) : (-1 : ℂ) ^ 2 ^ t = 1 :=
  Even.neg_one_pow (even_two_pow ht)

/-- `P_{t+2}(z) = 2 P_t(z)` provided `z^(2^(t+1)) = 1`. -/
private lemma eval_P_two_step {t : ℕ} {z : ℂ} (hv : z ^ 2 ^ (t + 1) = 1) :
    (P (t + 2)).eval z = 2 * (P t).eval z := by
  rw [eval_P_succ (t + 1) z, eval_P_succ t z, eval_Q_succ t z]
  rw [hv]
  ring

/-- `Q_{t+2}(z) = 2 Q_t(z)` provided `z^(2^t) = 1` and `z^(2^(t+1)) = 1`. -/
private lemma eval_Q_two_step {t : ℕ} {z : ℂ} (hu : z ^ 2 ^ t = 1)
    (hv : z ^ 2 ^ (t + 1) = 1) : (Q (t + 2)).eval z = 2 * (Q t).eval z := by
  rw [eval_Q_succ (t + 1) z, eval_P_succ t z, eval_Q_succ t z]
  rw [hu, hv]
  ring

/-- `2 * 2^n = 2^(n+1)` (complex powers). -/
private lemma two_mul_pow_succ (n : ℕ) : (2 : ℂ) * (2 : ℂ) ^ n = (2 : ℂ) ^ (n + 1) := by
  rw [pow_succ]
  ring

/-- `Q_{2(k+1)}(-1) = -2^(k+1)`, the version of `Q_eval_neg_one_even` that starts at
`t = 2` (the degenerate `Q_0 = 1` has `Q_0(-1) = 1`, not `-1`). -/
private lemma Q_eval_neg_one_even_core (k : ℕ) :
    ((Q (2 * (k + 1))).eval (-1 : ℂ)) = -(2 ^ (k + 1)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hk : 2 * ((k + 1) + 1) = (2 * (k + 1)) + 2 := by omega
      rw [hk]
      have hstep : (Q (2 * (k + 1) + 2)).eval (-1 : ℂ) =
          2 * (Q (2 * (k + 1))).eval (-1 : ℂ) := by
        exact eval_Q_two_step (t := 2 * (k + 1)) (z := (-1 : ℂ))
          (neg_one_pow_two_pow (t := 2 * (k + 1)) (by omega))
          (neg_one_pow_two_pow (t := 2 * (k + 1) + 1) (by omega))
      calc
        (Q (2 * (k + 1) + 2)).eval (-1 : ℂ) = 2 * (Q (2 * (k + 1))).eval (-1 : ℂ) := hstep
        _ = 2 * -(2 ^ (k + 1)) := by rw [ih]
        _ = -(2 ^ ((k + 1) + 1)) := by rw [pow_succ]; ring

lemma P_eval_one_even (k : ℕ) : ((P (2 * k)).eval 1) = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : 2 * (k + 1) = (2 * k) + 2 := by omega
      have hstep : (P (2 * k + 2)).eval (1 : ℂ) = 2 * (P (2 * k)).eval (1 : ℂ) := by
        exact eval_P_two_step (t := 2 * k) (z := (1 : ℂ)) (by simp)
      rw [hk]
      calc
        (P (2 * k + 2)).eval (1 : ℂ) = 2 * (P (2 * k)).eval (1 : ℂ) := hstep
        _ = 2 * (2 ^ k) := by rw [ih]
        _ = 2 ^ (k + 1) := two_mul_pow_succ k

lemma P_eval_neg_one_even (k : ℕ) : ((P (2 * k)).eval (-1 : ℂ)) = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : 2 * (k + 1) = (2 * k) + 2 := by omega
      have hstep : (P (2 * k + 2)).eval (-1 : ℂ) = 2 * (P (2 * k)).eval (-1 : ℂ) := by
        exact eval_P_two_step (t := 2 * k) (z := (-1 : ℂ))
          (neg_one_pow_two_pow (t := 2 * k + 1) (by omega))
      rw [hk]
      calc
        (P (2 * k + 2)).eval (-1 : ℂ) = 2 * (P (2 * k)).eval (-1 : ℂ) := hstep
        _ = 2 * (2 ^ k) := by rw [ih]
        _ = 2 ^ (k + 1) := two_mul_pow_succ k

lemma Q_eval_one_even (k : ℕ) : ((Q (2 * k)).eval 1) = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : 2 * (k + 1) = (2 * k) + 2 := by omega
      have hstep : (Q (2 * k + 2)).eval (1 : ℂ) = 2 * (Q (2 * k)).eval (1 : ℂ) := by
        exact eval_Q_two_step (t := 2 * k) (z := (1 : ℂ)) (by simp) (by simp)
      rw [hk]
      calc
        (Q (2 * k + 2)).eval (1 : ℂ) = 2 * (Q (2 * k)).eval (1 : ℂ) := hstep
        _ = 2 * (2 ^ k) := by rw [ih]
        _ = 2 ^ (k + 1) := two_mul_pow_succ k

/-- For `t = 2k` with `k ≥ 1`: `Q_t(-1) = -2^k`.

NOTE (deviation from the parent's original statement, which quantified over all
`k : ℕ`): the all-`k` version is *false* at `k = 0`: `Q_0 = 1`, hence
`Q_0(-1) = 1`, while `-2^0 = -1`.  (The published paper's display
`P_{2t}(1) = ... = -Q_{2t}(-1) = 2^t` carries the same harmless typo; only odd
levels are ever used there, where the corresponding identity is `Q_{2t+1}(-1) = 2^{t+1}`.)
The statement below is the correct form. -/
lemma Q_eval_neg_one_even (k : ℕ) (hk : 1 ≤ k) : ((Q (2 * k)).eval (-1 : ℂ)) = -(2 ^ k) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [hm]
  exact Q_eval_neg_one_even_core m

lemma P_eval_one_odd (k : ℕ) : ((P (2 * k + 1)).eval 1) = 2 ^ (k + 1) := by
  induction k with
  | zero => simp [P_succ]; norm_num
  | succ k ih =>
      have hk : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have hstep : (P (2 * k + 1 + 2)).eval (1 : ℂ) = 2 * (P (2 * k + 1)).eval (1 : ℂ) := by
        exact eval_P_two_step (t := 2 * k + 1) (z := (1 : ℂ)) (by simp)
      rw [hk]
      calc
        (P (2 * k + 1 + 2)).eval (1 : ℂ) = 2 * (P (2 * k + 1)).eval (1 : ℂ) := hstep
        _ = 2 * (2 ^ (k + 1)) := by rw [ih]
        _ = 2 ^ (k + 2) := by
          rw [show k + 2 = (k + 1) + 1 by omega]
          exact two_mul_pow_succ (k + 1)

lemma P_eval_neg_one_odd (k : ℕ) : ((P (2 * k + 1)).eval (-1 : ℂ)) = 0 := by
  induction k with
  | zero => simp [P_succ]
  | succ k ih =>
      have hk : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have hstep : (P (2 * k + 1 + 2)).eval (-1 : ℂ) = 2 * (P (2 * k + 1)).eval (-1 : ℂ) := by
        exact eval_P_two_step (t := 2 * k + 1) (z := (-1 : ℂ))
          (neg_one_pow_two_pow (t := 2 * k + 2) (by omega))
      rw [hk, hstep, ih]
      ring

lemma Q_eval_one_odd (k : ℕ) : ((Q (2 * k + 1)).eval 1) = 0 := by
  induction k with
  | zero => simp [Q_succ]
  | succ k ih =>
      have hk : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have hstep : (Q (2 * k + 1 + 2)).eval (1 : ℂ) = 2 * (Q (2 * k + 1)).eval (1 : ℂ) := by
        exact eval_Q_two_step (t := 2 * k + 1) (z := (1 : ℂ)) (by simp) (by simp)
      rw [hk, hstep, ih]
      ring

lemma Q_eval_neg_one_odd (k : ℕ) : ((Q (2 * k + 1)).eval (-1 : ℂ)) = 2 ^ (k + 1) := by
  induction k with
  | zero => simp [Q_succ]; norm_num
  | succ k ih =>
      have hk : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have hstep : (Q (2 * k + 1 + 2)).eval (-1 : ℂ) = 2 * (Q (2 * k + 1)).eval (-1 : ℂ) := by
        exact eval_Q_two_step (t := 2 * k + 1) (z := (-1 : ℂ))
          (neg_one_pow_two_pow (t := 2 * k + 1) (by omega))
          (neg_one_pow_two_pow (t := 2 * k + 2) (by omega))
      rw [hk]
      calc
        (Q (2 * k + 1 + 2)).eval (-1 : ℂ) = 2 * (Q (2 * k + 1)).eval (-1 : ℂ) := hstep
        _ = 2 * (2 ^ (k + 1)) := by rw [ih]
        _ = 2 ^ (k + 2) := by
          rw [show k + 2 = (k + 1) + 1 by omega]
          exact two_mul_pow_succ (k + 1)

/-- For odd `t`: `P_t(1) = 2^((t+1)/2)`. -/
lemma P_eval_one_of_odd {t : ℕ} (ht : Odd t) :
    ((P t).eval 1) = 2 ^ ((t + 1) / 2) := by
  rcases ht with ⟨k, hk⟩
  rw [hk]
  rw [P_eval_one_odd]
  congr 1
  omega

/-- For odd `t`: `P_t(-1) = 0`. -/
lemma P_eval_neg_one_of_odd {t : ℕ} (ht : Odd t) :
    ((P t).eval (-1 : ℂ)) = 0 := by
  rcases ht with ⟨k, hk⟩
  rw [hk]
  exact P_eval_neg_one_odd k

/-- For odd `t`: `Q_t(1) = 0`. -/
lemma Q_eval_one_of_odd {t : ℕ} (ht : Odd t) :
    ((Q t).eval 1) = 0 := by
  rcases ht with ⟨k, hk⟩
  rw [hk]
  exact Q_eval_one_odd k

/-- For odd `t`: `Q_t(-1) = 2^((t+1)/2)`. -/
lemma Q_eval_neg_one_of_odd {t : ℕ} (ht : Odd t) :
    ((Q t).eval (-1 : ℂ)) = 2 ^ ((t + 1) / 2) := by
  rcases ht with ⟨k, hk⟩
  rw [hk]
  rw [Q_eval_neg_one_odd]
  congr 1
  omega

end RudinShapiro
end Submission
