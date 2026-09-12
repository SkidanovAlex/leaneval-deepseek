import Mathlib
import Submission.S6Core

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex
set_option autoImplicit false

namespace Submission
namespace NumBounds

/-! The even sine polynomial `s_e` is `O(√q)`:

   `Sec3.abs_s_e_le s t q hsq θ` gives
   `|Sec3.s_e s t q θ| ≤ 6·√(q+1) + 2·√(2^(t+1))`.
   Show the RHS is `≤ 9·√q` under `1 ≤ (q:ℝ)` and `(2:ℝ)^(t+3) ≤ (q:ℝ)`:
   - `2·√(2^(t+1)) ≤ √q` (square both sides using `2^(t+3) ≤ q`);
   - `6·√(q+1) ≤ 8·√q`: square both sides: `36·(q+1) ≤ 64·q` ⟺ `q ≥ 2`.
   Suggested: prove `√(q+1) ≤ (4/3)·√q` by `Real.le_sqrt` (square: `q+1 ≤ 16q/9`),
   or directly `6·√(q+1) ≤ 8·√q` via `nlinarith` after using `Real.le_sqrt`. -/

/-- `(2:ℝ)^(t+3) = 4 * (2:ℝ)^(t+1)`. -/
lemma pow_t_add_three (t : ℕ) : (2 : ℝ) ^ (t + 3) = 4 * (2 : ℝ) ^ (t + 1) := by
  have hsucc : t + 3 = (t + 1) + 2 := by omega
  rw [hsucc, pow_add, pow_two]
  ring

/-- `2 ≤ q` follows from `(2:ℝ)^(t+3) ≤ q` (as `t+3 ≥ 3`, so `2 ≤ 2^(t+3)`). -/
lemma two_le_of_pow_le {t q : ℕ} (ht : (2 : ℝ) ^ (t + 3) ≤ (q : ℝ)) : (2 : ℝ) ≤ (q : ℝ) := by
  have hge3 : 3 ≤ t + 3 := by omega
  have hpowmono : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (t + 3) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hge3
  exact le_trans (by norm_num : (2 : ℝ) ≤ (2 : ℝ) ^ 3) (le_trans hpowmono ht)

/-- The small (`P_t`) contribution is at most `√q`. -/
lemma two_sqrt_pow_le_sqrt {t q : ℕ} (ht : (2 : ℝ) ^ (t + 3) ≤ (q : ℝ)) :
    2 * Real.sqrt ((2 : ℝ) ^ (t + 1)) ≤ Real.sqrt (q : ℝ) := by
  refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpow := pow_t_add_three t
  rw [hpow] at ht
  nlinarith

/-- The `6·√(q+1)` contribution is at most `8·√q`, provided `q ≥ 2`. -/
lemma six_sqrt_add_le_eight_sqrt {q : ℕ} (hq2 : (2 : ℝ) ≤ (q : ℝ)) :
    6 * Real.sqrt ((q : ℝ) + 1) ≤ 8 * Real.sqrt (q : ℝ) := by
  have hnonneg1 : 0 ≤ 6 * Real.sqrt ((q : ℝ) + 1) := by positivity
  have hnonneg2 : 0 ≤ 8 * Real.sqrt (q : ℝ) := by positivity
  have hsq : (6 * Real.sqrt ((q : ℝ) + 1)) ^ 2 ≤ (8 * Real.sqrt (q : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (q : ℝ) + 1),
      Real.sq_sqrt (by positivity : 0 ≤ (q : ℝ))]
    nlinarith [hq2]
  have habs : |6 * Real.sqrt ((q : ℝ) + 1)| ≤ |8 * Real.sqrt (q : ℝ)| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hnonneg1, abs_of_nonneg hnonneg2] at habs

theorem abs_s_e_le_nine {s t q : ℕ} (hq : 1 ≤ (q : ℝ))
    (ht : (2 : ℝ) ^ (t + 3) ≤ (q : ℝ)) (hsq : q + 1 ≤ 2 ^ s) (θ : ℝ) :
    |Sec3.s_e s t q θ| ≤ 9 * Real.sqrt (q : ℝ) := by
  have hb := Sec3.abs_s_e_le s t q hsq θ
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := two_le_of_pow_le ht
  have hB : 2 * Real.sqrt ((2 : ℝ) ^ (t + 1)) ≤ Real.sqrt (q : ℝ) := two_sqrt_pow_le_sqrt ht
  have hA : 6 * Real.sqrt ((q : ℝ) + 1) ≤ 8 * Real.sqrt (q : ℝ) :=
    six_sqrt_add_le_eight_sqrt hq2
  calc
    |Sec3.s_e s t q θ| ≤ 6 * Real.sqrt ((q : ℝ) + 1) + 2 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
      simpa using hb
    _ ≤ 8 * Real.sqrt (q : ℝ) + Real.sqrt (q : ℝ) := by nlinarith [hA, hB]
    _ = 9 * Real.sqrt (q : ℝ) := by ring

end NumBounds
end Submission
