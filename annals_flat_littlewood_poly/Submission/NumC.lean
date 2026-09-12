import Mathlib
import Submission.S6Core

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex
set_option autoImplicit false

namespace Submission
namespace NumBounds

/-! For `t` with `2^(t+3) ≤ q`, the cosine polynomial `c` is `O(√q)`:

   `|c t θ| ≤ 2·√(2^(t+1))` (lemma `Sec3.abs_c_le`) and
   `2·√(2^(t+1)) = √(2^(t+3)) ≤ √q`.

Prove `2 * sqrt (2^(t+1)) ≤ sqrt q` from `(2:ℝ)^(t+3) ≤ q` by squaring
(`Real.le_sqrt`) or via `Real.sqrt_le_sqrt` after rewriting
`2 * sqrt(2^(t+1)) = sqrt(2^(t+3))` using `Real.sqrt_mul`/`sq_sqrt`. -/

theorem abs_c_le_sqrt {t q : ℕ} (h : (2 : ℝ) ^ (t + 3) ≤ (q : ℝ)) (θ : ℝ) :
    |Sec3.c t θ| ≤ Real.sqrt (q : ℝ) := by
  have hmain : 2 * Real.sqrt (2 ^ (t + 1)) ≤ Real.sqrt (q : ℝ) := by
    have hx : 0 ≤ 2 * Real.sqrt (2 ^ (t + 1)) := by positivity
    have hy : 0 ≤ (q : ℝ) := by positivity
    rw [Real.le_sqrt hx hy]
    calc
      (2 * Real.sqrt (2 ^ (t + 1))) ^ 2 = (2 : ℝ) ^ 2 * (Real.sqrt (2 ^ (t + 1))) ^ 2 := by
        rw [mul_pow]
      _ = (2 : ℝ) ^ 2 * (2 : ℝ) ^ (t + 1) := by
        rw [Real.sq_sqrt]
        positivity
      _ = (2 : ℝ) ^ (t + 3) := by
        rw [pow_add, show (t + 1) + 2 = t + 3 by omega]
        ring
      _ ≤ (q : ℝ) := h
  calc
    |Sec3.c t θ| ≤ Real.sqrt (2 ^ (t + 1)) + Real.sqrt (2 ^ (t + 1)) := Sec3.abs_c_le t θ
    _ = 2 * Real.sqrt (2 ^ (t + 1)) := by ring
    _ ≤ Real.sqrt (q : ℝ) := hmain

end NumBounds
end Submission
