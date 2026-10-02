import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Set.Card

/-!
# A port of the commons threshold `2n + 2 ≤ n ^ log n`

Ported from `Submission/Commons/Analysis/Asymptotics/exists_two_mul_add_two_le_rpow_log.lean`
(proved by the fleet) with minimal imports, so that it can be used inside the
proof cone.
-/

namespace Commons.Analysis.Asymptotics

theorem exists_two_mul_add_two_le_rpow_log :
    ∃ N : ℕ, ∀ n ≥ N, (2 * (n : ℝ) + 2) ≤ (n : ℝ) ^ Real.log (n : ℝ) := by
  refine ⟨8, ?_⟩
  intro n hn
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [this, Real.log_pow]
    norm_num
  have hlog8 : (2 : ℝ) ≤ Real.log (8 : ℝ) := by
    rw [h8]
    nlinarith [Real.log_two_gt_d9]
  have hlog : (2 : ℝ) ≤ Real.log (n : ℝ) :=
    hlog8.trans (Real.log_le_log (by norm_num) hn8)
  have hstep : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (Real.log (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hlog
  have hsq : 2 * (n : ℝ) + 2 ≤ (n : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [hn8]
  exact hsq.trans hstep

end Commons.Analysis.Asymptotics
