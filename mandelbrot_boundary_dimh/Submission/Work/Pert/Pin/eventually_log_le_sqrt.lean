import Mathlib
import Submission.Work.Pert.Pin.log_le_sqrt

/-!
# `Work.Pert.Pin.eventually_log_le_sqrt`

For every real `a` the inequality `a * (1 + log M) ≤ √M` holds for all sufficiently large `M > 0`.

Split on the sign of `a`.

* `a ≤ 0`: for `M ≥ 1` we have `log M ≥ 0`, so the left hand side is `≤ 0 ≤ √M`; take `Ms = 1`.
* `a > 0`: this is `Work.Pert.Pin.log_mul_add_le_sqrt`, whose proof compares `log M` with the
  fourth root of `M` (`log M = 4 log (M^{1/4}) ≤ 4 M^{1/4}`, `Real.log_le_sub_one_of_pos`).
-/

namespace Work.Pert.Pin

theorem eventually_log_le_sqrt (a : ℝ) :
    ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M → a * (1 + Real.log M) ≤ Real.sqrt M := by
  by_cases ha : a ≤ 0
  · -- `a ≤ 0` and `M ≥ 1`: the left hand side is nonpositive
    refine ⟨1, one_pos, ?_⟩
    intro M hM
    have hlog : 0 ≤ Real.log M := Real.log_nonneg hM
    have hle : a * (1 + Real.log M) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha (by linarith)
    have hsqrt : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
    linarith
  · -- `a > 0`: the growth comparison already proved in this workspace
    have ha' : 0 < a := not_le.mp ha
    obtain ⟨M₀, hM₀pos, hM₀⟩ := log_mul_add_le_sqrt a ha'
    refine ⟨M₀, hM₀pos, fun M hM => ?_⟩
    have h := hM₀ M hM
    have hring : a * (1 + Real.log M) = a * Real.log M + a := by ring
    linarith [hring ▸ h]

end Work.Pert.Pin
