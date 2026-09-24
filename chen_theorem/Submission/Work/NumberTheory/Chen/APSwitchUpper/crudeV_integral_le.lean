import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude

namespace Work.NumberTheory.Chen.APSwitchUpper

/-! Conjunct 5 of the six in
`Work.NumberTheory.Chen.APSwitchUpper.crudePairHypotheses`: the second fixed-point
(supersolution) inequality for the crude exponential majorant pair
`crudeU s = if s < 1 then 8 else if s ≤ 3 then (9-s)/s else 2 exp(3-s)`,
`crudeV s = 6 exp(2-s)` of `Submission...APSwitchUpper.riPhiSharpCrude`.

Suggested route: `∫ u in m..b, crudeV u = 6 (exp (2-m) - exp (2-b)) ≤ 6 exp (2-m)`
(`intervalIntegral.integral_comp_sub_left` + `integral_exp`, or an explicit
antiderivative), then split on `s ≤ 3`: if `s ≤ 3` then `max (s-1) 2 = 2`, the integral is
`≤ 6`, and the claim is `3 - s + 6 ≤ 9 - s = s * crudeU s` (use `crudeU_of_mem`);
if `3 < s` then `max (s-1) 2 = s - 1`, the indicator term vanishes, the integral is
`≤ 6 exp (3-s)`, and `6 exp(3-s) ≤ 2 s exp (3-s) = s * crudeU s` as `s ≥ 3`
(use `crudeU_of_three_lt`). -/

open MeasureTheory

/-- An explicit antiderivative of `crudeV`: for all `a b`,
`∫_{a}^{b} crudeV = 6 (exp (2-a) - exp (2-b))`. -/
theorem crudeV_integral (a b : ℝ) :
    ∫ u in a..b, crudeV u = 6 * (Real.exp (2 - a) - Real.exp (2 - b)) := by
  rw [show (fun u => crudeV u) = fun u => 6 * Real.exp (2 - u) from by
    funext u; rw [crudeV]]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_left (fun x => Real.exp x) 2]
  rw [integral_exp]

theorem crudeV_integral_le :
    ∀ s : ℝ, 2 ≤ s → ∀ b : ℝ, max (s - 1) 2 ≤ b →
      (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
        + ∫ u in (max (s - 1) 2)..b, Work.NumberTheory.Chen.APSwitchUpper.crudeV u
      ≤ s * Work.NumberTheory.Chen.APSwitchUpper.crudeU s := by
  intro s hs b hb
  by_cases hs3 : s ≤ 3
  · -- `s ≤ 3`: the integral runs from `2` and is at most `6`.
    rw [if_pos hs3]
    have hmax : max (s - 1) 2 = 2 := max_eq_right (by linarith)
    rw [hmax, crudeV_integral]
    have hU : Work.NumberTheory.Chen.APSwitchUpper.crudeU s = (9 - s) / s :=
      Work.NumberTheory.Chen.APSwitchUpper.crudeU_of_mem (by linarith) hs3
    rw [hU]
    have hsne : s ≠ 0 := by linarith
    have hR : s * ((9 - s) / s) = 9 - s := by field_simp
    rw [hR]
    norm_num
    nlinarith [Real.exp_pos (2 - b)]
  · -- `3 < s`: the integral runs from `s - 1` and is at most `6 exp (3-s)`.
    rw [if_neg hs3]
    have hs3' : 3 < s := not_le.mp hs3
    have hmax : max (s - 1) 2 = s - 1 := max_eq_left (by linarith)
    rw [hmax, crudeV_integral]
    have hU : Work.NumberTheory.Chen.APSwitchUpper.crudeU s = 2 * Real.exp (3 - s) :=
      Work.NumberTheory.Chen.APSwitchUpper.crudeU_of_three_lt hs3'
    rw [hU]
    have h2 : 2 - (s - 1) = 3 - s := by ring
    rw [h2]
    have hexp : 0 ≤ Real.exp (3 - s) := Real.exp_nonneg _
    have h6 : 6 * Real.exp (3 - s) ≤ 2 * s * Real.exp (3 - s) := by
      have h : (6 : ℝ) ≤ 2 * s := by linarith
      nlinarith [hexp]
    nlinarith [Real.exp_pos (2 - b), h6]

end Work.NumberTheory.Chen.APSwitchUpper
