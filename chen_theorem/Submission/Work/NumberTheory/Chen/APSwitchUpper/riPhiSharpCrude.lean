/-
# `APSwitchUpper.riPhiSharpCrude` — the crude exponential majorants of `riPhi`, `riPsi`

`riPhi`/`riPsi` are `tsum`s of the delay family `profC` (see `APSwitchUpper/prof.lean`).
Before anything can be said about their *integrals* one needs

* **summability** of the defining series (so that the `tsum` is the limit of its partial sums),
* an explicit, **locally integrable** dominating function.

Both are supplied by a single explicit *supersolution pair* of the delay system, the
affine-plus-exponential pair

* `crudeU s = 8` for `s < 1`, `(9 − s)/s` for `1 ≤ s ≤ 3`, `2·exp (3 − s)` for `3 ≤ s`,
* `crudeV s = 6·exp (2 − s)`.

This pair satisfies the hypotheses of `riPhi_le_of_supersolution`
(`APSwitchUpper/riPhi_supersolution.lean`).  Indeed the companion inequalities

* `s·crudeU s ≥ (3−s)⁺ + ∫_{max(s−1,2)}^b crudeV`,  `s·crudeV s ≥ ∫_{s−1}^b crudeU`

reduce (letting `b → ∞`, the integrands being nonnegative) to `∫_2^∞ crudeV = 6 = 3·crudeU 3`
and to the elementary inequality `6·s·exp (2−s) ≥ 9·log (3/(s−1)) + s − 2` (for `2 ≤ s ≤ 4`).

The pair is deliberately very crude — the true profiles satisfy `riPhi 3 = 0.1874` while
`crudeU 3 = 2` — so it is useless for the numerics; it only makes the `tsum`s well behaved.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_supersolution

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory Finset
open scoped BigOperators

/-- A crude affine/exponential majorant of `riPhi`. -/
def crudeU (s : ℝ) : ℝ :=
  if s < 1 then 8 else if s ≤ 3 then (9 - s) / s else 2 * Real.exp (3 - s)

/-- A crude exponential majorant of `riPsi`. -/
def crudeV (s : ℝ) : ℝ := 6 * Real.exp (2 - s)

theorem crudeV_nonneg (s : ℝ) : 0 ≤ crudeV s := by
  unfold crudeV; positivity

theorem crudeU_nonneg (s : ℝ) : 0 ≤ crudeU s := by
  unfold crudeU
  by_cases h1 : s < 1
  · rw [if_pos h1]; norm_num
  · rw [if_neg h1]
    by_cases h3 : s ≤ 3
    · rw [if_pos h3]
      exact div_nonneg (by linarith [not_lt.mp h1]) (by linarith [not_lt.mp h1])
    · rw [if_neg h3]; positivity

theorem crudeU_of_mem {s : ℝ} (h1 : 1 ≤ s) (h3 : s ≤ 3) : crudeU s = (9 - s) / s := by
  rw [crudeU, if_neg (not_lt.mpr h1), if_pos h3]

theorem crudeU_of_three_lt {s : ℝ} (h : 3 < s) : crudeU s = 2 * Real.exp (3 - s) := by
  rw [crudeU, if_neg (not_lt.mpr (by linarith)), if_neg (not_le.mpr h)]

theorem crudeU_of_three_le' {s : ℝ} (h : 3 ≤ s) : crudeU s = 2 * Real.exp (3 - s) := by
  rcases eq_or_lt_of_le h with h3 | h3
  · subst h3
    rw [crudeU_of_mem (s := 3) (by norm_num) le_rfl]
    norm_num
  · exact crudeU_of_three_lt h3

theorem crudeU_three : crudeU 3 = 2 := by
  rw [crudeU_of_mem (s := 3) (by norm_num) le_rfl]; norm_num

end

end Work.NumberTheory.Chen.APSwitchUpper
