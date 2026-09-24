import Mathlib

/-!
# The error profile `h` of the sharp upper-bound linear sieve

The classical Buchstab–delay induction of the sharp linear sieve (Nathanson Ch. 9,
Bordignon arXiv:2207.09452, §"explicit version of the linear sieve") controls the accumulated
error of its layer profiles by the single explicit exponential profile

`h(s) = e^{-2}` for `s ≤ 2`,  `h(s) = e^{-s}` for `2 ≤ s ≤ 3`,  `h(s) = 3e^{-s}/s` for `s ≥ 3`,

whose two structural properties — the tail integral bound `H(s) ≤ κ s h(s)` and the shift
inequality `h(s-1) ≤ γ h(s)` — are exactly what the transport step consumes (they are
Lemmas 9.6/9.8 of Nathanson and the lemmas around `lemma:expf_n` of Bordignon).

This file only fixes the definition (and nonnegativity); the transport inequalities are
delegated as `errH_transport`.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-- The exponential error profile `h` of the sharp linear sieve: `e^{-2}` on `(-∞,2]`,
`e^{-s}` on `[2,3]`, `3e^{-s}/s` on `[3,∞)`. -/
noncomputable def errH (s : ℝ) : ℝ :=
  if s ≤ 2 then Real.exp (-2) else if s ≤ 3 then Real.exp (-s) else 3 * Real.exp (-s) / s

theorem errH_of_le_two {s : ℝ} (h : s ≤ 2) : errH s = Real.exp (-2) := if_pos h

theorem errH_of_between {s : ℝ} (h2 : 2 < s) (h3 : s ≤ 3) :
    errH s = Real.exp (-s) := by
  rw [errH, if_neg (not_le.mpr h2), if_pos h3]

theorem errH_of_three_lt {s : ℝ} (h : 3 < s) : errH s = 3 * Real.exp (-s) / s := by
  rw [errH, if_neg (not_le.mpr (by linarith : 2 < s)), if_neg (not_le.mpr h)]

theorem errH_pos (s : ℝ) (hs : 1 ≤ s) : 0 < errH s := by
  by_cases h : s ≤ 2
  · rw [errH_of_le_two h]; exact Real.exp_pos _
  · rw [not_le] at h
    by_cases h3 : s ≤ 3
    · rw [errH_of_between h h3]; exact Real.exp_pos _
    · rw [not_le] at h3
      rw [errH_of_three_lt h3]
      have hspos : 0 < s := by linarith
      positivity

theorem errH_nonneg (s : ℝ) : 0 ≤ errH s := by
  by_cases h : 1 ≤ s
  · exact (errH_pos s h).le
  · rw [errH, if_pos (by linarith)]; exact (Real.exp_pos _).le

end

end Work.NumberTheory.Chen.APSwitchUpper
