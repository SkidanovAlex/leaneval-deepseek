/-
# `APSwitchUpper.oddSum_formula` — the closed form of `u·oddSum (n+1) u` on `[2,4]`

The summed delay identity `oddSum_mul_integral` evaluates
`u · oddSum (n+1) u = ∫_{u-1}^{2(n+1)+3} evenSum (n+1)` as soon as `u ≥ 2`.  For `u ≤ 4` the
lower limit `u-1` lies in `[1,3]`, where `evenSum (n+1)` is the elementary function
`((3−s) + Cv n)/s` (`riPhi_le_env.evenSum_formula`).  Splitting off the piece `[3, 2(n+1)+3]`
(which is `Tv (n+1)` by definition) and integrating in closed form gives

  `u · oddSum (n+1) u = (3 + Cv n)·log(3/(u−1)) − 4 + u + Tv (n+1)`  for `2 ≤ u ≤ 4`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Finset
open scoped BigOperators

theorem oddSum_formula (n : ℕ) {u : ℝ} (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    u * oddSum (n + 1) u = (3 + Cv n) * Real.log (3 / (u - 1)) - 4 + u + Tv (n + 1) := by
  have hu1 : (1 : ℝ) ≤ u - 1 := by linarith
  have hu3 : u - 1 ≤ 3 := by linarith
  have hmain : (∫ x in (u - 1)..3, evenSum (n + 1) x)
      = (3 + Cv n) * Real.log (3 / (u - 1)) - 4 + u := by
    have hcongr : (∫ x in (u - 1)..3, evenSum (n + 1) x)
        = ∫ x in (u - 1)..3, ((3 + Cv n) * x⁻¹ - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hu3] at hx
      have hx1 : 1 ≤ x := by linarith [hx.1, hu1]
      have hx0 : x ≠ 0 := by linarith
      rw [evenSum_formula n hx1 hx.2]
      field_simp
      ring
    rw [hcongr]
    have hnot : (0 : ℝ) ∉ Set.uIcc (u - 1) 3 := by
      rw [Set.uIcc_of_le hu3, Set.mem_Icc]
      rintro ⟨h1, h2⟩
      linarith [hu1]
    have hint1 : IntervalIntegrable (fun x : ℝ => (3 + Cv n) * x⁻¹) volume (u - 1) 3 := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.const_mul ?_ _
      refine ContinuousOn.inv₀ continuousOn_id ?_
      intro x hx
      rw [Set.uIcc_of_le hu3, Set.mem_Icc] at hx
      exact ne_of_gt (by linarith [hx.1, hu1] : (0 : ℝ) < x)
    rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const]
    rw [intervalIntegral.integral_const_mul, integral_inv hnot, intervalIntegral.integral_const]
    simp
    ring
  have hsplit : (∫ x in (u - 1)..(((2 * (n + 1) + 3 : ℕ) : ℝ)), evenSum (n + 1) x)
      = (∫ x in (u - 1)..3, evenSum (n + 1) x) + Tv (n + 1) := by
    rw [Tv, ← intervalIntegral.integral_add_adjacent_intervals
      (evenSum_intervalIntegrable (n + 1) (u - 1) 3)
      (evenSum_intervalIntegrable (n + 1) 3 (((2 * (n + 1) + 3 : ℕ) : ℝ)))]
  rw [oddSum_mul_integral (n + 1) h2, hsplit, hmain]

end Work.NumberTheory.Chen.APSwitchUpper
