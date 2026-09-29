import Mathlib
import Submission.Work.CPsi.psiC_deps

/-!
# Continuity of the contour map `ψ_C` on the closed unit disc

`ψ_C z = -(3/4) · lune (23/10) z = -(3/4) · gobL z`, where
`gobL z = (B·z - B + √(R z)) / (2C)` and `R = gobR` is a polynomial
(`psiC_base`, `lune_eq`).

`R` is continuous, so the only delicate point is the continuity of the principal
square root `w ↦ w ^ (1/2)` along the values `R z`. On the closed unit disc, `R`
avoids the branch cut `(-∞,0)` except at its zeros, which lie on the unit circle
where `R z = 0` (`gobR_slitPlane_of_le_of_ne`). At such a zero Mathlib's
`Complex.continuousAt_cpow_const_of_re_pos` still applies, because its hypothesis
`0 ≤ re w ∨ im w ≠ 0` holds at `w = 0`; this gives continuity of the square root at
`0` as well. Together these yield `ContinuousOn ψ_C (closedBall 0 1)`.
-/

namespace Work.CPsi

open Submission.CDTPlan
open Complex Metric

theorem psiC_continuous : ContinuousOn Submission.CDTPlan.psiC (Metric.closedBall 0 1) := by
  -- `gobR` is a polynomial, hence continuous everywhere.
  have hcont_gobR : Continuous gobR := by unfold gobR; fun_prop
  -- The principal square root of `gobR` is continuous on the closed unit disc.
  have hsqrt : ContinuousOn (fun z : ℂ => (gobR z) ^ (1/2 : ℂ)) (Metric.closedBall 0 1) := by
    intro z hz
    have hzmem : ‖z‖ ≤ 1 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    -- Continuity criterion for `w ↦ w ^ (1/2)` at `w = gobR z`.
    have hcond : 0 ≤ (gobR z).re ∨ (gobR z).im ≠ 0 := by
      rcases eq_or_ne (gobR z) 0 with h | h
      · left; rw [h]; simp
      · obtain h1 | h2 := gobR_slitPlane_of_le_of_ne hzmem h
        · exact Or.inl (le_of_lt h1)
        · exact Or.inr h2
    have hw : 0 < (1/2 : ℂ).re := by norm_num
    exact (Complex.continuousAt_cpow_const_of_re_pos hcond hw).comp_continuousWithinAt
      (hcont_gobR.continuousAt.continuousWithinAt)
  -- Numerator `B·z - B + √(R z)`.
  have hnum : ContinuousOn (fun z : ℂ => gB * z - gB + (gobR z) ^ (1/2 : ℂ))
      (Metric.closedBall 0 1) :=
    ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).add hsqrt
  -- `gobL` is the numerator divided by the nonzero constant `2C`.
  have hmain : ContinuousOn
      (fun z : ℂ => -(3/4) * ((gB * z - gB + (gobR z) ^ (1/2 : ℂ)) / (2 * gC)))
      (Metric.closedBall 0 1) :=
    continuousOn_const.mul
      (ContinuousOn.div hnum continuousOn_const (fun _ _ => mul_ne_zero two_ne_zero gC_ne_zero))
  -- Rewrite `ψ_C` as `-(3/4) · gobL` and unfold `gobL`.
  have hfun : Submission.CDTPlan.psiC = fun z : ℂ => -(3/4) * gobL z := by
    funext z
    simp only [Submission.CDTPlan.psiC, lune_eq]
  rw [hfun]
  simp only [gobL]
  exact hmain

end Work.CPsi
