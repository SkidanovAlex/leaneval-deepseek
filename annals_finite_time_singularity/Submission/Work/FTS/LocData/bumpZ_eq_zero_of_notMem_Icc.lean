/-
# `Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc` — the radial bump vanishes off `[3/4, 7/4]`

The radial factor of the localised bump is `bumpZ z = χ(4z - 5)`, where `χ` is the smooth
cut-off `χ x = smoothTransition (2 - ‖x‖)` of `Work.Stability.Cutoff`, which vanishes off the
open ball `(-2,2)` (`Work.Stability.chi_eq_zero`).  Hence `bumpZ` vanishes wherever
`|4z - 5| ≥ 2`, i.e. on `(-∞, 3/4] ∪ [7/4, ∞)` — in particular off the closed interval
`[3/4, 7/4]`.  This is the containment of the support of `bumpZ` in `[3/4, 7/4]` that makes the
localised data compactly supported in `z`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- **The radial bump vanishes off `[3/4, 7/4]`.**  If `z ∉ [3/4, 7/4]` then `z < 3/4` or
`z > 7/4`; in the first case `4z - 5 < -2` and in the second `4z - 5 > 2`, so in either case
`|4z - 5| ≥ 2` and `χ(4z - 5) = 0` (`Work.Stability.chi_eq_zero`). -/
theorem bumpZ_eq_zero_of_notMem_Icc (z : ℝ) (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4)) :
    Work.FTS.LocData.bumpZ z = 0 := by
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have h : z < 3 / 4 ∨ 7 / 4 < z := by
    by_contra hc
    exact hz ⟨not_lt.mp (fun h => hc (Or.inl h)),
      not_lt.mp (fun h => hc (Or.inr h))⟩
  rcases h with h | h
  · have hneg : 4 * z - 5 < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · have hpos : 0 < 4 * z - 5 := by linarith
    rw [abs_of_pos hpos]
    linarith

end Work.FTS.LocData
