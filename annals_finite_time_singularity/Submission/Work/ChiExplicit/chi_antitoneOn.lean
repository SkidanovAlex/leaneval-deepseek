import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.ChiExplicit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.ChiExplicit.chi` is antitone on `[0, ∞)`

The explicit cut-off is `chi x = Real.smoothTransition (2 - |x|)`.  On the positive half-line
`|x| = x`, so `chi x = smoothTransition (2 - x)`: a *monotone* function (`smoothTransition.monotone`)
composed with the *antitone* map `x ↦ 2 - x`.  Hence `chi` is antitone on `[0, ∞)`.

This is the weak form of "the cut-off decreases in the radius": it combines with the flat parts
(`chi = 1` for `|x| ≤ 1`, `chi = 0` for `|x| ≥ 2`) to give the whole monotonicity of `chi` in `|x|`
on the annulus `1 ≤ |x| ≤ 2` where the cut-off is actually used.

The proof only needs the definitional reduction `chi_apply_abs` and `Real.smoothTransition.monotone`.
-/

open Set

namespace Work.ChiExplicit

/-- **The explicit cut-off is antitone on the non-negative half-line.**
For `0 ≤ x ≤ y`, `chi y ≤ chi x`: both are `smoothTransition` applied to `2 - x ≥ 2 - y`, and
`smoothTransition` is monotone. -/
theorem chi_antitoneOn : AntitoneOn Work.ChiExplicit.chi (Set.Ici (0:ℝ)) := by
  intro x hx y hy hxy
  rw [chi_apply_abs, chi_apply_abs, abs_of_nonneg hy, abs_of_nonneg hx]
  exact Real.smoothTransition.monotone (by linarith)

end Work.ChiExplicit
