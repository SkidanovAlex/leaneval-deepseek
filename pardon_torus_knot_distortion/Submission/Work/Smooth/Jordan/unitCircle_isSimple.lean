import Mathlib
import Submission.Work.Smooth.Jordan.Circle

/-!
# The standard circle is a simple closed curve

The curve `t ↦ e^{it}` is injective on one period `[0, 2π)`: it is the model simple closed curve of
the chapter.  The work is Mathlib's `Circle.exp_injOn_Ico`, which says that `ℝ → S¹`,
`t ↦ e^{it}`, is injective on any half-open interval of length `≤ 2π`.
-/

open Set

namespace Work.Smooth.Jordan

/-- The standard unit circle `t ↦ e^{it}` is a *simple* closed curve: it is injective on the period
`[0, 2π)`. -/
theorem unitCircle_isSimple : unitCircle.toPlaneCurve.IsSimple := by
  intro t₁ ht₁ t₂ ht₂ h
  -- Two parameters with the same image give the same point of `S¹ = Circle`; Mathlib's
  -- `Circle.exp_injOn_Ico` then forces them to be equal.
  have h' : Circle.exp t₁ = Circle.exp t₂ := by
    apply Subtype.ext
    simp only [Circle.coe_exp]
    exact h
  exact Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith [two_pi_pos]) ht₁ ht₂ h'

end Work.Smooth.Jordan
