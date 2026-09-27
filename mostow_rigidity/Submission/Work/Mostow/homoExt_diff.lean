import Mathlib
import Submission.Work.Mostow.homoExtDeriv

/-!
# Differentiability of `homoExt` away from the origin

`homoExt g x = ‖x‖ • bd g (‖x‖⁻¹ • x)` is differentiable at every `x ≠ 0`; this is the
"denominator is non-zero" instance of the differentiability of the explicit boundary quotient
`phiFun g` (see `Submission.Work.Mostow.homoExtDeriv`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem homoExt_diff (n : ℕ) (hn : 1 ≤ n) (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    ∀ x : Submission.Mostow.E n, x ≠ 0 → DifferentiableAt ℝ (Work.Mostow.homoExt g) x := by
  intro x hx
  exact differentiableAt_homoExt n g x hx

end Work.Mostow
