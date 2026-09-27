import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

namespace Work.EKLContract.Lemmas

/-- The projection `mkX : SL₃(ℝ) → X₃` is equivariant for the left action of `SL₃(ℝ)` on itself
and on the coset space `X₃ = SL₃(ℝ)/SL₃(ℤ)`: `mkX (g * h) = g • mkX h`.

This is definitional: the `MulAction` of `SL₃(ℝ)` on `SL₃(ℝ) ⧸ Γ₃` is the quotient of the
left-regular action, so `g • (hΓ) = (g * h)Γ`. -/
theorem mkX_mul (g h : Work.EKLContract.SL3) : Work.EKLContract.mkX (g * h) = g • Work.EKLContract.mkX h :=
  rfl

end Work.EKLContract.Lemmas
