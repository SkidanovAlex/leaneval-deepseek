import Mathlib

namespace Work.RPB.B4

theorem periodic_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (c : ℝ) (hf : Function.Periodic f c) : Function.Periodic (deriv f) c := by
  intro x
  -- Translation in the domain does not change the derivative, so the derivative of the
  -- translated function `y ↦ f (y + c)` at `x` is `deriv f (x + c)`.
  rw [← deriv_comp_add_const f c x]
  -- But `y ↦ f (y + c)` is `f` itself by periodicity, hence so are their derivatives.
  rw [show (fun y => f (y + c)) = f from funext fun y => hf y]

end Work.RPB.B4
