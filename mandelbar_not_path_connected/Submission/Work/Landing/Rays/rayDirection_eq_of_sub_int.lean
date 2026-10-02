import Mathlib
import Submission.Work.Landing.Rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Rays

/-- The direction `e^{2πiθ}` of the external ray depends on `θ` only through its class modulo `1`:
if `θ' = θ + n` for some integer `n` then `rayDirection θ' = rayDirection θ`. -/
theorem rayDirection_eq_of_sub_int {θ θ' : ℝ} (h : ∃ n : ℤ, θ' = θ + n) :
    Work.Landing.rayDirection θ' = Work.Landing.rayDirection θ := by
  obtain ⟨n, rfl⟩ := h
  have harg : ((2 * Real.pi * (θ + (n : ℝ)) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [Work.Landing.rayDirection, harg, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

end Work.Landing.Rays
