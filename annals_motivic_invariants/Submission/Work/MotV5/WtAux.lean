import Mathlib
import Submission.Work.MotV5.WtDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

/-!
# Small auxiliary facts for the `tp_as` assembly

These are the coefficient/degree bookkeeping lemmas the final assembly of
`Work.MotV5.tp_as` needs on top of `WtDefs.lean`.
-/

namespace Work.MotV5

open Polynomial

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation is nonzero on nonzero elements. -/
theorem val_ne_zero (v : Valuation F Γ₀) {x : F} (hx : x ≠ 0) : v x ≠ 0 := by
  intro h
  have h1 : v x * v x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- `wt v g c l = 0` iff `c = 0` (here `v g ≠ 0`). -/
theorem wt_eq_zero_iff (v : Valuation F Γ₀) {g : F} (hg0 : v g ≠ 0) (c : F) (l : ℕ) :
    wt v g c l = 0 ↔ c = 0 := by
  rw [wt, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (pow_ne_zero l hg0)
    · by_contra hc
      exact val_ne_zero v hc ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp h)
  · intro h; subst h; simp

end Work.MotV5
