/-
# The ceiling `β` is insensitive to the integral part of the meridian parameter

`cuspX v u y = u σ_v + y₂ λ₂ + y₃ λ₃` is the cusp coordinate with meridian parameter `u`.  The
meridian direction `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` is an **integer** vector and the
ceiling `β` is periodic under integer translations (`beta_add_int`, stored as
`beta_add_smul_slope : β (x + m • σ_v) = β x` for `m : ℤ`).  Hence replacing the meridian parameter
`u` by its fractional part does not change the ceiling:

  `beta_cuspX_fract : β (cuspX v (Int.fract u) y) = β (cuspX v u y)`.

This is the point where the *unslabbed* collar chart differs from the slabbed one: the slab
`0 < outerU v x < 1` made `Int.fract (outerU v x) = outerU v x` trivially (so the round trip of the
cusp chart could be proved without any periodicity), whereas the unslabbed box has
`outerU v x ∈ (outerU v c − 1/2, outerU v c + 1/2)`, an interval which need not lie in `[0,1)`.
The ceiling is nevertheless the same, which is all the round trip of the collar coordinate needs.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_add_smul_slope

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The ceiling at a cusp coordinate depends only on the fractional part of the meridian
parameter.**  Indeed `cuspX v u y = cuspX v (Int.fract u) y + ⌊u⌋ • σ_v` and `β` is invariant under
integer multiples of the integer vector `σ_v`. -/
theorem beta_cuspX_fract (v : Fin 5) (u : ℝ) (y : E2) :
    beta (cuspX v (Int.fract u) y) = beta (cuspX v u y) := by
  have hu : u = Int.fract u + (⌊u⌋ : ℝ) := by
    have := Int.self_sub_floor u
    linarith
  have hX : cuspX v u y = cuspX v (Int.fract u) y + (⌊u⌋ : ℝ) • slope v := by
    conv_lhs => rw [show u = Int.fract u + (⌊u⌋ : ℝ) from hu]
    simp only [cuspX]
    rw [add_smul]
    abel
  rw [hX, beta_add_smul_slope]

end Work.Cusp
