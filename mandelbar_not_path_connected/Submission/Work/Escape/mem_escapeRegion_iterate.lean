import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The escaping region is forward invariant

For a continuous map `f : ℂ → ℂ` whose norm behaviour is monic of degree `d ≥ 2` up to an additive
constant `A` (i.e. `MonicGrowth f d A`), the escaping region `{z | max 2 A < ‖z‖}` is forward
invariant: once the orbit of `z` has norm exceeding the escape radius `max 2 A`, it stays there.

The key point is the elementary *escape step*: if `max 2 A < ‖w‖` then `‖w‖ ≤ ‖f w‖`. Indeed,
since `‖w‖ ≥ 1` and `d ≥ 2`,
`‖f w‖ ≥ ‖w‖^d - A ≥ ‖w‖^2 - A ≥ ‖w‖^2 - ‖w‖ = ‖w‖(‖w‖ - 1) ≥ ‖w‖`,
the last inequality because `‖w‖ ≥ 2`. Hence `max 2 A < ‖w‖ ≤ ‖f w‖`.
-/

open Function

namespace Work.Escape

/-- **Escape step.** If `max 2 A < ‖w‖` then `max 2 A < ‖f w‖`: the escape radius `max 2 A` is
never crossed back. -/
theorem max_two_A_lt_norm_f (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {w : ℂ} (hw : max 2 A < ‖w‖) : max 2 A < ‖f w‖ := by
  have h2 : 2 ≤ ‖w‖ := le_of_lt ((le_max_left 2 A).trans_lt hw)
  have hA : A ≤ ‖w‖ := le_of_lt ((le_max_right 2 A).trans_lt hw)
  have h1 : (1 : ℝ) ≤ ‖w‖ := by linarith
  have hpow : ‖w‖ ^ 2 ≤ ‖w‖ ^ d := pow_le_pow_right₀ h1 hd
  have hle := h.le_norm w
  nlinarith [hle, hpow, hw, hA]

/-- The escaping region is forward invariant: `z ∈ escapeRegion A` implies
`(f^[n]) z ∈ escapeRegion A` for every `n`. -/
theorem mem_escapeRegion_iterate (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {z : ℂ} (hz : z ∈ escapeRegion A) (n : ℕ) :
    (f^[n]) z ∈ escapeRegion A := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact max_two_A_lt_norm_f f d A h hd ih

end Work.Escape
