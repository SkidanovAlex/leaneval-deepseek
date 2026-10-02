import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

open Function

/-- An integer multiple of the fractional part has the same fractional part as the integer
multiple of the number itself: `m * fract a ≡ m * a (mod 1)`.

This is the engine of `angDoubleQ_iterate`: since `-2` is an integer, applying `Int.fract (-2 * ·)`
to an already-normalised representative `fract a` produces `fract (-2 * a)`, so the iterates of
`angDoubleQ` are given by the single formula `q ↦ fract ((-2)^n * q)`. -/
theorem fract_mul_intCast_fract (a : ℚ) (m : ℤ) :
    Int.fract ((m : ℚ) * Int.fract a) = Int.fract ((m : ℚ) * a) := by
  have h : (m : ℚ) * (a - (⌊a⌋ : ℚ)) = (m : ℚ) * a - ((m * ⌊a⌋ : ℤ) : ℚ) := by
    push_cast
    ring
  rw [← Int.self_sub_floor a, h, Int.fract_sub_intCast]

/-- The specialisation of `fract_mul_intCast_fract` to the multiplier `-2` of `angDoubleQ`. -/
theorem fract_mul_neg_two_fract (a : ℚ) :
    Int.fract (-2 * Int.fract a) = Int.fract (-2 * a) :=
  fract_mul_intCast_fract a (-2)

/-- Angle doubling on rationals, iterated: `angDoubleQ^[n+1] q = fract ((-2)^(n+1) * q)`.

Note the shift by one: `Int.fract` is not the identity, so `angDoubleQ^[0] q = q` is *not*
`fract q`; the formula holds for the `(n+1)`-st iterate. -/
theorem angDoubleQ_iterate (q : ℚ) (n : ℕ) :
    (Work.Landing.angDoubleQ)^[n + 1] q = Int.fract ((-2 : ℚ) ^ (n + 1) * q) := by
  induction n with
  | zero => simp [Work.Landing.angDoubleQ]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Work.Landing.angDoubleQ, fract_mul_neg_two_fract]
    congr 1
    rw [pow_succ']
    ring

end Work.Landing.Angle
