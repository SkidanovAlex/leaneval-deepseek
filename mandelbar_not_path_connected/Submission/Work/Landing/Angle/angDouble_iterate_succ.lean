import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Angle

/-- An integer multiple of the fractional part has the same fractional part as the integer
multiple of the number itself: `m * fract a ≡ m * a (mod 1)` over `ℝ`.

This is the engine of `angDouble_iterate_succ`: since `-2` is an integer, applying
`Int.fract (-2 * ·)` to an already-normalised representative `fract a` produces `fract (-2 * a)`,
so the iterates of `angDouble` are given by the single formula `θ ↦ fract ((-2)^n * θ)`. -/
theorem fract_mul_intCast_fract_real (a : ℝ) (m : ℤ) :
    Int.fract ((m : ℝ) * Int.fract a) = Int.fract ((m : ℝ) * a) := by
  have h : (m : ℝ) * (a - (⌊a⌋ : ℝ)) = (m : ℝ) * a - ((m * ⌊a⌋ : ℤ) : ℝ) := by
    push_cast
    ring
  rw [← Int.self_sub_floor a, h, Int.fract_sub_intCast]

/-- The specialisation of `fract_mul_intCast_fract_real` to the multiplier `-2` of `angDouble`. -/
theorem fract_neg_two_fract (a : ℝ) :
    Int.fract (-2 * Int.fract a) = Int.fract (-2 * a) := by
  have h := fract_mul_intCast_fract_real a (-2)
  simpa using h

/-- Angle doubling on `ℝ`, iterated: `angDouble^[n+1] θ = fract ((-2)^(n+1) * θ)`.

Note the shift by one: `Int.fract` is not the identity, so `angDouble^[0] θ = θ` is *not*
`fract θ`; the formula holds from the `(n+1)`-st iterate onwards, and in particular
`angDouble` itself is the `n = 0` case. -/
theorem angDouble_iterate_succ (θ : ℝ) (n : ℕ) :
    (Work.Landing.angDouble)^[n + 1] θ = Int.fract ((-2 : ℝ) ^ (n + 1) * θ) := by
  induction n with
  | zero => simp [Work.Landing.angDouble]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Work.Landing.angDouble,
      fract_neg_two_fract ((-2 : ℝ) ^ (n + 1) * θ)]
    congr 1
    rw [pow_succ']
    ring

end Work.Landing.Angle
