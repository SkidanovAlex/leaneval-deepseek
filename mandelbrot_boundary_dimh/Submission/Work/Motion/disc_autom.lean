import Mathlib

/-!
# The automorphism of the unit disc `z ↦ (z - a) / (1 - conj a * z)`

This file only defines `Work.Motion.mob`, the Möbius transformation of the unit disc
sending `a` to `0`.  Its basic properties (it maps the unit disc to itself, it is
holomorphic there, and its derivative at `a` and at `0`) are proved in the sibling
files `Submission/Work/Motion/mob_disc.lean` and `Submission/Work/Motion/mob_deriv.lean`.
-/

namespace Work.Motion

open Metric Set
open scoped ComplexConjugate

/-- The Möbius transformation of the unit disc sending `a` to `0`,
`mob a t = (t - a) / (1 - conj a * t)`. -/
noncomputable def mob (a : ℂ) : ℂ → ℂ := fun t => (t - a) / (1 - conj a * t)

@[simp]
theorem mob_apply (a t : ℂ) : mob a t = (t - a) / (1 - conj a * t) := rfl

end Work.Motion
