import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# The left transvection of a free group

`Work.ORLyndon.transvectionLeft t y m` is the elementary Nielsen transformation of the free group
`F α` which fixes every generator except `y` and sends

`y ↦ t ^ (-m) * y`.

It is the only Nielsen transformation used by the transvection route to the residual of
`Work.ORLyndon.EpsNeZeroDescent` (see `NOTES_epsNeZeroDescent_level.md` §21): applied to a root `u`
it turns every occurrence of `y` into an occurrence of `y` preceded by `m` copies of `t ^ (-1)`,
hence changes the exponent sum of `t` by `-m · eps y u`, so that the *image* of `u` has vanishing
`t`-exponent sum whenever `m · eps y u = eps t u`.  Since `transvectionLeft` leaves `y` itself in
place, it is *clean at every letter*: `∂ (ψ (of q)) / ∂ x = 0` for `q ≠ x`, which is what the
componentwise Nielsen transfer `Work.ORLyndon.annAt_of_jacobian_zero` consumes.

## Main definitions

* `Work.ORLyndon.transvectionLeft`

## Main results

* `Work.ORLyndon.transvectionLeft_of`, `Work.ORLyndon.transvectionLeft_of_ne` -- values on the
  generators.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

/-- **The left transvection** `y ↦ t ^ (-m) * y` of the free group on `α`, all other generators
fixed. -/
noncomputable def transvectionLeft {α : Type*} [DecidableEq α] (t y : α) (m : ℤ) :
    FreeGroup α →* FreeGroup α :=
  FreeGroup.lift fun z => if z = y then (FreeGroup.of t) ^ (-m) * FreeGroup.of y else FreeGroup.of z

@[simp] theorem transvectionLeft_of {α : Type*} [DecidableEq α] (t y : α) (m : ℤ) :
    transvectionLeft t y m (FreeGroup.of y) = (FreeGroup.of t) ^ (-m) * FreeGroup.of y := by
  rw [transvectionLeft, FreeGroup.lift_apply_of]
  simp

theorem transvectionLeft_of_ne {α : Type*} [DecidableEq α] {t y z : α} (h : z ≠ y) (m : ℤ) :
    transvectionLeft t y m (FreeGroup.of z) = FreeGroup.of z := by
  rw [transvectionLeft, FreeGroup.lift_apply_of]
  simp [h]

end Work.ORLyndon
