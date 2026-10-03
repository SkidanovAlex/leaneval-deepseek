import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# The two-sided shear of a free group

`Work.ORLyndon.shear t x m m'` is the Nielsen transformation of the free group `F α` which fixes
every generator except `x` and sends

`x ↦ t ^ (-m) * x * t ^ (-m')`.

It is the composite of the left transvection `Work.ORLyndon.transvectionLeft t x m`
(`x ↦ t ^ (-m) * x`) with the *right* shear `x ↦ x * t ^ (-m')`, hence an automorphism of `F α`.
Applied to a root `u` it replaces every occurrence of `x` (with sign `s`) by
`t ^ (-m * s) * x ^ s * t ^ (-m' * s)`, so that

* the exponent sum of `t` changes by `-(m + m') * eps x u` (while that of every other letter is
  unchanged): choosing `m + m' = eps t u / eps x u` makes the image have **vanishing `t`-exponent
  sum**, which is the input of the exponent-sum-zero Magnus step `annAt_of_epsZero_strong`;
* the letter `x` occurs exactly as often as before, and all non-`t` letters are preserved;
* the transformation is *clean off `t`* (`∂ (ψ (of q)) / ∂ x = 0` for `x ≠ t`, `q ≠ x`), so the
  componentwise Nielsen transfer `Work.ORLyndon.annAt_of_jacobian_zero` applies at every letter
  `≠ t`.

The two free parameters `m`, `m'` with the *fixed* sum `m + m' = eps t u / eps x u` are what makes
this strictly more useful than a single transvection: the cyclicity of the image `ψ u` (needed for
the Magnus step) can be arranged by varying `m` while keeping the vanishing of `eps t`.

See `NOTES_epsNeZeroDescent_level.md` §22 for the census verifying that this shear family covers
every *residual* instance in which the letter `x` occurs only with one sign.

## Main definitions

* `Work.ORLyndon.shear`
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

/-- **The two-sided shear** `x ↦ t ^ (-m) * x * t ^ (-m')` of the free group on `α`, all other
generators fixed. -/
noncomputable def shear {α : Type*} [DecidableEq α] (t x : α) (m m' : ℤ) :
    FreeGroup α →* FreeGroup α :=
  FreeGroup.lift fun z =>
    if z = x then (FreeGroup.of t) ^ (-m) * FreeGroup.of x * (FreeGroup.of t) ^ (-m')
    else FreeGroup.of z

@[simp] theorem shear_of {α : Type*} [DecidableEq α] (t x : α) (m m' : ℤ) :
    shear t x m m' (FreeGroup.of x) =
      (FreeGroup.of t) ^ (-m) * FreeGroup.of x * (FreeGroup.of t) ^ (-m') := by
  rw [shear, FreeGroup.lift_apply_of]
  simp

theorem shear_of_ne {α : Type*} [DecidableEq α] {t x z : α} (h : z ≠ x) (m m' : ℤ) :
    shear t x m m' (FreeGroup.of z) = FreeGroup.of z := by
  rw [shear, FreeGroup.lift_apply_of]
  simp [h]

end Work.ORLyndon
