/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The right multiplication substitutions `y ↦ y * t ^ (-q y)`

For a fixed generator `t : α` and a function `q : α → ℤ`, the map

`rightPowFun t q : α → F(α)`,  `y ↦ of y * of t ^ (-(q y))`

extends to a homomorphism `rightPow t q : F(α) →* F(α)` (`FreeGroup.lift`).  When `q t = 0` (or
`q t = 2`) this homomorphism is an **automorphism**: its inverse is the map attached to `-q`
(completed by `of t ↦ of t`, respectively `of t ↦ of t⁻¹`).  This is the substitution that makes a
chosen exponent sum vanish: `σ_t (rightPow t q u) = σ_t u · ∏_y (σ_y u) ^ (-(q y))`, so that
`σ_t (rightPow t q u) = 0` whenever `Σ_y q y · σ_y u = σ_t u`.

It is the "cost-free" substitution for the all-exponent-sums-nonzero case of the Magnus step with
the root tracked: every letter of `u` is replaced by a word containing exactly one letter different
from `t` (namely that letter itself), so the number of non-`t` letters does not increase
(`nonTLetters_rightPow_le`), while `σ_t` can be adjusted at will.

This file contains definitions and proven lemmas only (no `sorry`).
-/
import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The generator map `y ↦ of y * of t ^ (-(q y))` whose lift is `rightPow t q`. -/
noncomputable def rightPowFun (t : α) (q : α → ℤ) : α → FreeGroup α := by
  classical
  exact fun y => FreeGroup.of y * FreeGroup.of t ^ (-(q y))

/-- The substitution `y ↦ y * t ^ (-(q y))` of the free group `F(α)`. -/
noncomputable def rightPow (t : α) (q : α → ℤ) : FreeGroup α →* FreeGroup α :=
  FreeGroup.lift (rightPowFun t q)

@[simp] theorem rightPow_of (t : α) (q : α → ℤ) (y : α) :
    rightPow t q (FreeGroup.of y) = FreeGroup.of y * FreeGroup.of t ^ (-(q y)) := by
  classical
  rw [rightPow, FreeGroup.lift_apply_of]
  rfl

@[simp] theorem rightPowFun_apply (t : α) (q : α → ℤ) (y : α) :
    rightPowFun t q y = FreeGroup.of y * FreeGroup.of t ^ (-(q y)) := rfl

/-- The substitution attached to `0` is the identity. -/
theorem rightPow_zero (t : α) : rightPow t (fun _ => 0) = MonoidHom.id (FreeGroup α) := by
  classical
  refine FreeGroup.ext_hom _ _ fun y => ?_
  simp

end Work.OROneRel
