/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The transvection `x ↦ x * t ^ (m x)` of a free group

For a fixed generator `t : α` and a weight function `m : α → ℤ` this file defines the
**transvection**

  `mmTrans t m : F α →* F α`,   `FreeGroup.of x ↦ FreeGroup.of x * FreeGroup.of t ^ (m x)`.

It is a free-group automorphism as soon as `m t = 0` (with inverse the transvection for `-m`) or
`m t = -2` (where it is an involution); these two cases are exactly the hypotheses of
`Work.OROneRel.mmStepData_of_transvection`.  Its effect on exponent sums is

  `sigma t (mmTrans t m r) = sigma t r * FreeGroup.lift (fun x => ofAdd (m x)) r`,

i.e. additively `eps t (mmTrans t m r) = eps t r + Σ_x m x * eps x r`: the transvection shifts the
exponent sum in `t` by the value of `m` on the abelianisation of `r`.  Hence a relator with a
vanishing combination of exponent sums can be moved to one whose `t`-exponent sum is zero, which is
the situation in which the Magnus--Moldavanskii step of
`Work.OROneRel.mmStepData_of_expsum_zero` applies.

This file contains definitions and immediately provable lemmas only.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.MagnusRewrite

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The substitution underlying the transvection with respect to the generator `t` and the weight
`m`: `x ↦ x * t ^ (m x)`.  (For `x = t` this is `t ↦ t ^ (1 + m t)`.) -/
noncomputable def mmTransvectionFun (t : α) (m : α → ℤ) : α → FreeGroup α :=
  fun x => FreeGroup.of x * FreeGroup.of t ^ (m x)

/-- The transvection `x ↦ x * t ^ (m x)` of the free group `F α`. -/
noncomputable def mmTrans (t : α) (m : α → ℤ) : FreeGroup α →* FreeGroup α :=
  FreeGroup.lift (mmTransvectionFun t m)

@[simp] theorem mmTrans_of (t x : α) (m : α → ℤ) :
    mmTrans t m (FreeGroup.of x) = FreeGroup.of x * FreeGroup.of t ^ (m x) :=
  FreeGroup.lift_apply_of

/-- The transvection is `FreeGroup.lift` of its restriction to the generators. -/
theorem mmTrans_eq_lift (t : α) (m : α → ℤ) :
    mmTrans t m = FreeGroup.lift (mmTransvectionFun t m) := rfl

end Work.OROneRel
