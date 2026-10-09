import Submission.NK.NUV2.LC.hilbertSymbol
import Submission.NK.NUV2.LC.hilbertSymbolAt_independent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm criterion for the canonical `p = 2` Hilbert symbol

`NK.NUV2.LC.hilbertSymbol` chooses a square root of the second argument once and for all (in a
separable closure).  This file records that the symbol so defined is *independent of that choice*
(`NK.NUV2.LC.hilbertSymbolAt_independent`) and that it therefore computes the norm condition:

  `(a,b) = 1  ↔  a ∈ N_{F(√b)/F}F(√b)ˣ`   for **any** square root of `b`.

This is the form in which the `2`-torsion product formula consumes the symbol: the value
`(a,b) = -1` is exactly "`a` is not a norm from `F(√b)`", and the extension `F(√b)` does not depend
on which square root was used to write it down.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace NK.NUV2.LC

section Symbol

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F']
variable [NeZero (2 : F)]

/-- **The norm criterion for the canonical Hilbert symbol**: `(a,b) = 1` exactly when `a` is a norm
from `F(√b)`, for any square root `y` of `b` whatsoever. -/
theorem hilbertSymbol_eq_one_iff_normGroup (R : NK.LocalArtin.ReciprocityMap F F') (a b : Fˣ) :
    hilbertSymbol R a b = 1 ↔
      ∃ (y : F') (hy : y * y = algebraMap F F' (b : F)),
        a ∈ NK.LocalReciprocity.normGroup F ↥(quadLevel y (b : F) hy) := by
  constructor
  · intro h
    refine ⟨sqroot (F := F) (F' := F') b, sqroot_mul_self (F := F) (F' := F') b, ?_⟩
    exact (hilbertSymbolAt_eq_one_iff R _ _ _ a).mp h
  · rintro ⟨y, hy, hm⟩
    have h1 : hilbertSymbolAt R y (b : F) hy a = 1 :=
      (hilbertSymbolAt_eq_one_iff R y (b : F) hy a).mpr hm
    have h2 : hilbertSymbol R a b =
        hilbertSymbolAt R (sqroot (F := F) (F' := F') b) (b : F)
          (sqroot_mul_self (F := F) (F' := F') b) a := rfl
    rw [h2, hilbertSymbolAt_independent R (hy := sqroot_mul_self (F := F) (F' := F') b)
      (hy' := hy) a, h1]

end Symbol

end NK.NUV2.LC
