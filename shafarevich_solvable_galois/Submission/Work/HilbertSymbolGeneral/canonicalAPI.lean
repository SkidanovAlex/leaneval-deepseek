import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Field.ZMod
import Submission.Work.HilbertSymbolGeneral.hilbertSymbol_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical-level API of the `2`-adic Hilbert symbol

`NK.NUV2.LC.hilbertSymbol R a b` is the canonical Hilbert symbol (the square root of `b` is
chosen in the separable closure, so the symbol depends on `(a,b)` alone).  The `hilbertSymbolAt`
form of the basic properties is proved in `Submission/NK/NUV2/LC/hilbertSymbol.lean`
(`hilbertSymbolAt_mul` for multiplicativity in the first variable, `hilbertSymbolAt_self_mul_left`
for the vanishing on squares, `hilbertSymbol_eq_one_iff_normGroup` for the norm criterion, and
`hilbertSymbolAt_independent` for the independence of the square root), but the *canonical* form —
the one a user of the chapter states — is not recorded there.

This module records the canonical-level statements.  Everything here is a formal consequence of
the `hilbertSymbolAt`-level lemmas above (the square root occurring in `hilbertSymbol R · b` is the
same in all the terms of a computation at a fixed `b`), so the file is thin; it exists so that the
chapter's users (e.g. the verification of Schmidt–Wingberg §4) can manipulate
`hilbertSymbol R a b` directly.

The names live in the sub-namespace `Work.HilbertSymbolGeneral.canonicalAPI` to leave the bare
names in `Work.HilbertSymbolGeneral` free for the delegated arithmetic statements of the chapter
(`hilbertSymbol_comm`, `hilbertSymbol_mul_right`, `hilbertReciprocityTwo`).
-/

open scoped Classical

namespace Work.HilbertSymbolGeneral.canonicalAPI

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F']
  [IsSepClosure F F'] [NeZero (2 : F)]

/-- **Multiplicativity of the canonical Hilbert symbol in the first variable**:
`(a a', b) = (a,b) · (a',b)`. -/
theorem hilbertSymbol_mul_left (R : NK.LocalArtin.ReciprocityMap F F') (a a' b : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R (a * a') b =
      NK.NUV2.LC.hilbertSymbol R a b * NK.NUV2.LC.hilbertSymbol R a' b := by
  simp only [NK.NUV2.LC.hilbertSymbol]
  exact NK.NUV2.LC.hilbertSymbolAt_mul R _ _ _ a a'

/-- **The canonical Hilbert symbol vanishes on a square in the first variable**:
`(a², b) = 1`. -/
theorem hilbertSymbol_sq_left (R : NK.LocalArtin.ReciprocityMap F F') (a b : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R (a * a) b = 1 := by
  simp only [NK.NUV2.LC.hilbertSymbol]
  exact NK.NUV2.LC.hilbertSymbolAt_self_mul_left R _ _ _ a

/-- **Multiplicativity of the canonical Hilbert symbol in the second variable**:
`(a, b b') = (a,b) · (a,b')`.  A formal consequence of symmetry
(`Work.HilbertSymbolGeneral.hilbertSymbol_comm`) and first-variable multiplicativity:
`(a, b b') = (b b', a) = (b,a) (b',a) = (a,b) (a,b')`. -/
theorem hilbertSymbol_mul_right (R : NK.LocalArtin.ReciprocityMap F F') (a b b' : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R a (b * b') =
      NK.NUV2.LC.hilbertSymbol R a b * NK.NUV2.LC.hilbertSymbol R a b' := by
  rw [Work.HilbertSymbolGeneral.hilbertSymbol_comm R a (b * b'),
    hilbertSymbol_mul_left R b b' a,
    Work.HilbertSymbolGeneral.hilbertSymbol_comm R b a,
    Work.HilbertSymbolGeneral.hilbertSymbol_comm R b' a]

/-- **The canonical Hilbert symbol vanishes on a square in the second variable**: `(a, b²) = 1`.
(Formal, because the values lie in the exponent-`2` group `Multiplicative (ZMod 2)`.) -/
theorem hilbertSymbol_sq_right (R : NK.LocalArtin.ReciprocityMap F F') (a b : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R a (b * b) = 1 := by
  rw [hilbertSymbol_mul_right, NK.NUV2.LC.mul_self_eq_one_zmod_two]

/-- **Triviality in the second variable**: `(a, 1) = 1`. -/
@[simp] theorem hilbertSymbol_one_right (R : NK.LocalArtin.ReciprocityMap F F') (a : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R a 1 = 1 := by
  simpa using hilbertSymbol_sq_right R a 1

/-- **Triviality in the first variable**: `(1, b) = 1`. -/
@[simp] theorem hilbertSymbol_one_left (R : NK.LocalArtin.ReciprocityMap F F') (b : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R 1 b = 1 := by
  simpa using hilbertSymbol_sq_left R 1 b

end Work.HilbertSymbolGeneral.canonicalAPI
