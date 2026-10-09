/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Mathlib
import Submission.NK.Chebotarev.ExistsSqrtInCyclotomic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Square roots of a finite family of rationals in one cyclotomic field

`NK.Chebotarev.SqrtInCyclotomic` records a cyclotomic field containing a square root of a single
rational.  For the multiquadratic case of Kronecker–Weber we need the *simultaneous* statement: a
single cyclotomic field `ℚ(ζ_n)` containing square roots of all members of a finite family
`d : Fin r → ℚ`.  This file only fixes the vocabulary; the existence statement is
`NK.Chebotarev.exists_common_sqrt`.
-/

set_option linter.unusedSectionVars false

universe u

namespace NK.Chebotarev

/-- A cyclotomic field together with square roots of a finite family of rational numbers. -/
structure CommonSqrtInCyclotomic (r : ℕ) (d : Fin r → ℚ) : Type (u + 1) where
  /-- the level of the cyclotomic field -/
  n : ℕ
  /-- the level is positive -/
  hn : 0 < n
  /-- the cyclotomic field -/
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  [algebraF : Algebra ℚ F]
  [cycloF : IsCyclotomicExtension {n} ℚ F]
  /-- the square roots -/
  s : Fin r → F
  /-- they are square roots of the corresponding `d i` -/
  s_sq : ∀ i, s i ^ 2 = algebraMap ℚ F (d i)

attribute [instance] CommonSqrtInCyclotomic.fieldF CommonSqrtInCyclotomic.numberFieldF
  CommonSqrtInCyclotomic.algebraF CommonSqrtInCyclotomic.cycloF

end NK.Chebotarev
