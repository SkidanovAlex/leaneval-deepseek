import Mathlib
import Submission.Work.HP.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Auxiliary definitions for `Work.HP.density` (node N14)

This file is *definition only* (no `sorry`), so that the lemmas delegated for N14 can import the
notions below without importing the (still incomplete) target file.

The two notions here are the ones the density argument needs:

* `pderivEval d n a i x` — the value at `x` of the formal partial derivative `∂f_a/∂x_i`, for a
  coefficient vector `a` and an integer point `x`.  It is used to state multivariate Hensel
  lifting: a primitive zero of `f_a` modulo `p^{2e+1}` whose gradient has `p`-adic valuation
  exactly `e` lifts to a primitive zero modulo `p^r` for every `r`.
* `BadCls p` — the set of classes `a mod p` all of whose `F_p`-zeros are singular.  A form whose
  residue class mod `p` lies in `BadCls p` is exactly one for which Hensel lifting is not
  available at `p`; these are the "bad" classes whose paucity drives the density argument.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

/-- The value at `x` of the formal partial derivative of `f_a` with respect to `x_i`,
for the coefficient vector `a` (monomial basis, no multinomial weights). -/
def pderivEval (d n : ℕ) (a : Mon d n → ℤ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℤ) : ℤ :=
  ∑ m : Mon d n, (a m) * (m.1 i : ℤ) *
    ∏ j : Fin (n + 1), x j ^ ((m.1 j : ℕ) - if j = i then 1 else 0)

/-- The value at `x` of the formal partial derivative, over `ZMod p`. -/
def pderivEvalZMod (d n p : ℕ) (a : Mon d n → ℤ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ZMod p) : ZMod p :=
  ∑ m : Mon d n, (a m : ZMod p) * (m.1 i : ℤ) *
    ∏ j : Fin (n + 1), x j ^ ((m.1 j : ℕ) - if j = i then 1 else 0)

/-- `BadOver p`: the coefficient vectors mod `p` all of whose nonzero `F_p`-zeros are singular,
i.e. forms whose reduction mod `p` has no nonsingular `F_p`-zero.  (A form with no nonzero
`F_p`-zero at all vacuously satisfies this; the corresponding class set is `B_p` in the design.) -/
def BadOver (d n p : ℕ) (a : Mon d n → ℤ) : Prop :=
  ∀ x : Fin (n + 1) → ZMod p, x ≠ 0 → formEval d n a x = 0 →
    ∀ i : Fin (n + 1), pderivEvalZMod d n p a i x = 0

end Work.HP

namespace Work.HP

/-- The evaluation of the reduction mod `p` of `f_a` at a point over `ZMod p`. -/
def formEvalZMod (d n p : ℕ) (a : Mon d n → ZMod p) (x : Fin (n + 1) → ZMod p) : ZMod p :=
  ∑ m : Mon d n, a m * ∏ j : Fin (n + 1), x j ^ ((m.1 j : ℕ))

/-- A coefficient class `a` mod `p` is *bad* (`BadCls`) if its reduction has no nonsingular
`F_p`-zero, i.e. every nonzero zero of `f_a` over `F_p` is a singular point.  These are exactly
the classes for which the Hensel lifting of `hensel_lift` is unavailable, so that a form reducing
to such a class at `p` may fail to have a primitive zero mod `p^r` for large `r`. -/
def BadCls (d n p : ℕ) (a : Mon d n → ZMod p) : Prop :=
  ∀ x : Fin (n + 1) → ZMod p, x ≠ 0 → formEvalZMod d n p a x = 0 →
    ∀ i : Fin (n + 1), (∑ m : Mon d n, a m * (m.1 i : ZMod p) *
      ∏ j : Fin (n + 1), x j ^ ((m.1 j : ℕ) - if j = i then 1 else 0)) = 0

end Work.HP
