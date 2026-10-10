/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Genus.Deriv
-/
import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The quotient-rule expression for `Work.Genus.deriv`

`Work.Genus.deriv f` is defined in `Submission/Work/Genus/Defs.lean` by the quotient rule applied
to the reduced representation `f = f.num / f.denom` of a rational function:

`deriv f = (p' q - p q') / q²`, with `p = f.num`, `q = f.denom`.

The purpose of this file is to single out the *expression* `(p' q - p q') / q²` on an arbitrary
pair of polynomials as an object of study, `derivQuot p q`, so that the two facts on which the
derivation axioms for `deriv` rest can be stated cleanly:

* `derivQuot_congr` — `derivQuot p q` depends only on the element `p/q ∈ F(t)`;
* `derivQuot_mul` — the Leibniz rule for this expression, over a product `(p r)/(q s)`.

`Work.Genus.deriv x` is *definitionally* `derivQuot x.num x.denom` (`deriv_eq_derivQuot`), so once
the two facts above are available, the derivation axioms for `deriv` on `F(t)` follow by writing
the reduced representations of `f + g` and `f * g` in terms of those of `f` and `g` (Mathlib's
`RatFunc.num_denom_add`, `RatFunc.num_denom_mul`) and using the fact that
`(algebraMap (num x)) / (algebraMap (denom x)) = x` (`RatFunc.num_div_denom`).
-/

set_option autoImplicit false

open Polynomial

namespace Work.Genus.Deriv

noncomputable section

variable {F : Type*} [Field F]

/-- **The quotient-rule expression** `(p' q - p q') / q²` attached to a pair of polynomials
`(p, q)`, viewed in `F(t) = RatFunc F`.  For `q ≠ 0` it is the formal derivative of the rational
function `p/q`; for `q = 0` it is `0` by the convention `x / 0 = 0`, which is also what
`Work.Genus.deriv` gives on the (impossible) representation with zero denominator. -/
def derivQuot (p q : Polynomial F) : RatFunc F :=
  (algebraMap (Polynomial F) (RatFunc F) (Polynomial.derivative p) * algebraMap (Polynomial F) (RatFunc F) q
    - algebraMap (Polynomial F) (RatFunc F) p * algebraMap (Polynomial F) (RatFunc F) (Polynomial.derivative q))
    / (algebraMap (Polynomial F) (RatFunc F) q) ^ 2

/-- `Work.Genus.deriv` is the quotient-rule expression evaluated at the reduced representation
`f = f.num / f.denom`.  This is definitional, and is the bridge between the two languages. -/
theorem deriv_eq_derivQuot (f : RatFunc F) :
    Work.Genus.deriv f = derivQuot f.num f.denom := rfl

end

end Work.Genus.Deriv
