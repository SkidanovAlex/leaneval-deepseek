/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Genus.Deriv
-/
import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Leibniz rule for the quotient-rule expression

For `q, s ≠ 0` the quotient-rule expression `derivQuot p q = (p' q - p q') / q²` of
`Submission/Work/Genus/Deriv/Defs.lean` satisfies

`derivQuot (p r) (q s) = derivQuot p q * (r/s) + (p/q) * derivQuot r s`,

because `(p r)' (q s) - (p r) (q s)' = (p' q - p q') r s + p q (r' s - r s')`.  This is the Leibniz
rule for the expression `f ↦ derivQuot f.num f.denom`; the well-definedness statement
`derivQuot_congr` turns it into the Leibniz rule for `Work.Genus.deriv` on `F(t)`.
-/

set_option autoImplicit false

open Polynomial

namespace Work.Genus.Deriv

noncomputable section

/-- The Leibniz rule for the quotient-rule expression `derivQuot`, on a product of fractions:
for `q, s ≠ 0`, `derivQuot (p * r) (q * s) = derivQuot p q * (r/s) + (p/q) * derivQuot r s`. -/
theorem derivQuot_mul {F : Type*} [Field F] {p q r s : Polynomial F} (hq : q ≠ 0) (hs : s ≠ 0) :
    derivQuot (p * r) (q * s)
      = derivQuot p q
          * (algebraMap (Polynomial F) (RatFunc F) r / algebraMap (Polynomial F) (RatFunc F) s)
        + (algebraMap (Polynomial F) (RatFunc F) p / algebraMap (Polynomial F) (RatFunc F) q)
          * derivQuot r s := by
  -- the denominators `q` and `s` of the two fractions are nonzero in `F(t)`
  have hQ : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hS : algebraMap (Polynomial F) (RatFunc F) s ≠ 0 := RatFunc.algebraMap_ne_zero hs
  simp only [derivQuot, derivative_mul, map_add, map_mul]
  field_simp
  first | refl_ring1 | ring

end

end Work.Genus.Deriv
