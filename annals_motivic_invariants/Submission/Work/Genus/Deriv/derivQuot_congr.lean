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
# Well-definedness of the quotient-rule expression

The expression `derivQuot p q = (p' q - p q') / q²` (see `Submission/Work/Genus/Deriv/Defs.lean`)
depends only on the rational function `p / q ∈ F(t)`, not on the chosen representation: two
representations `p/q = p'/q'` of the same element of `F(t)` are related by `p q' = p' q` in `F[X]`,
and differentiating that relation (`Polynomial.derivative_mul`) gives
`p' q' + p q'' = p'' q + p' q'`, from which

`(p' q - p q') q'² - (p'' q' - p' q'') q² = q q' * (p q' - p' q)'  = 0`.

Both being nonzero, `q²` and `q'²` can be cancelled in the field `F(t)`.
-/

set_option autoImplicit false

open Polynomial

namespace Work.Genus.Deriv

noncomputable section

/-- The quotient-rule expression `derivQuot p q = (p' q - p q') / q²` in `F(t) = RatFunc F` depends
only on the rational function `p/q`: if `p * q' = p' * q` in `F[X]` and `q, q' ≠ 0`, then
`derivQuot p q = derivQuot p' q'`. -/
theorem derivQuot_congr {F : Type*} [Field F] {p q p' q' : Polynomial F}
    (h : p * q' = p' * q) (hq : q ≠ 0) (hq' : q' ≠ 0) :
    derivQuot p q = derivQuot p' q' := by
  -- the relation `p q' = p' q`, and its formal derivative, in `F(t)`
  have h1 : algebraMap (Polynomial F) (RatFunc F) p * algebraMap (Polynomial F) (RatFunc F) q'
      = algebraMap (Polynomial F) (RatFunc F) p' * algebraMap (Polynomial F) (RatFunc F) q := by
    rw [← map_mul, ← map_mul, h]
  have h2 : algebraMap (Polynomial F) (RatFunc F) p.derivative * algebraMap (Polynomial F) (RatFunc F) q'
        + algebraMap (Polynomial F) (RatFunc F) p * algebraMap (Polynomial F) (RatFunc F) q'.derivative
      = algebraMap (Polynomial F) (RatFunc F) p'.derivative * algebraMap (Polynomial F) (RatFunc F) q
        + algebraMap (Polynomial F) (RatFunc F) p' * algebraMap (Polynomial F) (RatFunc F) q.derivative := by
    have hd : Polynomial.derivative (p * q') = Polynomial.derivative (p' * q) := by rw [h]
    have := congrArg (algebraMap (Polynomial F) (RatFunc F)) hd
    simpa only [map_add, map_mul, Polynomial.derivative_mul] using this
  -- clear denominators in `F(t)` and finish with the two relations above
  unfold derivQuot
  rw [div_eq_div_iff (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hq))
    (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hq'))]
  linear_combination (norm := first | refl_ring1 | ring1) h1 * (-(algebraMap (Polynomial F) (RatFunc F) q' * algebraMap (Polynomial F) (RatFunc F) q.derivative
        + algebraMap (Polynomial F) (RatFunc F) q * algebraMap (Polynomial F) (RatFunc F) q'.derivative))
      + h2 * (algebraMap (Polynomial F) (RatFunc F) q * algebraMap (Polynomial F) (RatFunc F) q')

end

end Work.Genus.Deriv
