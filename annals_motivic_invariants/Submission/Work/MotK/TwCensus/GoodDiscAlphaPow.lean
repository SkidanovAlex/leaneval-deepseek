/-
# The fifth power of `α = -(8r² + r⁷)`

ROUTE.  `gdAlpha r = -(8 * r ^ 2 + r ^ 7)`, so it suffices to prove
`(8 * r ^ 2 + r ^ 7) ^ 5 = 3125 * r ^ 5` from `r ^ 10 + 11 * r ^ 5 - 1 = 0`.

This is a polynomial identity modulo `g = r ^ 10 + 11 * r ^ 5 - 1`; an explicit cofactor is
`(8 * r ^ 2 + r ^ 7) ^ 5 - 3125 * r ^ 5 = g * q` with
`q = r ^ 5 * (r ^ 4 - r ^ 3 + 2 * r ^ 2 - 3 * r + 5) *
      (r ^ 16 + r ^ 15 - r ^ 14 + 21 * r ^ 11 + 26 * r ^ 10 - 16 * r ^ 9 - 5 * r ^ 8
        + 154 * r ^ 6 + 219 * r ^ 5 - 64 * r ^ 4 - 40 * r ^ 3 - 25 * r ^ 2 + 375 * r + 625)`
(verified symbolically over `ℤ`; `q` can also be found with `Polynomial.divByMonic` or by
`simp`-reducing `s = r ^ 5` to the relation `s ^ 2 + 11 * s - 1 = 0`).  `ring` after
`rw [hr]` / `linear_combination` with that cofactor closes the goal.
-/
import Mathlib
import Submission.Work.MotK.TwCensus.GoodDiscDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwCensus

/-- The certificate identity, in the variable `t = r⁵`: from `t² + 11t - 1 = 0` one gets
`t(8 + t)⁵ = 3125`, because `t(8 + t)⁵ - 3125 = (t⁴ + 29t³ + 322t² + 1607t + 3125)(t² + 11t - 1)`.
Equivalently `(8r² + r⁷)⁵ = 3125 r⁵`. -/
theorem gdAlpha_key {A : Type*} [Field A] (r : A) (hr : r ^ 10 + 11 * r ^ 5 - 1 = 0) :
    (8 * r ^ 2 + r ^ 7) ^ 5 = 3125 * r ^ 5 := by
  have h : r ^ 5 * (8 + r ^ 5) ^ 5 = 3125 := by
    linear_combination (norm := first | refl_ring1 | ring1)
      (r ^ 20 + 29 * r ^ 15 + 322 * r ^ 10 + 1607 * r ^ 5 + 3125) * hr
  calc (8 * r ^ 2 + r ^ 7) ^ 5 = r ^ 10 * (8 + r ^ 5) ^ 5 := by ring
    _ = r ^ 5 * (r ^ 5 * (8 + r ^ 5) ^ 5) := by ring
    _ = r ^ 5 * 3125 := by rw [h]
    _ = 3125 * r ^ 5 := by ring

theorem GoodDiscAlphaPow {A : Type*} [Field A] (r : A) (hr : r ^ 10 + 11 * r ^ 5 - 1 = 0) :
    gdAlpha r ^ 5 = -3125 * r ^ 5 := by
  have hneg : (-(8 * r ^ 2 + r ^ 7)) ^ 5 = -((8 * r ^ 2 + r ^ 7) ^ 5) := by ring
  rw [gdAlpha, hneg, gdAlpha_key r hr]
  first | refl_ring1 | ring

end Work.MotK.TwCensus
