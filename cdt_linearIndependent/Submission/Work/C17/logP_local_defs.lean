import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.local_exp_data

/-!
# Local data for the structure of `Pfun` at the cusp `x_s` (area C17)

This module collects the definitions used by `Work.C17.logP_local_structure` and its
supporting lemmas.

* `xsC a b` : the cusp `x_s = (a+√(a²−1))(b−√(b²−1))` as a complex number.
* `Q2x a b` : the cofactor of `P2x` by the factor `(X − x_s)`, i.e. the polynomial `q` with
  `P2x = (X − x_s)·q` and `q x_s ≠ 0`.  It is
  `(X − 1/x_s)(X−1)X(X+1)(X² − ledC·X + 1)`, where `x_s` is the root of the `ledD`-quadratic
  (`ledD = x_s + 1/x_s`).

The order-two operator `M = P2x·d²/dx² + P1x·d/dx + P0x` has a *double exponent `0`* at `x_s`
(`P1x x_s = P2x' x_s = Q2x x_s`), which is what makes the local structure of a solution
`Pfun = κ·y₁·log(x_s − ·) + hh` with `y₁` a solution of the homogeneous equation.
-/

namespace Work.C17

open Polynomial

noncomputable section

open scoped BigOperators

/-- The cusp `x_s = (a+√(a²−1))(b−√(b²−1))` as a complex number. -/
def xsC (a b : ℚ) : ℂ := (((xs a b : ℝ)) : ℂ)

/-- The cofactor `Q₂ = P₂/(X − x_s)` of the leading coefficient of `M` at the root `x_s` of `Q₄`.
Explicitly `Q₂ = (X − 1/x_s)(X−1)X(X+1)(X² − ledC·X + 1)`, so that `P2x = (X − x_s)·Q₂`. -/
def Q2x (a b : ℚ) : Polynomial ℂ :=
  (X - C ((1 / xs a b : ℝ) : ℂ)) * (X - 1) * X * (X + 1)
    * (X ^ 2 - C ((ledC a b : ℝ) : ℂ) * X + 1)

end

end Work.C17
