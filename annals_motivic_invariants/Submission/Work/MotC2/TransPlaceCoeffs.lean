/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# Coefficients of the explicit translation formulae in the chart at infinity

For a Weierstrass curve `E` over a field `L` and an affine point `T = (a, b)` of `E`, the
coordinates `U = transX E T`, `V = transY E T` of the translate `genPoint + T` of the generic point
can be written explicitly in the chart at infinity `u = 1/x`, `w = y/x²`:

* `(U - a)·(1 - a·u)² = μ·u + κ·u² - μ·w` — hmm, more precisely
  `(U - a)·(1 - a·u)² = λ·u + κ·u² - μ·w`;
* `(V - b)·(1 - a·u)³` is a polynomial in `u` and `w` of degree `3` in `u`.

The three constants involved are the ones defined here:
`μ = 2b + a₁a + a₃`, `λ = 3a² + 2a₂a + a₄ - a₁b`, `κ = a₆ + b² + a₁ab - 2a³ - a₂a²`.

## Tags

elliptic curve, function field, translation, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- The constant `μ = 2b + a₁a + a₃` attached to an affine point `(a, b)` of a Weierstrass curve;
it vanishes exactly when the point is `2`-torsion. -/
noncomputable def muCoeff (E : WeierstrassCurve L) (a b : L) : L :=
  2 * b + E.a₁ * a + E.a₃

/-- The constant `λ = 3a² + 2a₂a + a₄ - a₁b` attached to an affine point `(a, b)` of a Weierstrass
curve. -/
noncomputable def lamCoeff (E : WeierstrassCurve L) (a b : L) : L :=
  3 * a ^ 2 + 2 * E.a₂ * a + E.a₄ - E.a₁ * b

/-- The constant `κ = a₆ + b² + a₁ab - 2a³ - a₂a²` attached to an affine point `(a, b)` of a
Weierstrass curve. -/
noncomputable def kapCoeff (E : WeierstrassCurve L) (a b : L) : L :=
  E.a₆ + b ^ 2 + E.a₁ * a * b - 2 * a ^ 3 - E.a₂ * a ^ 2

end Work.MotC2
