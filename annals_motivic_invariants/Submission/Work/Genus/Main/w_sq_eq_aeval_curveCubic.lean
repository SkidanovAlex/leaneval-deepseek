import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

open Polynomial

/-- **Completing the square.**  If `(x, y)` satisfies the Weierstrass equation of `E`, then the
"completed ordinate" `w = 2y + a₁x + a₃` satisfies `w ^ 2 = A(x)` for the cubic
`A = Work.Genus.curveCubic E = 4X³ + b₂X² + 2b₄X + b₆` (with `b₂ = a₁² + 4a₂`,
`b₄ = 2a₄ + a₁a₃`, `b₆ = a₃² + 4a₆`).  A `ring` computation after rewriting with the equation:
`w² = 4(y² + a₁xy + a₃y) + (a₁x + a₃)²`. -/
theorem w_sq_eq_aeval_curveCubic {F : Type*} [Field F] (E : WeierstrassCurve F) {x y : RatFunc F}
    (h : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
      = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
        + algebraMap F (RatFunc F) E.a₆) :
    (2 * y + algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃) ^ 2
      = Polynomial.aeval x (Work.Genus.curveCubic E) := by
  -- Evaluate the cubic polynomial at `x`: `A(x) = 4x³ + b₂x² + 2b₄x + b₆`.
  have haeval : Polynomial.aeval x (Work.Genus.curveCubic E)
      = 4 * x ^ 3 + algebraMap F (RatFunc F) E.b₂ * x ^ 2
        + 2 * (algebraMap F (RatFunc F) E.b₄) * x + algebraMap F (RatFunc F) E.b₆ := by
    rw [Work.Genus.curveCubic]
    simp only [map_mul, map_ofNat, map_add, map_pow, aeval_C, aeval_X]
  rw [haeval]
  -- Complete the square: `w² = 4(y² + a₁xy + a₃y) + (a₁x + a₃)²`.
  have key : (2 * y + algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃) ^ 2
      = 4 * (y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y)
        + (algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃) ^ 2 := by ring
  rw [key, h]
  -- Expand `b₂`, `b₄`, `b₆` and compare.
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  first | refl_ring1 | ring

end Work.Genus.Main
