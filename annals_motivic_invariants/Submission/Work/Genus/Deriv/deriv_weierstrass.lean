import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.deriv_aeval
import Submission.Work.Genus.Deriv.deriv_mul
import Submission.Work.Genus.Deriv.deriv_add
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Deriv

/-- **The formal derivative on `F(t)` kills the constants.**  For `c : F`, the image
`algebraMap F (RatFunc F) c` is the constant polynomial `C c` viewed in `F(t)`, so its
derivative is `C c' = 0` by `deriv_algebraMap`. -/
private theorem deriv_C {F : Type*} [Field F] (c : F) :
    Work.Genus.deriv (algebraMap F (RatFunc F) c) = 0 := by
  have h1 : algebraMap F (RatFunc F) c
      = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c) := by
    rw [show (Polynomial.C c : Polynomial F) = algebraMap F (Polynomial F) c from rfl]
    exact (IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F) c).symm
  rw [h1, deriv_algebraMap, Polynomial.derivative_C, map_zero]

/-- **The differentiated Weierstrass equation.**  If `(x, y)` satisfies
`y ^ 2 + a₁ x y + a₃ y = x ^ 3 + a₂ x ^ 2 + a₄ x + a₆` in `F(t)`, then
`(2y + a₁x + a₃) * y' = (3x² + 2a₂x + a₄ - a₁y) * x'`.

Apply `deriv` to both sides and rewrite with `Work.Genus.Deriv.deriv_add`,
`Work.Genus.Deriv.deriv_mul`, `Work.Genus.Deriv.deriv_algebraMap` (`deriv` kills the constants);
the result is `2y y' + a₁(x'y + xy') + a₃y' = 3x²x' + 2a₂xx' + a₄x'`, which rearranges to the
statement. -/
theorem deriv_weierstrass {F : Type*} [Field F] (E : WeierstrassCurve F) {x y : RatFunc F}
    (h : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
      = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
        + algebraMap F (RatFunc F) E.a₆) :
    (2 * y + algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃) * Work.Genus.deriv y
      = (3 * x ^ 2 + algebraMap F (RatFunc F) E.a₂ * 2 * x + algebraMap F (RatFunc F) E.a₄
          - algebraMap F (RatFunc F) E.a₁ * y) * Work.Genus.deriv x := by
  -- write the cube as a square times the element, so that `deriv_mul` applies to every factor
  have h3 : x ^ 3 = x ^ 2 * x := by ring
  rw [h3] at h
  -- differentiate the Weierstrass equation
  have hd := congrArg Work.Genus.deriv h
  -- push `deriv` through the sums and products; the constants `aᵢ` die (`deriv_C`)
  simp only [deriv_add, deriv_mul, deriv_C, pow_two] at hd
  -- the differentiated identity rearranges to the statement
  linear_combination (norm := first | refl_ring1 | ring1) hd

end Work.Genus.Deriv
