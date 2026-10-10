import Mathlib
import Submission.Work.Genus.CharP.DescentBasic
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

open Polynomial

/-- **A point of a Weierstrass curve whose abscissa is constant has constant ordinate.**

If `x = c` is the image of an element of `F`, then the Weierstrass equation
`y² + a₁ x y + a₃ y = x³ + a₂ x² + a₄ x + a₆` becomes the quadratic equation
`y² + (a₁ c + a₃) y - (c³ + a₂ c² + a₄ c + a₆) = 0` for `y`, so `y` is algebraic over `F`
(being a root of the non-zero polynomial `T² + (a₁ c + a₃) T - (c³ + a₂ c² + a₄ c + a₆)`).
Since `F` is algebraically closed in `F(t)`
(`Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic`), `y` must be constant. -/
theorem isConst_of_isConst_abscissa {F : Type*} [Field F] (E : WeierstrassCurve F)
    {x y : RatFunc F} (h : Work.Genus.CharP.WEqn E x y) (hx : Work.Genus.CharP.IsConst x) :
    Work.Genus.CharP.IsConst y := by
  obtain ⟨c, rfl⟩ := hx
  show ∃ d, y = algebraMap F (RatFunc F) d
  refine Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic ?_
  unfold Work.Genus.CharP.WEqn at h
  -- `y` is a root of the quadratic `T² + (a₁ c + a₃) T - (c³ + a₂ c² + a₄ c + a₆) ∈ F[T]`.
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (E.a₁ * c + E.a₃) * Polynomial.X
      - Polynomial.C (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆), ?_, ?_⟩
  · -- The polynomial is non-zero: its `T²`-coefficient is `1`.
    intro hp
    have hc : (Polynomial.X ^ 2 + Polynomial.C (E.a₁ * c + E.a₃) * Polynomial.X
        - Polynomial.C (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆)).coeff 2 = 1 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    rw [hp] at hc
    simp at hc
  · -- Evaluating at `y` gives the Weierstrass equation, which holds by hypothesis.
    simp only [map_add, map_mul, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination (norm := first | refl_ring1 | ring1) h

end Work.Genus.CharP
