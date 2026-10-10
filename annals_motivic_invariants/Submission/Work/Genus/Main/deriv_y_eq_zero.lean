import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.deriv_weierstrass

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

/-- **The ordinate is constant whenever the abscissa is.**  If `(x, y)` is a `𝔽(t)`-point of the
Weierstrass curve `E` with `w = 2y + a₁x + a₃ ≠ 0` and `deriv x = 0`, then `deriv y = 0`.

Route: `Work.Genus.Deriv.deriv_weierstrass` gives `w * deriv y = δ * deriv x = 0`, and `w ≠ 0` in
the field `𝔽(t)`. -/
theorem deriv_y_eq_zero {F : Type*} [Field F] (E : WeierstrassCurve F) {x y : RatFunc F}
    (h : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
      = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
        + algebraMap F (RatFunc F) E.a₆)
    (hw : 2 * y + algebraMap F (RatFunc F) E.a₁ * x + algebraMap F (RatFunc F) E.a₃ ≠ 0)
    (hx : Work.Genus.deriv x = 0) : Work.Genus.deriv y = 0 := by
  have hd := Work.Genus.Deriv.deriv_weierstrass E h
  rw [hx, mul_zero] at hd
  exact (mul_eq_zero.mp hd).resolve_left hw

end Work.Genus.Main
