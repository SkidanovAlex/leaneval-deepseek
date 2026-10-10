import Mathlib
import Submission.Work.SilvermanReduction.Helpers
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SilvermanReduction

/-- **The chord identity computes the slope.**  For two points `(x,y)`, `(u,v)` of a Weierstrass
equation with `x ≠ u`, if the denominator `y + v + a₁x + a₃` is nonzero then
`slope x u y v = (x² + xu + u² + a₂(x+u) + a₄ - a₁v) / (y + v + a₁x + a₃)`.
This is the `x ≠ u` case of the chord identity `slope_mul_eq` of `Helpers`. -/
theorem slope_eq_div_of_chord {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve.Affine K} {x y u v : K}
    (hy : W.Equation x y) (hu : W.Equation u v) (hxu : x ≠ u)
    (hd : y + v + W.a₁ * x + W.a₃ ≠ 0) :
    W.slope x u y v
      = (x ^ 2 + x * u + u ^ 2 + W.a₂ * (x + u) + W.a₄ - W.a₁ * v)
        / (y + v + W.a₁ * x + W.a₃) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxu]
  rw [div_eq_div_iff (sub_ne_zero.mpr hxu) hd]
  linear_combination (norm := first | refl_ring1 | ring1) slope_mul_eq hy hu

end Work.SilvermanReduction
