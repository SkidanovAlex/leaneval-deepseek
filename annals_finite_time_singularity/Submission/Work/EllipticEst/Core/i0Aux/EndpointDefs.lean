/-
Copyright: work module for the Elgindi finite-time singularity project.

# The test function for the endpoint-value estimate

For the endpoint-value bound `endpointValuesCore` we use, at each scale `t > 0`, the smooth
("linear at the origin, quartic at the far end") test function

  `etaT t x = x * (1 - x/t)^3`,

whose first two derivatives are the explicit polynomials `etaT'` and `etaT''`.  The point of this
particular `η`: `η(0) = 0`, `η'(0) = 1`, `η(t) = η'(t) = 0`, the `L²(0,t)`-norm of `η` is `≲ t^{3/2}`
and the `L²(0,t)`-norm of `η''` is `≲ t^{-1/2}`, which is exactly the trade-off between the two
scales needed for the two-term estimate.

Two integrations by parts applied to `∫_0^t η · f''` and `∫_0^t η' · f` give the reproducing
formula

  `F = ∫_0^t η · f'' - ∫_0^t η'' · f`,   `F = lim_{x → 0⁺} f x`,

which bounds the endpoint value by the `L²`-norms of `f` and `f''`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The test function `η_t(x) = x (1 - x/t)^3`. -/
noncomputable def etaT (t x : ℝ) : ℝ := x * (1 - x / t) ^ 3

/-- The first derivative of `η_t`: `η_t'(x) = (1 - x/t)^2 (1 - 4x/t)`. -/
noncomputable def etaT' (t x : ℝ) : ℝ := (1 - x / t) ^ 2 * (1 - 4 * x / t)

/-- The second derivative of `η_t`: `η_t''(x) = (6/t) (1 - x/t) (2x/t - 1)`. -/
noncomputable def etaT'' (t x : ℝ) : ℝ := (6 / t) * (1 - x / t) * (2 * x / t - 1)

end Work.EllipticEst.Core.i0Aux
