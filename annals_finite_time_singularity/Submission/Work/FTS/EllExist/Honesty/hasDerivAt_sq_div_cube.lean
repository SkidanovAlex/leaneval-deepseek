import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllExist.Honesty.G1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

/-- If `g'(z) = (-a·g(z) + c(z))/z` with `z > 0`, then the expression `w ↦ g(w)²/w³`
has derivative `(2·c(z)·g(z) - (3 + 2a)·g(z)²)/z⁴` at `z`.

Indeed `(g²/w³)' = 2g·g'/w³ - 3g²/w⁴`, and substituting the ODE for `g'` at `w = z` gives
`(2g(z)(-a·g(z) + c(z)z) - 3g(z)²)/z⁴ = (2c(z)g(z) - (3+2a)g(z)²)/z⁴`. -/
theorem hasDerivAt_sq_div_cube {a : ℝ} {c g : ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) (hg : HasDerivAt g ((-a * g z + c z) / z) z) :
    HasDerivAt (fun w : ℝ => g w ^ 2 / w ^ 3)
      ((2 * c z * g z - (3 + 2 * a) * g z ^ 2) / z ^ 4) z := by
  -- derivative of the numerator `w ↦ g w ^ 2`
  have hnum : HasDerivAt (fun w : ℝ => g w ^ 2)
      (2 * g z * ((-a * g z + c z) / z)) z := by
    simpa only [Pi.pow_def, Nat.cast_ofNat, Nat.reduceSub, pow_one] using hg.pow 2
  -- derivative of the denominator `w ↦ w ^ 3`
  have hden : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using (hasDerivAt_pow 3 z)
  have h := hnum.div hden (pow_ne_zero 3 (ne_of_gt hz))
  convert h using 1
  field_simp
  ring

end Work.FTS.EllExist.Honesty
