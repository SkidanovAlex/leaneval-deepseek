import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem radZop_deriv5 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16) / (1 + y) ^ 7)
      (2 * z * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32) / (1 + z) ^ 8) z := by
  -- the polynomial is positive at no point of the proof; we only need the algebraic identity
  --   (2 y² P y)'(z) (1+z) - 7 · 2 z² P z = 2 z · Q z
  -- with `P y = y⁴ - 41y³ + 171y² - 131y + 16` and `Q z = -z⁵ + 88z⁴ - 718z³ + 1208z² - 473z + 32`,
  -- which `ring` checks once denominators are cleared.
  have hz1 : (1 : ℝ) + z ≠ 0 := fun h => hz (by linarith)
  -- derivative of the quartic factor
  have hP : HasDerivAt (fun y : ℝ => y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16)
      (4 * z ^ 3 - 123 * z ^ 2 + 342 * z - 131) z := by
    have h := ((((hasDerivAt_pow 4 z).sub ((hasDerivAt_pow 3 z).const_mul (41:ℝ))).add
        ((hasDerivAt_pow 2 z).const_mul (171:ℝ))).sub ((hasDerivAt_id' z).const_mul (131:ℝ))).add_const (16:ℝ)
    convert h using 1
    ring
  -- derivative of the numerator `2 y² · P y`
  have hN : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 4 - 41 * y ^ 3 + 171 * y ^ 2 - 131 * y + 16))
      (2 * (2 * z * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16)
        + z ^ 2 * (4 * z ^ 3 - 123 * z ^ 2 + 342 * z - 131))) z := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
    have h := (h2.const_mul (2:ℝ)).mul hP
    convert h using 1
    ring
  -- derivative of the denominator `(1 + y) ^ 7`
  have hD : HasDerivAt (fun y : ℝ => (1 + y) ^ 7) (7 * (1 + z) ^ 6) z := by
    have h := ((hasDerivAt_const z (1:ℝ)).add (hasDerivAt_id' z)).pow 7
    convert h using 1
    simp only [Pi.add_apply]
    ring
  have hz7 : (1 + z) ^ 7 ≠ 0 := pow_ne_zero 7 hz1
  -- quotient rule
  have h := hN.div hD hz7
  convert h using 1
  rw [div_eq_div_iff (pow_ne_zero 8 hz1) (pow_ne_zero 2 hz7)]
  ring

end Work.FTS.StrongPersist.L6Aux
