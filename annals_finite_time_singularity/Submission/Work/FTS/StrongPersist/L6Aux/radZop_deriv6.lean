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

/-- The sixth iterate of the radial operator `Zop u z = z·u'(z)` applied to the profile
`2z²/(1+z)³` is the rational function `2z²Q(z)/(1+z)⁹` with
`Q(z) = z⁶ - 183z⁵ + 2682z⁴ - 8422z³ + 7197z² - 1611z + 64`; this is the derivative of the
previous iterate.  The claim is a purely algebraic identity: the numerator
`N(y) = 2y²(-y⁵+88y⁴-718y³+1208y²-473y+32)` and the denominator `(1+y)⁸` are differentiated
by the product/quotient rule and the result is normalised by `ring`. -/
theorem radZop_deriv6 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (-y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32) / (1 + y) ^ 8)
      (2 * z * (z ^ 6 - 183 * z ^ 5 + 2682 * z ^ 4 - 8422 * z ^ 3 + 7197 * z ^ 2 - 1611 * z + 64) / (1 + z) ^ 9) z := by
  have hz1 : (1 + z) ≠ 0 := by intro h; exact hz (by linarith)
  -- The numerator `2y²·P(y)`.
  have hnum : HasDerivAt
      (fun y : ℝ => 2 * y ^ 2 * (-y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32))
      (4 * z * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
        + 2 * z ^ 2 * (-5 * z ^ 4 + 352 * z ^ 3 - 2154 * z ^ 2 + 2416 * z - 473)) z := by
    have h1 : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * z) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      convert h using 1
      ring
    have hP : HasDerivAt
        (fun y : ℝ => -y ^ 5 + 88 * y ^ 4 - 718 * y ^ 3 + 1208 * y ^ 2 - 473 * y + 32)
        (-5 * z ^ 4 + 352 * z ^ 3 - 2154 * z ^ 2 + 2416 * z - 473) z := by
      have t5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * z ^ 4) z := by
        have h := hasDerivAt_pow 5 z; simpa using h
      have t4 : HasDerivAt (fun y : ℝ => 88 * y ^ 4) (88 * (4 * z ^ 3)) z :=
        (hasDerivAt_pow 4 z).const_mul 88
      have t3 : HasDerivAt (fun y : ℝ => 718 * y ^ 3) (718 * (3 * z ^ 2)) z :=
        (hasDerivAt_pow 3 z).const_mul 718
      have t2 : HasDerivAt (fun y : ℝ => 1208 * y ^ 2) (1208 * (2 * z)) z := by
        have h := (hasDerivAt_pow 2 z).const_mul 1208
        convert h using 1
        ring
      have t1 : HasDerivAt (fun y : ℝ => 473 * y) (473 : ℝ) z := by
        simpa using (hasDerivAt_id z).const_mul (473 : ℝ)
      have hraw := ((((t5.neg.add t4).sub t3).add t2).sub t1).add_const 32
      convert hraw using 1
      ring
    exact h1.mul hP
  -- The denominator `(1+y)⁸`.
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 8) (8 * (1 + z) ^ 7) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) z := (hasDerivAt_id z).const_add 1
    have h := (hasDerivAt_pow 8 (1 + z)).comp z h1
    simpa [Function.comp_def] using h
  have hdiv := hnum.div hden (pow_ne_zero 8 hz1)
  -- Normalise the quotient rule result.
  convert hdiv using 1
  rw [div_eq_div_iff (pow_ne_zero 9 hz1) (pow_ne_zero 2 (pow_ne_zero 8 hz1))]
  ring

end Work.FTS.StrongPersist.L6Aux
