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

theorem radZop_deriv4 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (-y ^ 3 + 18 * y ^ 2 - 33 * y + 8) / (1 + y) ^ 6)
      (2 * z * (z ^ 4 - 41 * z ^ 3 + 171 * z ^ 2 - 131 * z + 16) / (1 + z) ^ 7) z := by
  have hz1 : (1 + z : ℝ) ≠ 0 := by intro h; exact hz (by linarith)
  -- ∂_z (z^2) = 2z, ∂_z (z^3) = 3z^2
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
  -- the numerator polynomial  N y = -y^3 + 18 y^2 - 33 y + 8
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 3) (-(3 * z ^ 2)) z := h3.neg
  have h18 : HasDerivAt (fun y : ℝ => 18 * y ^ 2) (18 * (2 * z)) z := h2.const_mul 18
  have h33 : HasDerivAt (fun y : ℝ => 33 * y) (33 * 1) z := (hasDerivAt_id z).const_mul 33
  have h8 : HasDerivAt (fun y : ℝ => (8 : ℝ)) 0 z := hasDerivAt_const z 8
  have hN : HasDerivAt (fun y : ℝ => -y ^ 3 + 18 * y ^ 2 - 33 * y + 8)
      (-(3 * z ^ 2) + 18 * (2 * z) - 33 * 1 + 0) z :=
    ((h1.add h18).sub h33).add h8
  have h2N : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (2 * (2 * z)) z := h2.const_mul 2
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (-y ^ 3 + 18 * y ^ 2 - 33 * y + 8))
      (2 * (2 * z) * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8)
        + 2 * z ^ 2 * (-(3 * z ^ 2) + 18 * (2 * z) - 33 * 1 + 0)) z :=
    h2N.mul hN
  -- ∂_z ((1+z)^6) = 6 (1+z)^5
  have hshift : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have hden := by simpa using hshift.pow 6
  have hz6 : (1 + z) ^ 6 ≠ 0 := pow_ne_zero 6 hz1
  refine (hnum.div hden hz6).congr_deriv ?_
  field_simp
  simp only [Pi.pow_apply]
  ring

end Work.FTS.StrongPersist.L6Aux
