import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial weighted `z`-derivative bound for `2α/(1+z)`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

For the rational function `B(z) = 2α/(1+z) = 2α·(1+z)⁻¹` one has the closed form

`deriv^[k] B z = (-1)^k k! · 2α · (1+z)^{-(k+1)}`   (`z > -1`),

so that the weight `(z+1)^k` cancels all but one power of `(1+z)⁻¹`:

`(z+1)^k deriv^[k] B z = (-1)^k k! · 2α · (1+z)⁻¹`,  hence `|…| ≤ 2α k!` for `z ≥ 0`.

The machinery for the closed form (`nInvClosed`, `iter_deriv_nInvClosed`,
`deriv_iter_const_mul`, `nInvClosed_weighted`) is proved in the sibling module
`Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points` and reused here.
-/

noncomputable section

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

theorem c2mInv_radial (α : ℝ) (hα : 0 < α) (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] (fun z : ℝ => 2 * α / (1 + z)) z| ≤ 2 * α * (k.factorial : ℝ) := by
  have hz1 : -1 < z := by linarith
  have hα2 : (0 : ℝ) ≤ 2 * α := by linarith
  -- closed form of the `k`-th derivative of `2α/(1+z)`
  have hB : deriv^[k] (fun z : ℝ => 2 * α / (1 + z)) z = 2 * α * nInvClosed k z := by
    have h1 : (fun z : ℝ => 2 * α / (1 + z)) = fun z : ℝ => (2 * α) * ((1 + z)⁻¹) := by
      funext z; rw [div_eq_mul_inv]
    rw [h1, congrFun (deriv_iter_const_mul (2 * α) (fun z : ℝ => (1 + z)⁻¹) k) z,
      iter_deriv_nInvClosed k z hz1]
  rw [hB, show (z + 1) ^ k * (2 * α * nInvClosed k z)
        = 2 * α * ((z + 1) ^ k * nInvClosed k z) by ring,
    abs_mul, abs_of_nonneg hα2]
  exact mul_le_mul_of_nonneg_left (nInvClosed_weighted k z hz) hα2

end Work.FTS.Nonlinear.FstarPkg
