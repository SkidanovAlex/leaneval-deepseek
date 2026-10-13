import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.GCompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **`Γ(|θ x|) ≤ (r/ρ)^{2α}` off the axis.**

Since `Γ(θ) = (sin θ cos²θ)^β` and `cos |θ x| = r(x)/ρ(x)` (the paper's `cos θ = r/ρ`), the claim
is `(sin ψ · cos²ψ)^α ≤ (cos²ψ)^α` for `ψ = psi x = |θ x|`: the base on the left is the base on
the right multiplied by `sin ψ ≤ 1`, and both are nonnegative. -/
theorem Gamma_abs_theta_le {α : ℝ} (hα : 0 < α) {x : Work.Cyl.R3} (hr : 0 < Work.Cyl.radial x) :
    Work.ConstructionInstance.Gamma α (|Work.Cyl.theta x|)
      ≤ (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by
  have hpsi : psi x = |Work.Cyl.theta x| := psi_eq_abs_theta hr
  have hIθ : psi x ∈ Work.Spaces.Iθ := psi_mem_Iθ x
  have hcos : Real.cos (psi x) = Work.Cyl.radial x / Work.Cyl.rho x := cos_psi x
  have hcosnn : 0 ≤ Real.cos (psi x) := by
    rw [hcos]; exact div_nonneg hr.le (Work.Cyl.rho_nonneg x)
  have hsin0 : 0 ≤ Real.sin (psi x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hIθ.1 (by linarith [hIθ.2, Real.pi_pos])
  have hbase : Real.sin (psi x) * Real.cos (psi x) ^ 2 ≤ Real.cos (psi x) ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right (Real.sin_le_one (psi x)) (sq_nonneg (Real.cos (psi x)))
  have hbase0 : 0 ≤ Real.sin (psi x) * Real.cos (psi x) ^ 2 :=
    mul_nonneg hsin0 (sq_nonneg _)
  rw [← hpsi, Gamma]
  calc (Real.sin (psi x) * Real.cos (psi x) ^ 2) ^ α
      ≤ (Real.cos (psi x) ^ 2) ^ α := Real.rpow_le_rpow hbase0 hbase hα.le
    _ = Real.cos (psi x) ^ (2 * α) := by
        rw [← Real.rpow_natCast (Real.cos (psi x)) 2]
        exact (Real.rpow_mul hcosnn 2 α).symm
    _ = (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by rw [hcos]

end Work.ConstructionInstance
