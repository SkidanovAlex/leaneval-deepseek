/-
# The axial derivative of the self-similar stream function `ψ = ρ² · λ⁻¹ Φ(ρ^p/λ, θ)`

`Work.CoreResiduals.ssPsi p lam Φ r z t = ρ(r,z)² · (λ(t))⁻¹ · Φ (ρ(r,z)^p/λ(t)) (θ(r,z))`
with `ρ = √(r²+z²) = Work.Cyl.rhoP` and `θ = arctan(z/r) = Work.Cyl.thetaP`.

Since

* `∂_z (ρ²) = 2·ρ·∂_zρ = 2z`,
* `∂_z (ρ^p/λ) = p · (ρ^p/λ) · (z/ρ²)`  (`Work.Cyl.hasDerivAt_rhoP_rpow_div_snd`), and
* `∂_z θ = r/ρ²`  (`Work.Cyl.hasDerivAt_thetaP_snd`),

the product rule together with the two-variable chain rule (`Work.Cyl.hasDerivAt_comp_two`)
gives the formula proved below:

`∂_z ψ = λ⁻¹ · ( 2z·Φ + ρ²·( (∂_ρΦ)·p·(ρ^p/λ)·(z/ρ²) + (∂_θΦ)·(r/ρ²) ) )`.

This is the axial companion of `Work.CoreResiduals.pdR_ssPsi_lam` and of
`Work.CoreResiduals.pdZ_ssVort_lam`; together they are the chain-rule inputs of the reduction of
the meridian equation (`Work.CoreResiduals.meridianEq_of_dynEqConst`) to the profile equation of
the construction.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.Cyl.pdZ_comp_polar
import Submission.Work.Cyl.pdZ_comp_polar_rho
import Submission.Work.Cyl.hasDerivAt_rhoP_rpow_div_snd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.CoreResiduals

theorem pdZ_ssPsi_lam {p : ℝ} {lam : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hr : 0 < r) (hlam : lam t ≠ 0)
    (hΦ : Work.Cyl.DiffAt2 Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => Work.CoreResiduals.ssPsi p lam Φ r' z' t) r z =
      (lam t)⁻¹ *
        (2 * z * Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
          + (Work.Cyl.rhoP r z) ^ 2 *
              (Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
                  * (p * (Work.Cyl.rhoP r z ^ p / lam t) * (z / Work.Cyl.rhoP r z ^ 2))
                + Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
                    * (r / Work.Cyl.rhoP r z ^ 2))) := by
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  -- The two-variable chain rule for `z' ↦ Φ (ρ(r,z')^p/λ) (θ(r,z'))` at the point `(ρ^p/λ, θ)`.
  have hchain : HasDerivAt
      (fun z' : ℝ => Φ (Work.Cyl.rhoP r z' ^ p / lam t) (Work.Cyl.thetaP r z'))
      (Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / lam t) * (z / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
            * (r / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_comp_two Φ
      (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / lam t) (fun z' : ℝ => Work.Cyl.thetaP r z')
      (p * (Work.Cyl.rhoP r z ^ p / lam t) * (z / Work.Cyl.rhoP r z ^ 2))
      (r / Work.Cyl.rhoP r z ^ 2) z hΦ
      (Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z (lam t) hr)
      (Work.Cyl.hasDerivAt_thetaP_snd r z hr)
  -- Multiply by the outer constant `λ⁻¹`.
  have hpsi : HasDerivAt
      (fun z' : ℝ => (lam t)⁻¹ * Φ (Work.Cyl.rhoP r z' ^ p / lam t) (Work.Cyl.thetaP r z'))
      ((lam t)⁻¹ *
        (Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
            * (p * (Work.Cyl.rhoP r z ^ p / lam t) * (z / Work.Cyl.rhoP r z ^ 2))
          + Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
              * (r / Work.Cyl.rhoP r z ^ 2))) z :=
    hchain.const_mul ((lam t)⁻¹)
  -- `∂_z (ρ²) = 2·ρ·(z/ρ) = 2z`.
  have hsq : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) (2 * z) z := by
    have h := (Work.Cyl.hasDerivAt_rhoP_snd r z hr).pow 2
    rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one] at h
    have hval : 2 * Work.Cyl.rhoP r z * (z / Work.Cyl.rhoP r z) = 2 * z := by
      field_simp
    exact h.congr_deriv hval
  -- Product rule and final arithmetic.
  have hprod := hsq.mul hpsi
  rw [Work.Cyl.pdZ]
  rw [show (fun z' : ℝ => Work.CoreResiduals.ssPsi p lam Φ r z' t) =
      ((fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) *
        fun z' : ℝ => (lam t)⁻¹ * Φ (Work.Cyl.rhoP r z' ^ p / lam t) (Work.Cyl.thetaP r z'))
      from rfl]
  rw [hprod.deriv]
  ring

end Work.CoreResiduals
