/-
# The axial derivative of the self-similar vorticity `W = λ⁻¹ F(ρ^p/λ, θ)`

`Work.CoreResiduals.ssVort p lam F r z t = (lam t)⁻¹ · F (ρ(r,z)^p / lam t) (θ(r,z))` with
`ρ = √(r²+z²) = Work.Cyl.rhoP` and `θ = arctan(z/r) = Work.Cyl.thetaP`.  Since

* `∂_z (ρ^p/λ) = p · (ρ^p/λ) · (z/ρ²)`   (because `∂_z ρ = z/ρ`), and
* `∂_z θ = r/ρ²`   (because `∂_z arctan(z/r) = (1/r)/(1+(z/r)²) = r/(r²+z²)`),

the two-variable chain rule (`Work.Cyl.hasDerivAt_comp_two`) gives the formula proved below:

`∂_z W = λ⁻¹ · ( (∂_ρF)·p·(ρ^p/λ)·(z/ρ²) + (∂_θF)·(r/ρ²) )`.

The factor `∂_z(ρ^p/λ)` is the delegated general lemma `Work.Cyl.hasDerivAt_rhoP_rpow_div_snd`;
the factor `∂_zθ` is the earlier `Work.Cyl.hasDerivAt_thetaP_snd`.  This is the axial companion of
`Work.CoreResiduals.pdR_ssVort_lam`; both are the chain-rule inputs of the reduction of the
meridian equation (`Work.CoreResiduals.meridianEq_of_dynEqConst`) to the profile equation of the
construction.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
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

theorem pdZ_ssVort_lam {p : ℝ} {lam : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hr : 0 < r) (hlam : lam t ≠ 0)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdZ (fun r' z' => Work.CoreResiduals.ssVort p lam F r' z' t) r z =
      (lam t)⁻¹ *
        (Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
            * (p * (Work.Cyl.rhoP r z ^ p / lam t) * (z / Work.Cyl.rhoP r z ^ 2))
          + Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
              * (r / Work.Cyl.rhoP r z ^ 2)) := by
  -- The two-variable chain rule for `z' ↦ F (ρ(r,z')^p/λ) (θ(r,z'))` at the point `(ρ^p/λ, θ)`.
  have hchain := Work.Cyl.hasDerivAt_comp_two F
    (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / lam t) (fun z' : ℝ => Work.Cyl.thetaP r z')
    (p * (Work.Cyl.rhoP r z ^ p / lam t) * (z / Work.Cyl.rhoP r z ^ 2))
    (r / Work.Cyl.rhoP r z ^ 2) z hF
    (Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z (lam t) hr)
    (Work.Cyl.hasDerivAt_thetaP_snd r z hr)
  -- Pull the constant prefactor `λ⁻¹` out of the derivative and unfold `ssVort` and `pdZ`.
  have hmain := hchain.const_mul ((lam t)⁻¹)
  rw [Work.Cyl.pdZ]
  show deriv (fun z' : ℝ =>
      (lam t)⁻¹ * F (Work.Cyl.rhoP r z' ^ p / lam t) (Work.Cyl.thetaP r z')) z = _
  rw [hmain.deriv]

end Work.CoreResiduals
