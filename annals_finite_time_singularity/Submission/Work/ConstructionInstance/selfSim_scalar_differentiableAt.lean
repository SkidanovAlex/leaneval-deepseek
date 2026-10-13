import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.Cyl.differentiableAt_rho_theta_comp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **Differentiability of the scalar self-similar vorticity profile.**

At a point `x` off the axis (`0 < radial x`) at which the profile `F = profile p g` is
differentiable as a function of two variables at the self-similar point
`(ρ(x)^p / c, θ(x))`, the scalar field

  `y ↦ c⁻¹ * F (ρ(y)^p / c) (θ(y))`

is differentiable at `x`.

The proof is the chain rule: `ρ` is differentiable at `x` (`Work.Cyl.differentiableAt_rho_of_radial_pos`,
legitimate since `radial x > 0`), hence so is `y ↦ ρ(y)^p / c` (rpow with nonzero base
`ρ x ≠ 0`, then division by the constant `c`); together with the differentiability of `θ`
(`Work.Cyl.differentiableAt_theta_of_radial_ne`) this makes `y ↦ (ρ(y)^p / c, θ(y))`
differentiable at `x`, and composing with `hF` and multiplying by the constant `c⁻¹` gives the
claim. -/
theorem selfSim_scalar_differentiableAt {p c : ℝ} {g : ℝ → ℝ → ℝ} {x : Work.ConstructionInstance.R3}
    (hr : 0 < Work.Cyl.radial x)
    (hF : Work.Cyl.DiffAt2 (Work.ConstructionInstance.profile p g) (Work.Cyl.rho x ^ p / c)
      (Work.Cyl.theta x)) :
    DifferentiableAt ℝ
      (fun y : Work.ConstructionInstance.R3 =>
        c⁻¹ * Work.ConstructionInstance.profile p g (Work.Cyl.rho y ^ p / c)
          (Work.Cyl.theta y)) x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hrho_ne : Work.Cyl.rho x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x))
  have hpow : DifferentiableAt ℝ (fun y : Work.ConstructionInstance.R3 => Work.Cyl.rho y ^ p) x :=
    (Work.Cyl.differentiableAt_rho_of_radial_pos x hr).rpow_const (Or.inl hrho_ne)
  have hdiv : DifferentiableAt ℝ
      (fun y : Work.ConstructionInstance.R3 => Work.Cyl.rho y ^ p / c) x := by
    simpa only [div_eq_mul_inv] using hpow.mul_const c⁻¹
  have hpair : DifferentiableAt ℝ
      (fun y : Work.ConstructionInstance.R3 =>
        (Work.Cyl.rho y ^ p / c, Work.Cyl.theta y)) x :=
    hdiv.prodMk (Work.Cyl.differentiableAt_theta_of_radial_ne x hrne)
  exact (hF.comp x hpair).const_mul c⁻¹

end Work.ConstructionInstance
