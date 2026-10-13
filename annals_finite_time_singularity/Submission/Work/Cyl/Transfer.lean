import Mathlib.Tactic.MinImports
import Submission.Work.Cyl.pdR_comp_polar
import Submission.Work.Cyl.pdZ_comp_polar
import Submission.Work.Cyl.pdR_comp_polar_rho
import Submission.Work.Cyl.pdZ_comp_polar_rho
import Submission.Work.Cyl.alpha_mul_pow_mul_pdR

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The transfer lemmas for the polar change of variables `(r, x₃) ↦ (ρ, θ)`, `R = ρ^α`

This module collects the chain-rule dictionary of §Setup (paper line 258):

* `Work.Cyl.pdR_comp_polar` : `∂_r [F(ρ^α, θ)] = (cos θ/ρ)·αR·∂_R F − (sin θ/ρ)·∂_θ F`
* `Work.Cyl.pdZ_comp_polar` : `∂_{x₃} [F(ρ^α, θ)] = (sin θ/ρ)·αR·∂_R F + (cos θ/ρ)·∂_θ F`
* `Work.Cyl.pdR_comp_polar_rho`, `Work.Cyl.pdZ_comp_polar_rho` : the same with `G(ρ, θ)`
  (`α = 0` form, `∂_ρ` instead of `R ∂_R`)
* `Work.Cyl.alpha_mul_pow_mul_pdR` : `α R ∂_R = ρ ∂_ρ`, i.e.
  `α · ρ^α · ∂_R F(ρ^α, θ) = ρ · ∂_ρ (F(ρ^α, θ))`
* the same dictionary read on `ℝ³` itself (the direction `e_r` is `∂_r`, the direction `e₃` is
  `∂_{x₃}`): `Work.Cyl.fderiv_rho_theta_eR`, `Work.Cyl.fderiv_rho_theta_eZ`,
  `Work.Cyl.fderiv_R_theta_eR`, `Work.Cyl.fderiv_R_theta_eZ`
  (e.g. `fderiv ℝ (fun y ↦ F (ρ y ^ α) (θ y)) x (e_r x)
   = (cos θ/ρ)·αR·∂_R F − (sin θ/ρ)·∂_θ F` with `ρ = rho x`, `θ = theta x`).

Here `Work.Cyl.rhoP r z = √(r²+z²)`, `Work.Cyl.thetaP r z = arctan(z/r)`,
`Work.Cyl.pdR`, `Work.Cyl.pdZ` are the partial derivatives `∂_r`, `∂_{x₃}`, and
`Real.cos (thetaP r z) = r/ρ`, `Real.sin (thetaP r z) = z/ρ` (see `Work.Cyl.cos_thetaP`,
`Work.Cyl.sin_thetaP`).
-/
