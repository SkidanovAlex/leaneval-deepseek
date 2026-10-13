/-
# The cylindrical / polar calculus layer for axisymmetric no-swirl fields on ℝ³

This is the `Work.Cyl` area: the coordinate dictionary of §Setup of Elgindi's paper
(Annals of Math. **194** (2021) 771--887, lines 222--310 of the LaTeX source).

## Conventions

* `R3 = EuclideanSpace ℝ (Fin 3)`, coordinates `0`, `1` in the plane and coordinate `2` on the
  symmetry axis (the paper's `x₃`).  This choice is forced by `FiniteTimeSingularity.IsOdd`, whose
  third conjunct is oddness/evenness in coordinate `2`.
* On ℝ³: `radial x = √(x₀²+x₁²)` (`r`), `axial x = x₃`, `radialVec x = (x₀,x₁,0) = r e_r`,
  `angularVec x = (-x₁,x₀,0) = r e_θ`, `eR`, `eTheta`, `eZ`,
  `rho x = √(r²+x₃²) = ‖x‖`, `theta x = arctan(x₃/r)`, `Rc α x = ρ^α`.
* Two-variable functions are curried `f : ℝ → ℝ → ℝ`, `f r z`; `pdR f r z = ∂_r f`,
  `pdZ f r z = ∂_{x₃} f` are slice derivatives, `pdRR`, `pdZZ` the second ones.
* `rhoP r z = √(r²+z²)`, `thetaP r z = arctan(z/r)`, `RP α r z = ρ^α` are the same objects on the
  `(r,x₃)` plane, where the transfer lemmas of item 1 live.
* Fields: `cylField ur uz x = (u_r(r,x₃)/r) • (x₀,x₁,0) + u_z(r,x₃) • e₃` (off the axis this is
  `u_r e_r + u_z e_z`, the axisymmetric field without swirl);
  `psiField ψ = cylField (∂_zψ) (-ψ/r - ∂_rψ)` is the field with stream function `ψ`;
  `redR ur = ur/r` is the reduced radial profile.
* `vortTheta ur uz = ∂_z u_r - ∂_r u_z` is the `e_θ`-component of `∇×u`, i.e. `ω^θ`;
  `cylOp ψ = -∂_rrψ - ∂_zzψ - (1/r)∂_rψ + ψ/r²` is the elliptic operator `L` of (3dBSL).
  **Sign convention:** the paper's scalar vorticity `ω` in `Lψ = ω` is `-ω^θ = cylOp ψ`.

## What is available (import `Submission.Work.Cyl`)

* smoothness of the polar coordinates on ℝ³: `Work.Cyl.differentiableAt_rho_theta_comp`
  (`F` differentiable at `(ρ x, θ x)`, `radial x > 0` ⟹ `y ↦ F (ρ y) (θ y)` differentiable at `x`),
  `Work.Cyl.differentiableAt_rho_of_radial_pos`, `Work.Cyl.differentiableAt_theta_of_radial_ne`;
* item 1 (transfer, paper line 258): `Work.Cyl.pdR_comp_polar`, `Work.Cyl.pdZ_comp_polar`
  (`∂_r`, `∂_{x₃}` of `F(ρ^α,θ)`), the `α = 0` forms `Work.Cyl.pdR_comp_polar_rho`,
  `Work.Cyl.pdZ_comp_polar_rho`, the identity `Work.Cyl.alpha_mul_pow_mul_pdR`
  (`αR∂_R = ρ∂_ρ`), and the ℝ³ forms `Work.Cyl.fderiv_rho_theta_eR`,
  `Work.Cyl.fderiv_rho_theta_eZ`, `Work.Cyl.fderiv_R_theta_eR`, `Work.Cyl.fderiv_R_theta_eZ`.
* item 2 (no-swirl representation): `Work.Cyl.vorticity_cylField`,
  `Work.Cyl.vorticity_psiField`, `Work.Cyl.vortTheta_psiField` (the elliptic reduction
  `ω^θ = -Lψ`), `Work.Cyl.div_cylField`, `Work.Cyl.div_cylField_eq_zero`,
  `Work.Cyl.div_psiField` (`div u = 0` automatically), `Work.Cyl.differentiableAt_cylField`,
  `Work.Cyl.norm_vorticity_cylField`, `Work.Cyl.norm_vorticity_psiField`, and the nine partial
  derivatives `Work.Cyl.pd_cylField_ij`.
* item 3 (`IsOdd` dictionary): `Work.Cyl.isOdd_iff_reflections` (decomposition of `IsOdd` into the
  three reflection conditions), `Work.Cyl.isOdd_axiField`, `Work.Cyl.isOdd_cylField`
  (`IsOdd u ↔ u_r even in x₃ for r>0 ∧ u_z odd in x₃ for r≥0`),
  `Work.Cyl.oddZ_vortTheta_psiField` (`ψ` odd in x₃ ⟹ `ω^θ` odd in x₃),
  `Work.Cyl.derivParity`, `Work.Cyl.isOdd_psiField_of_oddZ`,
  `Work.Cyl.oddZnn_of_isOdd_psiField`, and the reflection-propagation statements
  `Work.Cyl.reflZ_invariant_of_unique`, `Work.Cyl.isOdd_of_reflZ_invariant`,
  `Work.Cyl.isOdd_solution_of_unique_reflection`.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.Transfer
import Submission.Work.Cyl.Elliptic
import Submission.Work.Cyl.Parity
import Submission.Work.Cyl.isOdd_axiField
import Submission.Work.Cyl.isOdd_cylField
import Submission.Work.Cyl.isOdd_iff_reflections
import Submission.Work.Cyl.isOdd_of_reflZ_invariant
import Submission.Work.Cyl.differentiableAt_rho_theta_comp
import Submission.Work.Cyl.fderiv_rho_theta_eR
import Submission.Work.Cyl.fderiv_rho_theta_eZ
import Submission.Work.Cyl.fderiv_R_theta_eR
import Submission.Work.Cyl.fderiv_R_theta_eZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
