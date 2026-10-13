import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.R1G.Defs
import Submission.Work.Elliptic.cylOp_polar
import Submission.Work.Cyl.vorticity_psiField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The vorticity of the self-similar stream-function field, in the elliptic variables

For the stream function `ψ(r,z) = ρ(r,z)² Ψ(ρ(r,z)^p, θ(r,z))` (the polar ansatz (PolarBSL) of
Elgindi's §Setup), the `ℝ³` vorticity of the associated no-swirl field `psiField ψ` is
`-L(Ψ) e_θ`, where `L = bslOp p` is the elliptic operator of the self-similar variables.

This is the composition of the two established halves of the computation:

* `Work.Cyl.vorticity_psiField` : off the axis, `∇ × (psiField ψ) = -(cylOp ψ) e_θ`, where
  `cylOp` is the axisymmetric elliptic operator `-∂_rr - ∂_zz - (1/r)∂_r + 1/r²` of (3dBSL);
* `Work.Elliptic.cylOp_polar` : `cylOp (ρ²Ψ(ρ^p,·)) r z = bslOp p Ψ (ρ^p) (θ)`, the polar change
  of variables (PolarBSL) of the elliptic section.

The only extra ingredient is that the polar ansatz is `C²` at the point `(radial x, axial x)`,
which follows from `ContDiffAt`-stability of `ρ = √(r²+z²)` (away from the origin) and of
`θ = arctan(z/r)` (away from the axis), together with the given regularity of `Ψ` at
`(ρ(x)^p, θ(x))`.

Main statement: `Work.R1G.vorticity_psiField_bslOp`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Real Topology Matrix

namespace Work.R1G

/-! ## The dictionary between `(ρ, θ)` on `ℝ³` and `(rhoP, thetaP)` on the half plane -/

/-- `ρ(x) = rhoP (radial x) (axial x)`: the three-dimensional radius `ρ = √(r²+x₃²)` is the
plane polar radius of the pair `(r, x₃)` of cylindrical coordinates. -/
theorem rhoP_radial_axial (x : R3) :
    Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
  rw [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radial_sq]

/-- `θ(x) = thetaP (radial x) (axial x)`: with our definitions this is `rfl`. -/
theorem thetaP_radial_axial (x : R3) :
    Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl

/-! ## The polar ansatz is `C²` off the axis -/

/-- **The polar stream-function ansatz is `C²` off the axis.**  If `Ψ` is `C²` at
`(ρ(x)^p, θ(x))` and `0 < radial x`, then `(r,z) ↦ ρ(r,z)² Ψ(ρ(r,z)^p, θ(r,z))` is `C²` at
`(radial x, axial x)`.

This is the regularity hypothesis needed to apply the curl identity
`Work.Cyl.vorticity_psiField` to the polar ansatz: near a point with `radial x > 0` the map
`(r,z) ↦ (ρ(r,z), θ(r,z))` is `C²` (the origin is excluded by `ρ ≥ radial x > 0` and the axis by
`radial x > 0`), and the composed function `(a,b) ↦ a² Ψ(a^p, b)` is `C²` at `(ρ x, θ x)`. -/
theorem contDiffAt_rhoP_mul_rpow_comp (p : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΨ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2)
      (Work.Cyl.rho x ^ p, Work.Cyl.theta x)) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2
        * Ψ (Work.Cyl.rhoP q.1 q.2 ^ p) (Work.Cyl.thetaP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
  have hrho : Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x :=
    rhoP_radial_axial x
  have hrhone : Work.Cyl.rho x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hx (Work.Cyl.radial_le_rho x))
  -- the map `(r,z) ↦ (ρ(r,z), θ(r,z))` is `C²` at `(radial x, axial x)`
  have hpair : ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      (Work.Cyl.rhoP q.1 q.2, Work.Cyl.thetaP q.1 q.2))
      (Work.Cyl.radial x, Work.Cyl.axial x) := by
    apply ContDiffAt.prodMk
    · -- `ρ = √(r²+z²)`, and `r²+z² ≠ 0` at the point since `radial x > 0`
      have hsq : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2)
          (Work.Cyl.radial x, Work.Cyl.axial x) := by fun_prop
      have hne : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2)
          (Work.Cyl.radial x, Work.Cyl.axial x) ≠ 0 := by
        have : 0 < Work.Cyl.radial x ^ 2 := pow_pos hx 2
        positivity
      have h := (Real.contDiffAt_sqrt hne).comp
        (Work.Cyl.radial x, Work.Cyl.axial x) hsq
      simpa [Work.Cyl.rhoP, Function.comp_def] using h
    · -- `θ = arctan(z/r)`, with `r ≠ 0` at the point
      have hdiv : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / q.1)
          (Work.Cyl.radial x, Work.Cyl.axial x) :=
        ContDiffAt.div contDiffAt_snd contDiffAt_fst (ne_of_gt hx)
      have h := (Real.contDiff_arctan.contDiffAt).comp
        (Work.Cyl.radial x, Work.Cyl.axial x) hdiv
      simpa [Work.Cyl.thetaP, Function.comp_def] using h
  -- the model function `(a,b) ↦ a² Ψ(a^p, b)` is `C²` at `(ρ x, θ x)`
  have hG : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 * Ψ (q.1 ^ p) q.2)
      (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x),
        Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)) := by
    rw [hrho]
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2)
        (Work.Cyl.rho x, Work.Cyl.theta x) := by fun_prop
    have h2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ (q.1 ^ p) q.2)
        (Work.Cyl.rho x, Work.Cyl.theta x) := by
      have hpr : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ p)
          (Work.Cyl.rho x, Work.Cyl.theta x) :=
        (Real.contDiffAt_rpow_const (x := Work.Cyl.rho x) (n := 2)
          (Or.inl hrhone)).comp (Work.Cyl.rho x, Work.Cyl.theta x) contDiffAt_fst
      have h := hΨ.comp (Work.Cyl.rho x, Work.Cyl.theta x)
        (hpr.prodMk contDiffAt_snd)
      simpa [Function.comp_def, Function.uncurry] using h
    exact h1.mul h2
  -- assemble the composition
  rw [show (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2
        * Ψ (Work.Cyl.rhoP q.1 q.2 ^ p) (Work.Cyl.thetaP q.1 q.2))
      = (fun q : ℝ × ℝ => q.1 ^ 2 * Ψ (q.1 ^ p) q.2) ∘
        (fun q : ℝ × ℝ => (Work.Cyl.rhoP q.1 q.2, Work.Cyl.thetaP q.1 q.2)) from rfl]
  exact hG.comp (Work.Cyl.radial x, Work.Cyl.axial x) hpair

/-! ## The main statement -/

/-- **The vorticity of the polar-ansatz stream-function field, in the elliptic variables.**

For the stream function `ψ(r,z) = ρ(r,z)² Ψ(ρ(r,z)^p, θ(r,z))` of the self-similar variables
`R = ρ^p`, `θ`, the `ℝ³` vorticity of the no-swirl field `u = psiField ψ` is

  `∇ × u = -(LΨ) e_θ`,  `LΨ = bslOp p Ψ (ρ(x)^p) θ(x)`,

i.e. the elliptic operator of (PolarBSL) evaluated at the point `(ρ(x)^p, θ(x))` of the
self-similar half plane.  This is `Work.Cyl.vorticity_psiField` (the curl identity of (3dBSL)) fed
with `Work.Elliptic.cylOp_polar` (the polar change of variables (PolarBSL)); the polar ansatz is
`C²` off the axis by `Work.R1G.contDiffAt_rhoP_mul_rpow_comp`. -/
theorem vorticity_psiField_bslOp (p : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΨ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2)
      (Work.Cyl.rho x ^ p, Work.Cyl.theta x)) :
    FiniteTimeSingularity.vorticity
        (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
          * Ψ (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z))) x
      = -(Work.Elliptic.bslOp p Ψ (Work.Cyl.rho x ^ p) (Work.Cyl.theta x))
          • Work.Cyl.eTheta x := by
  have hρ : Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) ^ p = Work.Cyl.rho x ^ p :=
    congrArg (· ^ p) (rhoP_radial_axial x)
  have hψ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (fun r z => Work.Cyl.rhoP r z ^ 2
        * Ψ (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z)) q.1 q.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    contDiffAt_rhoP_mul_rpow_comp p Ψ x hx hΨ
  have hΨ' : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2)
      (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) ^ p,
        Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)) := by
    rw [hρ, thetaP_radial_axial x]; exact hΨ
  rw [Work.Cyl.vorticity_psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * Ψ (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z)) x hψ hx,
    Work.Elliptic.cylOp_polar p Ψ (Work.Cyl.radial x) (Work.Cyl.axial x) hx hΨ',
    hρ, thetaP_radial_axial x]

end Work.R1G
