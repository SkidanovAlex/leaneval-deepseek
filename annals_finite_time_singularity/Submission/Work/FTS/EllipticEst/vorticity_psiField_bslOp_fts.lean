import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.cylOp_polar
import Submission.Work.Cyl.vorticity_psiField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The vorticity of a self-similar stream-function field is `bslOp`

For a stream function of the self-similar no-swirl form
`ψ(r,z) = ρ² Ψ(ρ^α,θ)`, `ρ = √(r²+z²)`, `θ = arctan(z/r)`, the delivered curl identity
`Work.Cyl.vorticity_psiField` and the polar reduction `Work.Elliptic.cylOp_polar` compose to

  `vorticity (psiField (ρ² Ψ(ρ^α,θ))) x = -(bslOp α Ψ (ρ x ^ α) (θ x)) • e_θ(x)`.

This is the sign convention recorded in `Submission/Work/FTS/EllipticEst/Defs.lean`:
the `e_θ`-coefficient `Ω` of the vorticity and the source `F` of (PolarBSL) satisfy `F = -Ω`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Real Topology

namespace Work.FTS.EllipticEst

/-! ## Two `C²` calculus helpers

These are the (private) calculus inputs of `Work.Elliptic.cylOp_polar` and of
`Work.Cyl.vorticity_psiField`, reproduced here because both consumers need the *composite*
`C²` statement for `(r,z) ↦ ρ(r,z)² Ψ(ρ(r,z)^α, θ(r,z))` at the point `(radial x, axial x)`. -/

/-- If `Ψ` is `C²` at `(ρ^α, θ)` with `ρ > 0`, then `(p,q) ↦ p² Ψ(p^α, q)` is `C²` at `(ρ,θ)`. -/
private theorem contDiffAt_mul_pow (Ψ : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (ρ ^ α, θ)) :
    ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2 * Ψ (y.1 ^ α) y.2) (ρ, θ) := by
  have hsq : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2) (ρ, θ) := by fun_prop
  have hpow : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ α) (ρ, θ) := by
    have h1 : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1) (ρ, θ) := contDiffAt_fst
    have hr : ContDiffAt ℝ 2 (fun x : ℝ => x ^ α) ρ :=
      Real.contDiffAt_rpow_const (x := ρ) (p := α) (n := 2) (Or.inl (ne_of_gt hρ))
    have h := hr.comp (ρ, θ) h1
    simpa [Function.comp_def] using h
  have hpsi : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => Ψ (y.1 ^ α) y.2) (ρ, θ) := by
    have hpair : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => (y.1 ^ α, y.2)) (ρ, θ) :=
      hpow.prodMk (contDiffAt_snd : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.2) (ρ, θ))
    have h := hΨ.comp (ρ, θ) hpair
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h
  exact hsq.mul hpsi

/-- `(p,q) ↦ ρ(p,q) = √(p²+q²)` is `C²` at every point with `p > 0`. -/
private theorem contDiffAt_rhoP_aux (r z : ℝ) (hr : 0 < r) :
    ContDiffAt ℝ 2 (fun y : ℝ × ℝ => Work.Cyl.rhoP y.1 y.2) (r, z) := by
  have h1 : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2 + y.2 ^ 2) (r, z) := by fun_prop
  have h2 : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) (r, z) :=
    h1.sqrt (by positivity)
  simpa [Work.Cyl.rhoP] using h2

/-- `(p,q) ↦ θ(p,q) = arctan(q/p)` is `C²` at every point with `p > 0`. -/
private theorem contDiffAt_thetaP_aux (r z : ℝ) (hr : 0 < r) :
    ContDiffAt ℝ 2 (fun y : ℝ × ℝ => Work.Cyl.thetaP y.1 y.2) (r, z) := by
  have h1 : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.2 / y.1) (r, z) :=
    contDiffAt_snd.div contDiffAt_fst (by simpa using ne_of_gt hr)
  have h2 := h1.arctan
  simpa [Work.Cyl.thetaP] using h2

/-- The composite `(r,z) ↦ ρ(r,z)² Ψ(ρ(r,z)^α, θ(r,z))` is `C²` at `(r,z)` whenever `r > 0` and
`Ψ` is `C²` at `(ρ(r,z)^α, θ(r,z))`. -/
private theorem contDiffAt_psi_comp (Ψ : ℝ → ℝ → ℝ) (α r z : ℝ) (hr : 0 < r)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (Work.Cyl.rhoP r z ^ α, Work.Cyl.thetaP r z)) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 ^ 2
      * Ψ (Work.Cyl.rhoP p.1 p.2 ^ α) (Work.Cyl.thetaP p.1 p.2)) (r, z) := by
  have hF : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => y.1 ^ 2 * Ψ (y.1 ^ α) y.2)
      (Work.Cyl.rhoP r z, Work.Cyl.thetaP r z) :=
    contDiffAt_mul_pow Ψ α _ _ (Work.Cyl.rhoP_pos hr z) hΨ
  have hmap : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => (Work.Cyl.rhoP y.1 y.2, Work.Cyl.thetaP y.1 y.2))
      (r, z) := (contDiffAt_rhoP_aux r z hr).prodMk (contDiffAt_thetaP_aux r z hr)
  have h := hF.comp (r, z) hmap
  simpa [Function.comp_def, Function.uncurry_apply_pair] using h

/-- At a point off the axis, `ρ(radial x, axial x) = rho x`. -/
private theorem rhoP_radial_axial (x : Work.Cyl.R3) :
    Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
  simp only [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.radial]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ x 0 ^ 2 + x 1 ^ 2)]

/-- At a point off the axis, `θ(radial x, axial x) = theta x`. -/
private theorem thetaP_radial_axial (x : Work.Cyl.R3) :
    Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl

/-- **The `e_θ`-coefficient of the vorticity of a self-similar no-swirl field is `-bslOp`.**

For `ψ(r,z) = ρ²Ψ(ρ^α,θ)` the stream function of the no-swirl field `psiField ψ`, the vorticity
at a point `x` off the axis is `-(bslOp α Ψ (ρ x ^ α) (θ x)) • e_θ(x)`.  This is the composition
of the delivered curl identity `Work.Cyl.vorticity_psiField` with the polar reduction
`Work.Elliptic.cylOp_polar`; it pins the sign convention of the elliptic chapter. -/
theorem vorticity_psiField_bslOp_fts (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hx : 0 < Work.Cyl.radial x)
    (hΨ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2) (Work.Cyl.rho x ^ α, Work.Cyl.theta x)) :
    FiniteTimeSingularity.vorticity
        (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
          * Ψ (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))) x
      = -(Work.Elliptic.bslOp α Ψ (Work.Cyl.rho x ^ α) (Work.Cyl.theta x))
          • Work.Cyl.eTheta x := by
  have hθ := thetaP_radial_axial x
  have hρ := rhoP_radial_axial x
  -- transport the `C²` hypothesis to the polar coordinates of `x`
  have hΨ' : ContDiffAt ℝ 2 (Function.uncurry Ψ)
      (Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) ^ α,
       Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)) := by
    rw [hρ, hθ]
    exact hΨ
  -- the stream function `ψ` is `C²` at `(radial x, axial x)`
  have hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
      (fun r z => Work.Cyl.rhoP r z ^ 2 * Ψ (Work.Cyl.rhoP r z ^ α)
        (Work.Cyl.thetaP r z)) p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    contDiffAt_psi_comp Ψ α (Work.Cyl.radial x) (Work.Cyl.axial x) hx hΨ'
  -- the curl identity and the polar reduction
  rw [Work.Cyl.vorticity_psiField _ x hψ hx,
      Work.Elliptic.cylOp_polar α Ψ (Work.Cyl.radial x) (Work.Cyl.axial x) hx hΨ']
  rw [hρ, hθ]

end Work.FTS.EllipticEst
