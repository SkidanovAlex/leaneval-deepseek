/-
# `Work.FTS.Physical.Ident.vorticity_psiField_scaled` — the curl identity at the rescaled stream function

The reconstruction's vorticity is node N7's field

  `physVort α A B g x τ = A(τ)⁻¹ · profile (3α) (g·τ) (ρ(x)^{3α}/B(τ)) (θ(x)) · e_θ(x)`,

i.e. a swirl field whose self-similar variable is `z = ρ(x)^{3α}/B(τ)` — *rescaled* by the clock
`B`.  To identify it with the curl of a stream-function field (`BS ω = ± psiField Ψ`, audit §4 N8
item 4) one needs the curl identity at that rescaled variable, namely

  `vorticity (psiField (ρ²·Φ(ρ^p/B, θ))) x = -(bslOp p Φ (ρ(x)^p/B, θ(x))) • e_θ(x)`,

which is the extension of the **workspace's** delivered identity
`Work.R1G.vorticity_psiField_bslOp` (stated at the unscaled variable `ρ^p`) by the scale covariance
of the elliptic operator, already proved in the tree as `Work.R1G3.bslOp_scale`:

  `bslOp α (fun z θ => Φ (z/c) θ) z θ = bslOp α Φ (z/c) θ`.

Consequences for the identification (with the sign convention of `Work.FTS.Physical.SignConvention`):
the field `psiField (ρ²·Φ(ρ^p/B, θ))` has vorticity `-(bslOp p Φ)·e_θ`, so it is the field of
vorticity `+F(z,θ)·e_θ` exactly when `bslOp p Φ = -F` — i.e. the elliptic law of the dynamic route is
the *negative* of `Work.FTS.Galerkin.EllLaw`'s.  This module records that identity at the rescaled
variable so that the identification can be stated in the self-similar variables.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.R1G.vorticity_psiField_bslOp
import Submission.Work.R1G3.bslOp_scale

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Physical.Ident

/-- **The curl identity at the rescaled stream function.**  For the stream function
`ψ(r,z) = ρ(r,z)²·Φ(ρ(r,z)^p/B, θ(r,z))` — the ansatz of the dynamic rescaling — the vorticity off
the axis is `-(bslOp p Φ (ρ(x)^p/B, θ(x))) • e_θ(x)`. -/
theorem vorticity_psiField_scaled {p B : ℝ} (hB : B ≠ 0) {Φ : ℝ → ℝ → ℝ}
    (x : Work.Cyl.R3) (hx : 0 < Work.Cyl.radial x)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2)
      (Work.Cyl.rho x ^ p / B, Work.Cyl.theta x)) :
    FiniteTimeSingularity.vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2
        * Φ (Work.Cyl.rhoP r z ^ p / B) (Work.Cyl.thetaP r z))) x
      = -(Work.Elliptic.bslOp p Φ (Work.Cyl.rho x ^ p / B) (Work.Cyl.theta x))
          • Work.Cyl.eTheta x := by
  -- the rescaled stream function is `Φ_B(ρ^p)` with `Φ_B(w,θ) = Φ(w/B,θ)`
  have hfun : (fun r z => Work.Cyl.rhoP r z ^ 2 * Φ (Work.Cyl.rhoP r z ^ p / B)
        (Work.Cyl.thetaP r z))
      = fun r z => Work.Cyl.rhoP r z ^ 2
          * (fun w θ' => Φ (w / B) θ') (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z) := rfl
  rw [hfun]
  -- the `C²` hypothesis transported to `Φ_B` at `(ρ(x)^p, θ(x))`
  have hΦB : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (fun w θ' => Φ (w / B) θ') q.1 q.2)
      (Work.Cyl.rho x ^ p, Work.Cyl.theta x) := by
    have hcomp : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1 / B, q.2))
        (Work.Cyl.rho x ^ p, Work.Cyl.theta x) :=
      (contDiffAt_fst.div_const B).prodMk contDiffAt_snd
    exact hΦ.comp (Work.Cyl.rho x ^ p, Work.Cyl.theta x) hcomp
  rw [Work.R1G.vorticity_psiField_bslOp p (fun w θ' => Φ (w / B) θ') x hx hΦB,
    Work.R1G3.bslOp_scale p B hB Φ (Work.Cyl.rho x ^ p) (Work.Cyl.theta x) hΦ]

end Work.FTS.Physical.Ident
