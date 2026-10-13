/-
# `Work.CoreResiduals.SelfSimReduction` — the self-similar reduction of the meridian equation

## What this file is for

`VorticityEquation.lean` proves that the `ℝ³` vorticity equation for a swirl vorticity
`W(radial ·, axial ·, t)·eTheta` and a stream-function velocity `psiField (ψ · t)` is equivalent to
the **meridian scalar equation**

  `∂ₜW + (∂_zψ)·∂_rW + (-(ψ/r) - ∂_rψ)·∂_zW = ((∂_zψ)/r)·W`   (`r > 0`),

whose residual is `Work.CoreResiduals.meridianResid` below.

This file defines the **self-similar pair** of a profile `F` and a stream function `Φ` at a
modulation `λ`,

  `W(r,z,t) = λ(t)⁻¹·F(ρ(r,z)^p/λ(t), Θ(r,z))`,   `ψ(r,z,t) = ρ²·λ(t)⁻¹·Φ(ρ(r,z)^p/λ(t), Θ(r,z))`

(`ρ(r,z) = √(r²+z²) = Work.Cyl.rhoP`, `Θ(r,z) = arctan(z/r) = Work.Cyl.thetaP`), and it is the
home of the **chain-rule reduction** that turns the meridian equation into the *profile* equation
of the Construction/Stability areas:

  `meridian equation for (W,ψ)  ⟺  2·(-λ')·(F + D_z F) + UVR p F Φ = 0`  on the open quadrant,

i.e. `DynEqConst p (2·(-λ')) 1 F Φ` — note that the parameter of `UVR` is the *profile exponent* `p`
of the ansatz (`ρ^p`), not the interface's Hölder exponent `α`.  The factor `2` is the `1/2`-dilation bookkeeping audited in
`Model.lean`: the paper's self-similar equation carries the `1/2` on `∂_t` (tex 1319, the announced
"time dilation"), whereas the *delivered* residual R1 is the **physical** equation with coefficient
`1` on `∂_t`; hence the effective rate of the delivered ansatz is `2·(-λ')`, which at the inhabitant
(`λ(t) = 1 - t/2`) equals `1 = κ*`, the reference rate.

## Main statements

* `Work.CoreResiduals.ssVort`, `ssPsi` — the self-similar pair;
* `Work.CoreResiduals.meridianResid` — the residual of the meridian equation;
* `Work.CoreResiduals.MeridianEq` — the meridian equation as a predicate;
* `Work.CoreResiduals.meridianEq_of_dynEqConst` — the reduction (delegated to
  `Submission/Work/CoreResiduals/meridianEq_of_dynEqConst.lean`).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.CoreResiduals.Enstrophy
import Submission.Work.CoreResiduals.VorticityEquation

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-- **The self-similar vorticity profile**
`W(r,z,t) = λ(t)⁻¹·F(ρ(r,z)^p/λ(t), Θ(r,z))`, `ρ = √(r²+z²)`, `Θ = arctan(z/r)`. -/
noncomputable def ssVort (p : ℝ) (lam : ℝ → ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun r z t => (lam t)⁻¹ * F ((Work.Cyl.rhoP r z) ^ p / lam t) (Work.Cyl.thetaP r z)

/-- **The self-similar stream function**.  The paper's self-similar stream function is `Ψ = λ⁻¹Φ`
and the *physical* stream function of the swirl field is `ψ = ρ²Ψ` (`Work.Elliptic`'s convention:
"in the self-similar variables `R = ρ^α`, `θ` with `ψ = ρ²Ψ(R,θ)`").  Hence

  `ψ(r,z,t) = ρ(r,z)²·λ(t)⁻¹·Φ(ρ(r,z)^p/λ(t), Θ(r,z))`. -/
noncomputable def ssPsi (p : ℝ) (lam : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun r z t => (Work.Cyl.rhoP r z) ^ 2 * ((lam t)⁻¹ * Φ
    ((Work.Cyl.rhoP r z) ^ p / lam t) (Work.Cyl.thetaP r z))

/-- **The residual of the meridian scalar equation** at `(r,z,t)`: the left-hand side minus the
right-hand side of
`∂ₜW + (∂_zψ)·∂_rW + (-(ψ/r) - ∂_rψ)·∂_zW = ((∂_zψ)/r)·W`. -/
noncomputable def meridianResid (W ψ : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  deriv (fun s : ℝ => W r z s) t
    + Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z * Work.Cyl.pdR (fun r' z' => W r' z' t) r z
    + (-(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
        * Work.Cyl.pdZ (fun r' z' => W r' z' t) r z
    - (Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z / r) * W r z t

/-- **The meridian scalar equation** for a swirl vorticity profile `W(·,·,t)` and a (possibly
`t`-dependent) stream function `ψ(·,·,t)`: off the axis its residual vanishes.  This is the exact
scalar form of the `ℝ³` vorticity equation for `u = psiField (ψ · t)` and
`ω = W(radial ·, axial ·, t)·eTheta`
(`VorticityEquation.vorticityEquation_psiField_iff_scalar`). -/
def MeridianEq (W ψ : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ r z t : ℝ, 0 < r → meridianResid W ψ r z t = 0
