import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Definitions for the far region of the angular slice estimate (`remov/slice_ang_gen`)

The far region `θ ∈ [3π/8, π/2]` of the one-dimensional angular estimate of Elgindi's
§"General `ℋ^k` case" is handled by the paper's integration by parts, whose combined form is

```
  ∫_a^b [ top-order triple ] · q  =  - ∫_a^b B(θ)·(v^{(k+1)})²·q
                                       + ((k+1)/2)·∫_a^b (cos²θ·q)''·(v^{(k)})²
                                       + D(b) - D(a)
```

with `v = u/cos θ`, `q = sin(2θ)^{2k-γ}`, the room coefficient
`B = ((2k+1-γ)/2)cos2θ + (k+2)sin²θ + (k+1)cos²θ = ((4k+3-γ)/2)cos²θ + ((3+γ)/2)sin²θ ≥ (3+γ)/2 > 0`,
and the flux `D` defined below.  This file only *defines* the objects; the identity itself
(an immediate consequence of the two product-rule identities of `remov/slice_ang_room_ident`,
integrated over `(a,b)`) is `roomFluxIdentity`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The function `v = u / cos θ` of the paper's far-region computation. -/
def vF (u : ℝ → ℝ) : ℝ → ℝ := fun θ => u θ / Real.cos θ

/-- The weight `q = sin(2θ)^{2k-γ}`. -/
def qW (k : ℕ) (γ θ : ℝ) : ℝ := Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)

/-- The room coefficient `B` of the far-region integration by parts. -/
def roomB (k : ℕ) (γ θ : ℝ) : ℝ :=
  ((2 * (k : ℝ) + 1 - γ) / 2) * Real.cos (2 * θ) + ((k : ℝ) + 2) * Real.sin θ ^ 2
    + ((k : ℝ) + 1) * Real.cos θ ^ 2

/-- The top-order triple integrand of the far-region computation. -/
def tripleT (k : ℕ) (γ : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.sin θ * Real.cos θ * iteratedDeriv (k + 1) (vF u) θ * iteratedDeriv (k + 2) (vF u) θ
    - ((k : ℝ) + 2) * Real.sin θ ^ 2 * (iteratedDeriv (k + 1) (vF u) θ) ^ 2
    + ((k : ℝ) + 1) * Real.cos θ ^ 2 * iteratedDeriv k (vF u) θ
        * iteratedDeriv (k + 2) (vF u) θ

/-- The flux `D` of the far-region integration by parts. -/
def fluxT (k : ℕ) (γ : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 / 4) * Real.sin (2 * θ) * qW k γ θ * (iteratedDeriv (k + 1) (vF u) θ) ^ 2
    + ((k : ℝ) + 1) * Real.cos θ ^ 2 * qW k γ θ * iteratedDeriv k (vF u) θ
        * iteratedDeriv (k + 1) (vF u) θ
    - (1 / 2) * ((k : ℝ) + 1) * deriv (fun t => Real.cos t ^ 2 * qW k γ t) θ
        * (iteratedDeriv k (vF u) θ) ^ 2

end Work.FTS.EllipticEst.remov.TopCoreB
