/-
Copyright: work module for the Elgindi finite-time singularity project.

# The flux vocabulary for the angular slice pair inequality (`slicePairIneqFluxFree`)

For `η : ℝ` this file fixes the weight and the flux expressions used by the proof of

  `∫_{θ∈(0,π/2)} sin(2θ)^{-η} f f''  ≤  2η ∫_{θ∈(0,π/2)} sin(2θ)^{-η} f²`

* `wS η θ = sin(2θ)^{-η}` — the angular weight `σ`;
* `wS1 η θ = -2η cos(2θ) sin(2θ)^{-(1+η)}` — its derivative on `(0,π/2)`;
* `wS2 η θ = 4η sin(2θ)^{-η} + 4η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}` — its second derivative;
* `fluxG η f θ = σ θ · f θ · f' θ − (1/2) σ' θ · f θ²` — the *flux* whose two endpoint
  values are compared by the hypothesis `hflux` of the target (so that the boundary term
  produced by the integration by parts has a sign);
* `fluxGD η f θ` — the derivative of the flux, written out with the explicit second
  derivative `(1/2) σ'' = 2ησ + 2η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}`:
  `fluxGD = σ (f')² + σ f f'' − 2ησ f² − 2η(1+η) cos²(2θ) sin(2θ)^{-(2+η)} f²`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The angular weight `σ η θ = sin(2θ)^{-η}`. -/
def wS (η : ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-η)

/-- The derivative of `wS η` on the open angular interval:
`-2η cos(2θ) sin(2θ)^{-(1+η)}`. -/
def wS1 (η : ℝ) (θ : ℝ) : ℝ :=
  -(2 * η) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))

/-- The second derivative of `wS η` on the open angular interval:
`4η sin(2θ)^{-η} + 4η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def wS2 (η : ℝ) (θ : ℝ) : ℝ :=
  4 * η * (Real.sin (2 * θ)) ^ (-η)
    + 4 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))

/-- The flux `σ · f · f' − (1/2) σ' · f²` of the integration by parts. -/
def fluxG (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  wS η θ * f θ * deriv f θ - (1 / 2) * deriv (wS η) θ * (f θ) ^ 2

/-- The derivative of the flux `fluxG η f`, in the explicit form obtained from
`(1/2) σ'' = 2ησ + 2η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def fluxGD (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  wS η θ * (deriv f θ) ^ 2 + wS η θ * (f θ * deriv (deriv f) θ)
    - 2 * η * wS η θ * (f θ) ^ 2
    - 2 * η * (1 + η) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) * (f θ) ^ 2

end Work.FTS.EllipticEst.AngAWeak
