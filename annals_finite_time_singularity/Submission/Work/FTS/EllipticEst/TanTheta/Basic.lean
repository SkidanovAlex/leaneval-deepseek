/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular slice `(0, π/2)` : the variable `ψ = u / cos θ` and the weight `ρ`

This file introduces the two objects used in the slice identity behind the paper's
`I₄` (Elgindi, Annals of Math. 194 (3) 2021, Step 2 of the proof of Proposition `prop:H2`):

* `psi u θ = u θ / Real.cos θ`, the slice variable,
* `wrho η θ = sin θ · cos θ · sin(2θ)^(-η) = (1/2) sin(2θ)^(1-η)`, the integration weight,
  with derivative `wrhoD η θ = (1-η) · cos(2θ) · sin(2θ)^(-η)`.
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

/-- The slice variable `ψ θ = u θ / cos θ`. -/
def psi (u : ℝ → ℝ) : ℝ → ℝ := fun θ => u θ / Real.cos θ

/-- The integration weight `ρ θ = sin θ · cos θ · sin(2θ)^(-η)`, which on `(0, π/2)`
equals `(1/2) · sin(2θ)^(1-η)`. -/
def wrho (η : ℝ) : ℝ → ℝ := fun θ => Real.sin θ * Real.cos θ * (Real.sin (2 * θ)) ^ (-η)

/-- `ρ' θ = (1-η) · cos(2θ) · sin(2θ)^(-η)`, the derivative of `wrho η` on `(0, π/2)`
(note `wrho η θ = (1/2) sin(2θ)^(1-η)` there, and `d/dθ sin(2θ)^(1-η) = 2(1-η)cos(2θ)sin(2θ)^(-η)`). -/
def wrhoD (η : ℝ) : ℝ → ℝ := fun θ => (1 - η) * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-η)

end Work.FTS.EllipticEst.TanTheta
