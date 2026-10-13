import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-- The comparison function `Φ(θ) = 50 · sin(2θ)^{1-η} / cos(θ)^4`. -/
noncomputable def cwPhi (θ : ℝ) : ℝ :=
  50 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) / (Real.cos θ) ^ (4 : ℕ)

/-- The derivative of `cwPhi` (valid for `θ ∈ (0, π/2)`). -/
noncomputable def cwPhiD (θ : ℝ) : ℝ :=
  50 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * (2 * (1 - Work.Spaces.eta) * Real.cos (2 * θ) + 8 * (Real.sin θ) ^ (2 : ℕ))
      / (Real.cos θ) ^ (4 : ℕ)

/-- The integrand `g(θ) = sin(2θ)^{-η} / cos(θ)^4`. -/
noncomputable def cwG (θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / (Real.cos θ) ^ (4 : ℕ)

/-- The second weight `sin(2θ)^{-η} / cos(θ)^2` appearing on the RHS of the goal. -/
noncomputable def cwB (θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / (Real.cos θ) ^ (2 : ℕ)

end Work.FTS_EllLimOK.PkgJets
