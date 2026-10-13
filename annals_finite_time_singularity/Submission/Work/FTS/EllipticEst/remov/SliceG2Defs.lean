/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular weight `σ = sin(2θ)^{2-γ}` of the `∫g²σ` estimate

This module fixes the vocabulary used by `Work.FTS.EllipticEst.remov.slice_G2_le`
(the `∫g²σ`-bound of Elgindi's §H2 slice estimates).  The weight is

  `sigG γ θ = sin(2θ)^{2-γ}`,   `1 ≤ γ ≤ 3/2`,

which vanishes like `θ^{2-γ}` at the two endpoints of `Iθ = [0, π/2]` (note that
`2 - γ ∈ [1/2, 1]`, so the exponent is positive) and is maximal at `θ = π/4`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

/-- The angular weight `σ θ = sin(2θ)^{2-γ}` of the `∫g²σ`-estimate. -/
def sigG (γ : ℝ) : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)

/-- Unfolding lemma (definitional). -/
theorem sigG_eq (γ θ : ℝ) : sigG γ θ = Real.rpow (Real.sin (2 * θ)) (2 - γ) := rfl

end Work.FTS.EllipticEst.remov
