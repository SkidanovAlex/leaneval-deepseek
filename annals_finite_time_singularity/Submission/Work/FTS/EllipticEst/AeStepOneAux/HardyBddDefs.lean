/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions for the `σ`-weighted Hardy inequality `HardyBddEta`

This module fixes the two objects that the proof of
`Work.FTS.EllipticEst.AeStepOneAux.HardyBddEta` (the sharp weighted Hardy inequality

  `∫_Iθ f²/sin(2θ)^{2+η} ≤ (1+η)⁻² ∫_Iθ (f')²/sin(2θ)^η + C ∫_Iθ f²/sin(2θ)^η`

for slices given only by the explicit endpoint bounds `|f θ| ≤ C₀ θ`, `|f θ| ≤ C₀ (π/2-θ)`,
`|deriv f θ| ≤ C₀`, i.e. without `C¹`-on-the-closed-interval or integrability hypotheses)
uses:

* `hbA = (1+η)/2`, the sharp constant of the classical power Hardy inequality;
* `hbPrim f`, the flux `G θ = 2·hbA·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` whose total variation gives
  the boundary term of the inequality;
* `hbDeriv f`, the explicit derivative of `hbPrim f`,
  `G' = -4a·sin(2θ)f²s^{-(1+η)} + 4a·cos(2θ)f f' s^{-(1+η)} - 4a(1+η)cos²(2θ)f²s^{-(2+η)}`.

The pointwise identity behind the inequality is `Work.FTS.EllipticEst.H2W.sliceSigmaPointwise`:
writing `a = hbA`, `S = sin(2θ)`, `C = cos(2θ)`, `U = f θ`, `D = deriv f θ`,

  `D² S^{-η} - 4a² U² S^{-(2+η)}
     = (∂_θ(U S^{-a}))² S^{2a-η} + ∂_θ(2a C U² S^{-(1+η)}) + 4a(1-a)U²S^{-η}`,

whose two right-hand summands are nonnegative on `(0, π/2)`; integrating it and using that the
flux `hbPrim f` tends to `0` at both endpoints (which the linear vanishing bounds supply) yields
`(1+η)² ∫ f² sin(2θ)^{-(2+η)} ≤ ∫ (f')² sin(2θ)^{-η}`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeStepOneAux

set_option autoImplicit false

/-- The sharp constant `a = (1+η)/2` of the weighted Hardy inequality. -/
noncomputable def hbA : ℝ := (1 + Work.Spaces.eta) / 2

theorem hbA_pos : 0 < hbA := by
  rw [hbA]
  have := Work.Spaces.eta_pos
  linarith

theorem hbA_nonneg : 0 ≤ hbA := le_of_lt hbA_pos

/-- `2·hbA = 1 + η`. -/
theorem two_hbA : 2 * hbA = 1 + Work.Spaces.eta := by
  rw [hbA]; ring

/-- `4·hbA² = (1+η)²`. -/
theorem four_hbA_sq : 4 * hbA ^ 2 = (1 + Work.Spaces.eta) ^ 2 := by
  rw [hbA]; ring

/-- `4·hbA·(1-a) = (1+η)(1-η)`, nonnegative for `η ≤ 1`. -/
theorem four_hbA_one_sub : 4 * hbA * (1 - hbA) = (1 + Work.Spaces.eta) * (1 - Work.Spaces.eta) := by
  rw [hbA]; ring

theorem four_hbA_one_sub_nonneg : 0 ≤ 4 * hbA * (1 - hbA) := by
  rw [four_hbA_one_sub]
  have h1 : (0 : ℝ) < 1 + Work.Spaces.eta := by have := Work.Spaces.eta_pos; linarith
  have h2 : (0 : ℝ) ≤ 1 - Work.Spaces.eta := by have := Work.Spaces.eta_lt_one; linarith
  positivity

/-- The flux `G θ = 2a·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` of the weighted Hardy inequality. -/
noncomputable def hbPrim (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  2 * hbA * Real.cos (2 * θ) * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- The explicit derivative of the flux `hbPrim`. -/
noncomputable def hbDeriv (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -4 * hbA * Real.sin (2 * θ) * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
  + 4 * hbA * Real.cos (2 * θ) * (f θ) * deriv f θ * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
  - 4 * hbA * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2 * (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- The identity `hbPrim f θ = 2·hbA·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` (definitional). -/
theorem hbPrim_def (f : ℝ → ℝ) (θ : ℝ) :
    hbPrim f θ = 2 * hbA * Real.cos (2 * θ) * (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := rfl

end Work.FTS.EllipticEst.AeStepOneAux
