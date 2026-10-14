import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_setup
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/psiDeriv_layer` — the angular layer bound

The `θ`-analysis of the boundary term `∫_θ σ θ (χ_ε)' θ (U·V)` of `psiDeriv_tendsto_zero`:

`|∫_{(0,π/2)} σ (χ_ε)' Uloc Vloc| ≤ 2 S₁ √(2·(2^η/(1+η))·(π/4)^η) √A
    √(∫_{(0,ε)} σ Vloc² + ∫_{(π/2-ε,π/2)} σ Vloc²)`,

for `0 < ε ≤ π/4`, given the two endpoint bounds `Uloc θ² ≤ (2^η/(1+η)) A θ^{1+η}` and
`Uloc θ² ≤ (2^η/(1+η)) A (π/2-θ)^{1+η}` for the slice `Uloc` and the `σ`-integrability of
`Uloc²`, `Vloc²`.  The ingredients are in `psiDeriv_layer_prep` (which also holds
`sigE_pi_div_two_sub`, `sigE_le_rpow`, `layerLeft_U_bound`, `layerRight_U_bound` and
`layer_cs`); here they are assembled.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)


end Work.FTS.EllipticEst.AeI1Fts
