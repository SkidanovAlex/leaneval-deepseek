import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- The product rule for the trace of the Jacobian:
`div (ψ • ω) y = ψ y * div ω y + (fderiv ℝ ψ y) (ω y)`.  This is the trace computation that
underlies `div_smul_eq`; it is stated separately because the identification
`fderiv ℝ ψ y (ω y) = ⟪∇ψ y, ω y⟫` is a second, independent step. -/
lemma div_smul_eq_fderiv {ψ : Work.FTS.PressureOn.R3 → ℝ}
    {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3} {y : Work.FTS.PressureOn.R3}
    (hψ : DifferentiableAt ℝ ψ y) (hω : DifferentiableAt ℝ ω y) :
    FiniteTimeSingularity.div (ψ • ω) y
      = ψ y * FiniteTimeSingularity.div ω y + fderiv ℝ ψ y (ω y) := by
  have hsmul := fderiv_smul (𝕜 := ℝ) hψ hω
  rw [FiniteTimeSingularity.div, FiniteTimeSingularity.div, hsmul]
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_smulRight]
  rw [map_add, map_smul, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe]
  ring

theorem div_smul_eq {ψ : Work.FTS.PressureOn.R3 → ℝ} {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3}
    (hψ : DifferentiableAt ℝ ψ y) (hω : DifferentiableAt ℝ ω y) :
    FiniteTimeSingularity.div (ψ • ω) y
      = ψ y * FiniteTimeSingularity.div ω y + inner ℝ (gradient ψ y) (ω y) := by
  rw [div_smul_eq_fderiv hψ hω, inner_gradient_left]

end Work.FTS.PressureOn
