/-
Copyright: work module for the Elgindi finite-time singularity project.

# Cauchy–Schwarz for the iterated integral over the quadrant

Two-stage Cauchy–Schwarz for the iterated `L²` integral over the quadrant
`[0,∞) × [0,π/2]` w.r.t. the measure `dz dθ`: for `L2Mem` functions `U`, `V`,

`∫_z ∫_θ |U·V| ≤ √(L2Sq U) · √(L2Sq V)`.

This is the "product" form of the estimate of `Submission/Work/FTS/H2/T2Easy/L2Mem_prod_le.lean`,
which states the same bound for the integrand `|U| · |V|`; the two integrands agree by
`abs_mul` (`|U z θ * V z θ| = |U z θ| * |V z θ|`).  The two-stage argument itself lives in
that file: Cauchy–Schwarz on each angular slice, then Cauchy–Schwarz (over `Iz`) for the
two slicewise "second moments" `z ↦ ∫_θ U z θ ^ 2`, `z ↦ ∫_θ V z θ ^ 2`, whose integrals
over `Iz` are `L2Sq U` resp. `L2Sq V` by definition.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T2Easy.L2Mem_prod_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T2Easy

/-- Cauchy–Schwarz in the quadrant, in the "product" form: the iterated integral of
`|U·V|` is bounded by the product of the two square roots of `L2Sq`. -/
theorem QuadrantCS {U V : ℝ → ℝ → ℝ} (hU : Work.Spaces.L2Mem U) (hV : Work.Spaces.L2Mem V) :
    ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, |U z θ * V z θ|
      ≤ Real.sqrt (Work.Spaces.L2Sq U) * Real.sqrt (Work.Spaces.L2Sq V) := by
  simpa only [abs_mul] using L2Mem_prod_le hU hV

end Work.FTS.H2.T2Easy
