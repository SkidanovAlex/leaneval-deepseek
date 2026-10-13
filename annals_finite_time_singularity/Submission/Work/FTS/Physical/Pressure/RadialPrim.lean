/-
# `Work.FTS.Physical.Pressure.RadialPrim` — the radial primitive of a curl-free field

`radialPrim G x t = ∫ s in 0..1, ⟪G (s • x) t, x⟫` is the explicit primitive of a curl-free field
`G` (the Poincaré lemma for the curl on `ℝ³`), used to produce the pressure of the reconstructed
Euler solution: the vorticity formulation of Euler says that
`G = ∂ₜu + (u·∇)u` is curl-free, and `p = -radialPrim G` is then a pressure.

The definition lives in this low-level module rather than in the umbrella module
`Submission.Work.FTS.Physical.Pressure` (which re-exports it) because the lemma modules
`Submission.Work.FTS.Physical.Pressure.contDiffOn_radialPrim` and
`...hasFDerivAt_radialPrim` state their results in terms of `radialPrim` and are imported by the
umbrella; a definition in the umbrella would therefore create a genuine import cycle
(umbrella → lemma about `radialPrim` → umbrella).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

/-- **The radial primitive** of a curl-free field `G`: `p(x,t) = ∫₀¹ ⟪G(sx,t), x⟫ ds`. -/
noncomputable def radialPrim (G : R3 → ℝ → R3) (x : R3) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, inner ℝ (G (s • x) t) x

end Work.FTS.Physical
