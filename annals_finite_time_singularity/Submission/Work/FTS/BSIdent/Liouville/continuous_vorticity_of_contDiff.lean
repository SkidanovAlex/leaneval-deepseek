import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff`

A `C¹` vector field on `ℝ³` has continuous curl (vorticity).  Indeed

  `vorticity u x = ∑ i, eᵢ × (Du(x) eᵢ)`

is a fixed *continuous* (indeed linear) function of the Fréchet derivative `Du(x)`, and `Du` is
continuous as soon as `u` is `C¹` (`ContDiff.continuous_fderiv`).  So the continuity of
`vorticity u` reduces to the continuity of the three elementary operations: evaluation of a
continuous linear map, the cross product on `Fin 3 → ℝ`, the finite sum, and of the linear
identification `WithLp.toLp 2 : (Fin 3 → ℝ) → ℝ³` — which is exactly the decomposition that
`fun_prop` discharges.

This is the `C^{1,0}` half of the regularity of the vorticity field used by the
Liouville-type/Biot–Savart part of the chapter: it yields `ContinuousOn` statements about
`(x,t) ↦ vorticity (u · t) x` (via `Continuous.continuousOn` and `continuous_apply`).
-/

open FiniteTimeSingularity
open scoped Topology Matrix

namespace Work.FTS.BSIdent.Liouville

/-- **The vorticity of a `C¹` field is continuous.**  `vorticity u x = curl (Du(x))` is a
continuous function of the derivative `Du(x)`, and `fderiv ℝ u` is continuous when `u` is `C¹`. -/
theorem continuous_vorticity_of_contDiff {u : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (hu : ContDiff ℝ 1 u) :
    Continuous (FiniteTimeSingularity.vorticity u) := by
  -- `vorticity u x = ∑ᵢ eᵢ × (Du(x) eᵢ)` is a continuous function of `Du(x)`.
  have hf : Continuous (fun x => fderiv ℝ u x) := hu.continuous_fderiv (by norm_num)
  unfold FiniteTimeSingularity.vorticity
  fun_prop

end Work.FTS.BSIdent.Liouville
