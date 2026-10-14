import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The slots `D_zⁱD_θ^j` of a curried function, as functions on the quadrant -/

/-- The `(j,i)`-slot `D_z^j D_θ^i u` of `u`, as a function on `ℝ × ℝ`. -/
private def slot (j i : ℕ) (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.mixed j i u p.1 p.2

/-- The `z`-partial derivative of `u`, uncurried. -/
private def pzf (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => Work.Spaces.pz u p.1 p.2

/-- The `θ`-partial derivative of `u`, uncurried. -/
private def pthf (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => Work.Spaces.pth u p.1 p.2

/-- The first jet of `u` as a continuous linear map. -/
private def jet (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun p => clmPair (pzf u p, pthf u p)









/-! ## The theorem -/


end Work.FTS.StrongEps.E5Aux
