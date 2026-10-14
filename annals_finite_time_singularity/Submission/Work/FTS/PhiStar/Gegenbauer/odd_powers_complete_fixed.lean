import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.sin2_parseval_aesm
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.H2.STDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- The multiplier `h = f / sin(2θ)` of `SpecialTransport`. -/
def hsf (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ / Real.sin (2 * θ)




end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.odd_powers_complete_fixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory
open Polynomial

namespace Work.FTS.PhiStar.Gegenbauer















end Work.FTS.PhiStar.Gegenbauer
end
end
