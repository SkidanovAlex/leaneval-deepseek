import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.MainLHSSubN
import Submission.Work.Stability.ModEqn
-- ===== merged: Submission.Work.FTS.EllipticEst.RadialEnergyDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **The truncated radial weight** `W_R z = chi (z/R) · (w z)²`, where `w z = (1+z)²/z²` and
`chi` is the smooth cut-off of `Work.Stability` (`chi = 1` on `[-1,1]`, `chi = 0` off `(-2,2)`).
For `R ≥ 1` this weight equals `w²` on `[0,R]` and vanishes on `[2R,∞)`, and it tends pointwise to
`w²` as `R → ∞`; multiplying the elliptic equation by `Φ · W_R` is the truncation used to justify
the radial integration by parts of the energy inequality. -/
def cutW (R : ℝ) (z : ℝ) : ℝ := Work.Stability.chi (z / R) * (Work.Spaces.w z) ^ 2








end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.Stability.DynGEquation =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability


end Work.Stability
end
