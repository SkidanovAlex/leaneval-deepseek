import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Final.Small
import Submission.Work.FTS.RegPkgGal.R7d.support_strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

variable {α Cg C₀ : ℝ} {g Φ : Fam} {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}


end Work.FTS.Final
