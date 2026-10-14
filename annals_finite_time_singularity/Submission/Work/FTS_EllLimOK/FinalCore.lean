import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.exists_ellLimOK3_of_closed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- The area's `EllLimOK3` is the lead's `FinalV2.EllLimOK3`, verbatim. -/
theorem Lead_EllLimOK3_iff (α : ℝ) (E : Fn → Fn) :
    EllLimOK3 α E ↔ Work.FTS.FinalV2.EllLimOK3 α E :=
  Iff.rfl


end Work.FTS_EllLimOK
