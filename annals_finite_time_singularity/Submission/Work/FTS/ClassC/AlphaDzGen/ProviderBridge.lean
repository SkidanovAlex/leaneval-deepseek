/-
Bridge: the `EllPkgAux` statement `InterpOpenTraceStmt` is *verbatim* the `K5c` statement
`InterpOpenTrace` (both are the paper's §7 trace-class single-function interpolation), so a
provider of either serves the `ClassC`/`ℛ`-chain (which consumes `K5c.InterpOpenTrace` through
`K5c.i0Family_le_of_interpOpenTrace`).
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllSol.PkgK5.K5c.TraceOpen
import Submission.Work.FTS.EllSol.EllPkgAux.TraceStmt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.AlphaDzGen

theorem openTrace_of_openTraceStmt
    (h : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt C) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.PkgK5.K5c.InterpOpenTrace C := h

theorem openTraceStmt_of_openTrace
    (h : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.PkgK5.K5c.InterpOpenTrace C) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt C := h

end Work.FTS.ClassC.AlphaDzGen
