/-
# `Work.FTS.LocData.SmoothQuad_Fstar` — `F_*` is `C^∞` on the open quadrant

A one-line restatement of `Work.FTS.LocData.Fstar_smoothQuad` (in `SmoothQuad_locG.lean`), kept
because the interface name `SmoothQuad_Fstar` is the one used in the statements of the chapter.
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.LocData.SmoothQuad_locG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The reference profile `F_*` is `C^∞` on the open quadrant (no hypothesis on `α`). -/
theorem SmoothQuad_Fstar (α : ℝ) : SmoothQuad (Work.Construction.Fstar α) :=
  Fstar_smoothQuad α

end Work.FTS.LocData
