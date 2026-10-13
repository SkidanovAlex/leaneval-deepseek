import Mathlib.Tactic.MinImports
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.H2W.z2pzIter2Comm
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq
import Submission.Work.FTS.EllipticEst.H2W.angL0weak
import Submission.Work.FTS.EllipticEst.H2W.weakSliceDerivBound
import Submission.Work.FTS.EllipticEst.H2W.slot20A

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING (de-duplication of the `Final/Rep` cone).
--
-- Every declaration of this module is the same declaration as the corresponding one of
-- `Submission.Work.FTS.EllipticEst.H2W.slot20A` (the two bodies are byte-identical modulo their `import` lines).
-- Re-declaring them here would be a duplicate declaration in every module whose import
-- cone contains both — and the `Final/Rep` tree lies on the level-`2` path
-- (`Mine.TopSlotTwo`, `Cores.topSlotsTwo`, `TT.slot20_le`).  The names stay available to
-- every consumer of this module, transitively through the import above.
-- The original import list is kept, so nothing that this module used to re-export
-- transitively is lost.
