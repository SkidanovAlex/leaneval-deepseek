/-
Copied-from-`Mine/TopSlotTwo` support for `Final/slot20_bound_fts`.

This module is now an **alias** of `Submission.Work.FTS.EllipticEst.Final.Rep.Mine.TopSlotTwo`,
which holds the declarations (the head of `Mine/TopSlotTwo`, up to `Tk_pointwise_le_closed`) that
the original copy carried; the `Mine/ShiftLevelOne` import and the two declarations of
`Mine/TopSlotTwo` that use it stay outside the cone, exactly as before.  Declaring a second copy
here would duplicate the names of `Final.Rep.Mine.TopSlotTwo` (and of `Mine.TopSlotTwo`, whose
`Tk_le_two_terms`/`Tk_le_two_split` this file also used to repeat) in every module whose import
cone contains both trees.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.Final.Rep.Mine.TopSlotTwo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
