import Mathlib.Tactic.MinImports
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzAmgm.Defs
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.FTS.EllipticEst.DzCalc
import Submission.Work.FTS.EllipticEst.DzAmgm.Scratch

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- DECLARATION THINNING: this module was byte-identical (modulo imports) to
-- `Submission.Work.FTS.EllipticEst.DzAmgm.Scratch`, in the same namespace `Work.FTS.EllipticEst.DzAmgm`,
-- so importing both was a duplicate-declaration error.  The names stay available to every
-- consumer of this module through the import above.