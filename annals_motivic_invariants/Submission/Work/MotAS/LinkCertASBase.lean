import Mathlib
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.CensusASOld
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.ChartDefs
import Submission.Work.MotAS.ASRed
import Submission.Work.MotAS.ASEntries
import Submission.Work.MotV.Defs
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.LinkCertASBase` — the import context of `linkCertAS.lean`, without the theorem

`Submission/Work/MotAS/linkCertAS.lean` declares the target certificate `Work.MotAS.linkCertAS`,
but proving it requires importing the census modules (`CensusAS2All`, `censusAS2_class_sAS`, …),
some of which used to import `linkCertAS.lean` itself — an import cycle.

This module carries the *import context* of `linkCertAS.lean` (the definitions of `MotAS.AK`,
`ChartDefs`, `ASEntries`, `MotV.Defs`, …) and nothing else, so that the census modules can import it
instead of `linkCertAS.lean`.  The environment it provides is exactly the one they previously got
transitively from `linkCertAS.lean`; every statement and proof in them is unchanged.
-/

namespace Work.MotAS

end Work.MotAS
