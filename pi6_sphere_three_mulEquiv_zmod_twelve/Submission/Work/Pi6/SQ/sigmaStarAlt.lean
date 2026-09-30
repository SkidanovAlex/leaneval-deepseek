import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.SQM.SIG.sigmaCup1_3
import Submission.Work.Pi6.SQM.SIG.sigmaCup2_3
import Submission.Work.Pi6.SQM.SIG.sigmaCup3_4
import Submission.Work.Pi6.SQM.SIG.sigmaCup2_4
import Submission.Work.Pi6.SQM.SIG.sigmaCup3_5
import Submission.Work.Pi6.SQM.SIG.sigmaNatural
import Submission.Work.Pi6.SQ.sigmaRangeFinal
import Submission.Work.Pi6.SQ.sigmaLift
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Area SQ: the cohomology suspension `σ*`, assembled in area SQ

The lead's contract `Work.Pi6.SQM.SigmaStar` (naturality (b), the five Steenrod-square
compatibility clauses (c1)–(c5), the Serre range statement (d) and `ℤ/4`-liftability (e)) is
realised by the concrete map `Work.Pi6.SQM.SIG.sigma` (`σ_n = δ⁻¹ ∘ q* ∘ ρ` on the path fibration
`evalOne : PK → K`).  This file assembles it from the five proved clause files in area SQM's `SIG`
together with area SQ's own range (`Work.Pi6.SQ.sigmaRange`) and liftability
(`Work.Pi6.SQ.sigmaLift`) statements — an alternative to `Work.Pi6.SQM.sigmaStar` that avoids the
`ℤ/4` decoration of area SQM's `SIG.sigmaLift`.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.SQ

open CategoryTheory Limits AlgebraicTopology

/-- **The cohomology suspension of the path fibration**, i.e. the contract
`Work.Pi6.SQM.SigmaStar`, assembled from `Work.Pi6.SQM.SIG.sigma` and the seven statements
(b) `sigmaNatural` (SQM/SIG), (c1)–(c5) `sigmaCup*` (SQM/SIG, area SQ's proofs),
(d) `sigmaRange` (SQ) and (e) `sigmaLift` (SQ). -/
theorem sigmaStarAlt (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) (hN : Work.Pi6.SQM.CupINatural) :
    Work.Pi6.SQM.SigmaStar :=
  ⟨fun K _ k₀ n => Work.Pi6.SQM.SIG.sigma K k₀ n,
   Work.Pi6.SQM.SIG.sigmaNatural h1 h2 h3 hN,
   Work.Pi6.SQM.SIG.sigmaCup1_3 h1 h2 h3 hN,
   Work.Pi6.SQM.SIG.sigmaCup3_4 h1 h2 h3 hN,
   Work.Pi6.SQM.SIG.sigmaCup2_3 h1 h2 h3 hN,
   Work.Pi6.SQM.SIG.sigmaCup3_5 h1 h2 h3 hN,
   Work.Pi6.SQM.SIG.sigmaCup2_4 h1 h2 h3 hN,
   Work.Pi6.SQ.sigmaRangeFinal,
   Work.Pi6.SQ.sigmaLift⟩

end Work.Pi6.SQ
