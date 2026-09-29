import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.ALift.defs
import Submission.Work.ALift.coef_bound_A
import Submission.Work.CLift.hauptH_tiny
import Submission.Work.CLift.hasDerivAt_U

/-!
# Area ALift — bridge module

Re-exports the orchestrator blueprint `Submission.CDTPlan.InterfacesA2` (which pulls in
`Interfaces`, `InterfacesA`, `InterfacesC`, `InterfacesK`: `HZ`, `ARel`, `LiftData`, `phiA`, `psiA`,
`hauptH`, `PsiAFacts`, `ANumerics`, `OdeContinuation`, `HLiftContA`) together with the local
definitions of area ALift (`Submission/Work/ALift/defs.lean`) and the auxiliary bound
`coef_bound_A`, so that `Submission/Work/ALift/...` lemmas can list a single module in
`depends_on`.
-/
