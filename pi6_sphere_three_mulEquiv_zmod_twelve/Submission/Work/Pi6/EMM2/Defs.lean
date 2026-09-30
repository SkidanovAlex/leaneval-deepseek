import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMM2.SSKit
import Submission.Work.Serre.MapPathDefs
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.FGThm.mpathHomotopyEquiv
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.EMFG.kOneComparison
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.SSS.serreFGThreeForTwo
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.gradedComm
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Area EMM2 — common vocabulary and the library modules the forcing arguments need

Everything in `Submission/Work/Pi6/EMM2/` imports this module: it re-exports the workspace lemmas
about the mapping path space (`Work.Serre.mpath`, `mpathQ`, `mpathQ_isSerreFibration`,
`mpathQ_fibreHomeo`, `Work.FGThm.mpathHomotopyEquiv`), about loop spaces of range models
(`Work.Stems.isEMSpaceUpTo_loop'`), about the cohomology of a contractible space
(`Work.Cohomology.contractible`), about duality (`kronH_bijective_field`, `kronH_natural`),
about the `K(ℤ,1)` comparison (`Work.EMFG.kOneComparison`), the finiteness theorem
(`Work.SSS.serreFGThreeForTwo`, `Work.EMFG.emHomologyFG`) and the cup-product toolkit
(`cupNaturalH`, `gradedComm`).
-/

namespace Work.Pi6

noncomputable section

open CategoryTheory CategoryTheory.Limits

end

end Work.Pi6
