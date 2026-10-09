/-
Shared vocabulary module for the `levelInertiaNormalProEll` development.

This module only collects imports: the definitions used by the delegated lemmas
(`SSGRoute.IsFinPlace`, `Work.SSGRoute.levelPrime`, `ValuationSubring.decompositionSubgroup`,
`ValuationSubring.inertiaSubgroup`, `Ideal.inertia`, `NK.RamificationDeep.UniformizerData`, the
higher-ramification filtration of `NK.Ramification`) come from the modules imported here.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Ramification.All
import Submission.NK.RamificationDeep.WildInertiaUnconditional
import Submission.NK.RamificationDeep.isCyclic_quotient_ramificationSubgroup
import Submission.NK.RamificationDeep.uniformizerData_of_isGalois
import Submission.NK.RamificationDeep.ramificationSubgroup_inf_fixingSubgroup
import Submission.NK.RamificationAudit.Vocab
import Submission.NeukirchUchida.Local.PlaceFromValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise NumberField
