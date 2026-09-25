import Mathlib
import Submission.CFTLib.Interfaces
import Submission.CFTLib.NKProps
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.CFTLib.roquette_bound
import Submission.NK.CFTLib.unramifiedAbelianDegreeLe
import Submission.NK.CFTLib.pClassField_exists
import Submission.NK.CFTLib.pClassFieldArtin_of_fc
import Submission.Work.CFTLib.shafBound_of_fc
import Submission.Work.CFTLib.relShafBound_of_fcA
import Submission.Work.CFTLib.maximalClassCond

/-!
# The CFT quadruple, proved

Glue: the interface Props of `Submission.CFTLib.Interfaces` from the proved library roots
(`NK.CFTLib.*`, ported from the neukirch workspace) and the endgame lemmas of this workspace.
-/

namespace Work.CFTLib

theorem roquetteBound : CFTLib.RoquetteBound := NK.CFTLib.roquette_bound

theorem unramifiedAbelianDegreeLe_proved : CFTLib.UnramifiedAbelianDegreeLe :=
  NK.CFTLib.unramifiedAbelianDegreeLe NK.CFTLib.fundamentalClassElement

theorem pClassFieldArtin_proved : CFTLib.PClassFieldArtin :=
  NK.CFTLib.pClassFieldArtin_of_fc NK.CFTLib.fundamentalClassElement

theorem pClassFieldExists_proved : CFTLib.PClassFieldExists := NK.CFTLib.pClassFieldExists

theorem shafBound_proved : CFTLib.ShafBound :=
  shafBound_of_fc NK.CFTLib.fundamentalClassElement roquetteBound

theorem relShafBound_proved : CFTLib.RelShafBound :=
  relShafBound_of_fcA NK.CFTLib.fundamentalClassElement pClassFieldArtin_proved
    unramifiedAbelianDegreeLe_proved

theorem maximalClassCond_proved : CFTLib.MaximalClassCond :=
  maximalClassCond pClassFieldExists_proved

end Work.CFTLib
