/-
Import umbrella for the class-field-theoretic level construction
(`Submission.Work.SSGRoute.CycLevel.levelData_of_localGroup` and its helper lemmas).

It collects the local and global class field theory modules of the workspace that the per-place
Grünwald packaging needs, so that delegated lemmas can be stated against them.
-/
import Mathlib
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.NK.GlobalCFT.Inclusion
import Submission.NeukirchUchida.Local.LocalTransfer
import Submission.NeukirchUchida.Local.PlaceUnder
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.GaloisAction
import Submission.NK.GlobalCFT.NormGroup.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
