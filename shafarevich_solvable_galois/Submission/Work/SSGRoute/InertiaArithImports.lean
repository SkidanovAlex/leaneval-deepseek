/-
Shim module collecting the imports needed to state the arithmetic lemmas about the inertia
subgroup of a finite place (used only to make `depends_on` work for the delegated lemmas).
-/
import Submission.NK.FrobeniusBridge.Basic
import Submission.NK.ResidueFrob.inertia_of_levels_of_tameData
import Submission.NK.ResidueFrob.mem_inertiaSubgroup_of_fixes_rootsOfUnity
import Submission.NK.ResidueFrob.Main
import Submission.NK.TameStructureDeep.Tame.Unconditional
import Submission.NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed
import Submission.NK.TameStructure.ProCyclic.exists_continuous_surjective_zhat_of_isProCyclic
import Submission.NK.LocalAnabelian.ResidueField.Defs
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
import Submission.NK.LocalTame.All
import Submission.NK.TameData.Definitions
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PTW.Prelude
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
