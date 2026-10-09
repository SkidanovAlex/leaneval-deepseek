/-
Copyright (c) 2025. All rights reserved.
# Solutions of an embedding problem with abelian kernel: the whole chapter
This module imports the entire `Submission/Work/Properness/` development (see
`Submission/Work/Properness/NOTES.md` for the dictionary with the paper):

* `Defs` — the abstract setting `Setup` (`1 → A → E → Q → 1`, `ρ : H ↠ Q`), the canonical
  conjugation action, the twisted action, the properness predicates, and the named arithmetic
  hypothesis;
* `Torsor` — the set of solutions is a `Z¹(H, A)`-torsor and `H¹(H, A)` classifies it up to
  conjugation by the kernel;
* `Criterion` — the properness criterion of Proposition 11 / step 4 of Theorem 15;
* `ScholzGrunwaldWang` — the conditional Proposition 11 (and the sharp form agreeing with the
  prescribed local maps), for the abstract setting and for an embedding problem over `ℚ`;
* `Example` — `HasLift` does not imply `HasProperLift`;
* `BridgeDefs`, `Bridge` — the dictionary with `Submission.EmbeddingProblem` and
  `Work.AbsoluteGalois` (closure models, `HasSurjectiveLift`, the obstruction calculus).
-/
import Submission.Work.Properness.Bridge
import Submission.Work.Properness.BridgeDefs
import Submission.Work.Properness.Criterion
import Submission.Work.Properness.Defs
import Submission.Work.Properness.Example
import Submission.Work.Properness.ScholzGrunwaldWang
import Submission.Work.Properness.Torsor
import Submission.Work.Properness.cocycleOfLiftFun_eq_of_forall_mulFun
import Submission.Work.Properness.cocycleOfLiftFun_mem_Z1
import Submission.Work.Properness.conjLift_mulFun
import Submission.Work.Properness.exists_lift_mulFun
import Submission.Work.Properness.exists_properLift_agreeing_of_datum
import Submission.Work.Properness.exists_properLift_of_datum
import Submission.Work.Properness.exists_unique_smulLift
import Submission.Work.Properness.hasLift_iff_pullbackCocycle_mem_B2
import Submission.Work.Properness.hasProperLift_of_scholzGrunwaldWang
import Submission.Work.Properness.hasSurjectiveLift_iff_exists_properLift
import Submission.Work.Properness.hasSurjectiveLift_imp_hasProperLift
import Submission.Work.Properness.isProper_iff_map_HK_eq_A
import Submission.Work.Properness.isProper_of_iSup_map_eq
import Submission.Work.Properness.liftClass_eq_iff_exists_conj
import Submission.Work.Properness.mulFun_cocycleOfLiftFun
import Submission.Work.Properness.section_lift_not_isProper
import Submission.Work.Properness.trivialSetup_hasLift
import Submission.Work.Properness.trivialSetup_no_properLift
import Submission.Work.Properness.twist_eq_smul_of_isLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
