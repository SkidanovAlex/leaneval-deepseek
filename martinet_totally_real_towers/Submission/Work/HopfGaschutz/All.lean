import Submission.Work.HopfGaschutz.Defs
import Submission.Work.HopfGaschutz.normalClosure_eq_sup_commutator
import Submission.Work.HopfGaschutz.eq_bot_of_eq_pow_sup_commutator
import Submission.Work.HopfGaschutz.engine_finite_pgroup_defect
import Submission.Work.HopfGaschutz.le_normalClosure_of_le_sup_relFrattini
import Submission.Work.HopfGaschutz.le_normalClosure_of_finite_pgroup_defect
import Submission.Work.HopfGaschutz.relFrattiniDim_le_card_of_normalGenerates
import Submission.Work.HopfGaschutz.h2DimOf_le_card_of_presentation
import Submission.Work.HopfGaschutz.map_mk_le_pPower_sup_commutator
import Submission.Work.HopfGaschutz.natCard_eq_card_map_quotientGroup_mul
import Submission.Work.HopfGaschutz.normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup
import Submission.Work.HopfGaschutz.Counterexample
import Submission.Work.HopfGaschutz.Dictionary
import Submission.Work.HopfGaschutz.Setup
import Submission.Work.HopfGaschutz.isConjInvariant_iff_le_ker
import Submission.Work.HopfGaschutz.finite_quotient_relFrattiniIn
import Submission.Work.HopfGaschutz.finite_and_natCard_le_pow_of_comm_exp_p
import Submission.Work.HopfGaschutz.h2_freeGroup_subsingleton
import Submission.Work.HopfGaschutz.tgClass_surjective
import Submission.Work.HopfGaschutz.tgClass_injective
import Submission.Work.HopfGaschutz.card_conjInvariantZ1
import Submission.Work.HopfGaschutz.le_relFrattini_of_minimal_generating
import Submission.Work.HopfGaschutz.CohomologicalDictionary
import Submission.Work.HopfGaschutz.FiveSix
import Submission.Work.HopfGaschutz.ProP
import Submission.Work.HopfGaschutz.closed_engine
import Submission.Work.HopfGaschutz.closedRelationData_of_spanningModulo
import Submission.Work.HopfGaschutz.ClosedDictionary
import Submission.Work.HopfGaschutz.cochainFactorization
import Submission.Work.HopfGaschutz.Profinite

/-!
# `Work.HopfGaschutz` -- one import for the whole area

```lean
import Submission.Work.HopfGaschutz.All
```

Hopf's formula and the relation-rank dictionary for finite `p`-groups (and as much of the pro-`p`
version as the workspace reaches): the group theory that converts a bound on
`dim_{𝔽_p} H²` into a **presentation**.  See `README.md` in this directory for the full statement of
what is proved, what is assumed, and why.
-/
