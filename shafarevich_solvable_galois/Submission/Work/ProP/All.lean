/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.ProP`: umbrella import

The free group of finite rank, its descending `p`-central (Zassenhaus) filtration quotients as
generic kernels, and the pro-`p` completion.  See `Submission/Work/ProP/NOTES.md` for the
statements of every result and for what is *not* proved here.

Use this module to get the whole area (except the optional `G`-operator files, which are listed
separately at the end):

* `Work.ProP.FreePQuotient p n ν = FreeGroup (Fin n) ⧸ F^(n)(ν)` and the pro-`p` completion
  `Work.ProP.proPCompletion p n` (`Defs.lean`, `API.lean`);
* compatibility of the filtration with the lower central series and with surjections
  (`lowerCentralSeries_le_pCentralSeries`, `map_pCentralStep_of_surjective`, `pCentralStep_mono`);
* the Nakayama property and termination of the filtration on finite `p`-groups
  (`pCentralStep_eq_self_iff`, `pCentralSeries_eq_bot_of_card`);
* **cofinality** — the key finiteness input: `pCentralSeries_le_of_pgroup_quotient`,
  `pCentralSeries_le_of_card_dvd`, `exists_pCentralSeries_le_ker`,
  `factors_through_freePQuotient`, `exists_surjective_freePQuotient`,
  `exists_pCentralRefined_le_ker`;
* finiteness and `p`-group structure of the quotients (`finite_freePQuotient`,
  `isPGroup_freePQuotient`, `card_freePQuotient_one`, and the supporting
  `finite_of_fg_of_finite_exponent`, `card_le_pow_of_finset_closure`, `powSubgroup_mul_le`,
  `card_quotient_lt`);
* the universal property of the pro-`p` completion (`proPCompletion_exists_lift_of_le_ker`,
  `proPCompletion_lift_unique_of_factors`, `proPCompletion_exists_lift_canonical`);
* the constructing form of the generic kernel corollary
  (`exists_surjective_freePQuotient_of_generators`) and the transport along a surjection of free
  groups (`exists_freePQuotient_map`);
* the `G`-operator refinement (`exists_freePQuotientAction`,
  `exists_surjective_freePQuotient_equivariant`).
-/

import Submission.Work.ProP.Defs
import Submission.Work.ProP.API
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
import Submission.Work.ProP.map_pCentralStep_of_surjective
import Submission.Work.ProP.pCentralStep_mono
import Submission.Work.ProP.card_quotient_lt
import Submission.Work.ProP.powSubgroup_top_ne_top
import Submission.Work.ProP.pCentralStep_eq_self_iff
import Submission.Work.ProP.abelian_powSubgroup_eq_bot
import Submission.Work.ProP.finite_of_fg_of_finite_exponent
import Submission.Work.ProP.powSubgroup_mul_le
import Submission.Work.ProP.card_le_pow_of_finset_closure
import Submission.Work.ProP.card_freePQuotient_one
import Submission.Work.ProP.finite_freePQuotient
import Submission.Work.ProP.isPGroup_freePQuotient
import Submission.Work.ProP.pCentralSeries_eq_bot_of_card
import Submission.Work.ProP.pCentralSeries_le_of_pgroup_quotient
import Submission.Work.ProP.pCentralSeries_le_of_card_dvd
import Submission.Work.ProP.exists_pCentralSeries_le_ker
import Submission.Work.ProP.factors_through_freePQuotient
import Submission.Work.ProP.exists_surjective_freePQuotient
import Submission.Work.ProP.exists_pCentralRefined_le_ker
import Submission.Work.ProP.proPCompletion_exists_lift_of_le_ker
import Submission.Work.ProP.proPCompletion_lift_unique_of_factors
import Submission.Work.ProP.proPCompletion_exists_lift_canonical
import Submission.Work.ProP.exists_freePQuotientAction
import Submission.Work.ProP.exists_surjective_freePQuotient_equivariant
import Submission.Work.ProP.exists_surjective_freePQuotient_of_generators
import Submission.Work.ProP.exists_freePQuotient_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
