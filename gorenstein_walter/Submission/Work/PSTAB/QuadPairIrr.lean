/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.QuadPairReductions

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# AREA PSTAB — `Work.PSTAB.QuadPairIrr` (RETIRED, not proved)

The subgroup-strength irreducible quadratic-pair lemma `Work.PSTAB.QuadPairIrrProp`
(`∀ Q : Subgroup L, …`) is **not** a target of this area any more.  The design (pass 11 §4, lead's
ruling) keeps `Work.PSTAB.QuadPairIrrSectionProp` — the section-strength form, proved in
`Submission/Work/PSTAB/QuadPairIrrSection.lean` — as the leaf actually consumed by
`Work.PSTAB.StabPerFactorSection` and hence by the deliverable `Work.GW2.pStable`.

The obstruction to the subgroup-strength form is the *subdirect product* step: a single
`D`-composition factor only shows that some `D ⧸ C_D(W)` has `Q₈` as a subgroup, and pulling back
through `C_D(W)` (which need not be a `p`-group) does not give a subgroup of `D`.  The attempted
route through `⨅ᵢ ker (ρ i)` was abandoned; its scaffolding has been retired (see `NOTES.md` §0).

The sorry-free reductions that route was built on are kept in
`Submission.Work.PSTAB.QuadPairReductions` and re-exported here:

* `Work.PSTAB.ne_one_of_rho_ne_one`, `Work.PSTAB.nontrivial_of_rho_ne_one`,
  `Work.PSTAB.top_ne_bot_of_nontrivial`,
* `Work.PSTAB.normal_pSubgroup_apply_eq_one`,
* `Work.PSTAB.pCore_eq_bot`, `Work.PSTAB.notMem_pCore`,
* `Work.PSTAB.subsingleton_of_isPGroup_faithful_irreducible`,
* `Work.PSTAB.exists_pair_not_isPGroup`.
-/

namespace Work.PSTAB

end Work.PSTAB
