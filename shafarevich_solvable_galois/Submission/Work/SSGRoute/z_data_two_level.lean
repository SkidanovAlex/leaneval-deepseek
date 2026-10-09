import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# RETRACTED STATEMENT (session 4): the `p = 2` one-dimensional `z`-data with a confinement level

**This file records a mis-stated lemma** -- the `p = 2` sibling of the statement retracted in
`Submission/Work/SSGRoute/z_data_mup_level.lean`, with the same two extra clauses (confinement at a
level `M`, killing on the conjugates of `T''`).

A prover has shown (`Submission/Work/SSGRoute/z_data_two_level_proof.lean`,
`Work.SSGRoute.z_data_two_level_of_le`, proved and axiom-clean):

* the missing hypothesis is the link `M ≤ Λ` between the level of the confinement clause and the
  auxiliary field, and
* **with `M ≤ Λ` the statement is trivial**: `z := y` extended by `0` off `G_K` witnesses all three
  conjuncts.

Without that hypothesis the statement is false for the same reason as its odd-`p` sibling: `hyunr`
(unramified at places *unramified in `M`*) does not prevent `y` from being ramified at `M`-ramified
places, where the conclusion forbids `z` to be ramified at all, and the Poitou--Tate realisation
criterion then obstructs the local datum of `y` against the Selmer dual.

See `Submission/Work/SSGRoute/z_data_mup_level.lean` for the full record, and
`ZConstruction/ZDataInduction.lean` for the rung `Work.SSGRoute.hasZData_of_le_level` that replaces
the confinement clause by a *change of the auxiliary field* `Λ ↦ Λ·L`.
-/

namespace Work.SSGRoute

end Work.SSGRoute
