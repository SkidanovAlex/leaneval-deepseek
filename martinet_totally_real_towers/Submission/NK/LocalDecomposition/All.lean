/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Submission/Work/LocalDecomposition/` — Neukirch's characterisation of decomposition groups

The chapter attacking the linchpin of the `(a)`-chain of the Neukirch–Uchida development: the "if"
direction of Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (12.1.9) (Neukirch,
*Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*, Invent. Math. **6**
(1969), Theorem 1).

**Import everything with** `import Submission.NK.LocalDecomposition.All`.

Main entry points:

* `NK.LocalDecomposition.localDecompositionCriterion` (`Reduction.lean`) — Neukirch's criterion
  `NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ'` from the four named classical inputs
  `IndecomposedPrime`, `InjectionFiniteIndex`, `LocalGaloisInfinite`, `IndexOneOfSelfNormalizing`;
* `NK.LocalDecomposition.localFinishingStep_iff_indexOne` (`Reduction.lean`) — the finishing step
  of `Submission/Work/LocalStructure/` is *equivalent* to the index-one statement;
* `NK.LocalDecomposition.indexOne_of_localDecompositionCriterion` (`Main.lean`) — conversely, the
  criterion (with the local Brauer nonvanishing input) implies the index-one statement, so the
  reduction is tight;
* `NK.LocalDecomposition.preservesDecompositionGroups_of_localData_two` (`Main.lean`) — the
  `(a)`-chain at `p = 2` from the local data;
* `NK.LocalDecomposition.korollar1Local_iff_localNUExistence` (`Local/Korollar1.lean`) — the local
  reconstruction: Neukirch's Korollar 1 and the local Neukirch–Uchida theorem are equivalent;
* `NK.LocalDecomposition.loc_eq_res` (`Localisation.lean`) — the localisation at a place *is* the
  restriction to the decomposition group (definitionally);
* `NK.LocalDecomposition.le_stabSubgroup_of_openSubgroup_le` (`Basic.lean`) — Ivanov's
  `lm:finindexlm` (the passage from an open subgroup to the whole group), proved from the
  disjointness of decomposition groups of distinct places.

See `README.md` for the full account, the references of the four inputs, and the honest list of what
is not proved here.
-/
import Submission.NK.LocalDecomposition.Defs
import Submission.NK.LocalDecomposition.Basic
import Submission.NK.LocalDecomposition.Reduction
import Submission.NK.LocalDecomposition.Localisation
import Submission.NK.LocalDecomposition.Local.Korollar1
import Submission.NK.LocalDecomposition.Local.Korollar1Global
import Submission.NK.LocalDecomposition.exists_intermediateField_of_finiteIndex_finrank
import Submission.NK.LocalDecomposition.loc_joinAdd
import Submission.NK.LocalDecomposition.joinAdd_laws
import Submission.NK.LocalDecomposition.Main
