/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Re-export of the `Submission/Commons` modules used by `Submission/Work/NUV2/ABHN/`

`Submission/Work/NUV2/ABHN/unitsLevelH2_card.lean` (and the lemmas delegated from it) need

* `Commons.NumberTheory.NumberField.Completion.exists_galois_realization` — every finite Galois
  extension of a `p`-adic completion of a number field is the completion of a *Galois* extension
  of number fields,
* `Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion`
  — the local fundamental class: `H²(Gal(L_q/K_Q), L_qˣ)` has an element of order `[L_q : K_Q]`,
* `Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable`
  — the upper bound `|H²(Gal(L_q/K_Q), L_qˣ)| ≤ [L_q : K_Q]` for solvable Galois groups,
* `Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_adicCompletion_of_isGalois`
  — finiteness of that `H²` (and, in particular, the solvability of the local Galois group),

together with the coefficient-ring transfer of `NK.HassePrinciple` and Mathlib's invariance of
group cohomology under restriction along a group isomorphism.

This module exists so that these imports have a single home under `Submission/Work/`.
-/

import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_realization
import Submission.Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable
import Submission.Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_adicCompletion_of_isGalois
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_topAlgEquiv
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
import Submission.NK.HassePrinciple.CoeffTransfer
