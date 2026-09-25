/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Re-export of the `Submission/Commons` modules used by the local Brauer computation

The local Brauer group computation at a `p`-adic field
(`NK.NUV2.ABHN.muColimCard`, and the requested lemma `NK.NUV2.ABHN.localBrauerH2Card`)
consumes the following classical results of local class field theory, all of them *proved*
(sorry-free) under `Submission/Commons/NumberTheory/NumberField/Completion/`:

* `Commons.NumberTheory.NumberField.Completion.exists_galois_realization` — every finite Galois
  extension of a `p`-adic completion of a number field is the completion of a Galois extension of
  number fields;
* `Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion`
  — the local fundamental class: `H²(Gal(L_q/K_Q), L_qˣ)` contains an element of order `[L_q:K_Q]`
  (Milne, *CFT*, III.2);
* `Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable`
  — the upper bound `|H²(Gal(L_q/K_Q), L_qˣ)| ≤ [L_q:K_Q]` for solvable Galois groups;
* `Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian`;
* `Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_adicCompletion_of_isGalois`
  — finiteness of that `H²`, proved through the solvability of the local Galois group (the
  ramification filtration);
* `Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_tower_with_subfield`;
* `Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv`;
* `Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero`;
* `Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units`.

This module is a single home for those imports under `Submission/Work/`.
-/

import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_realization
import Submission.Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
import Submission.Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_adicCompletion_of_isGalois
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_tower_with_subfield
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_eq_card_of_cyclic_arbitrary_base
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
import Submission.NK.HassePrinciple.CoeffTransfer
