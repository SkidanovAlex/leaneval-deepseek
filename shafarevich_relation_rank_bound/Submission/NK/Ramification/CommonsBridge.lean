/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge to the `Commons` local field arithmetic

This module only re-exports the `Submission.Commons` results about the `p`-adic completions of a
number field at a finite prime that the ramification chapter builds on:

* `Commons.RingTheory.Henselian.adicCompletionMap` and the induced algebra structure
  `Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra`;
* the inertia subgroup of the local Galois group `Gal(L_q/K_Q)` and its order
  (`exists_inertiaSubgroup_adicCompletion`,
  `exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx`);
* the existence of the higher ramification subgroups in the form of an existential statement
  (`exists_ramificationSubgroups_adicCompletion`), which the chapter replaces by an honest
  canonical definition (`NK.Ramification.ramificationSubgroup`);
* the identification of the decomposition subgroup with the whole local Galois group
  (`decompositionSubgroup_adicCompletionIntegers_eq_top`) and the Krull intersection theorem
  (`adicCompletionIntegers_iInf_maximalIdeal_pow_eq_bot`);
* the order of `Gal(L_q/K_Q)` (`natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`).
-/
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_isNormal_card_quotient
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ramificationSubgroups_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_adicCompletionIntegers_eq_top
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionIntegers_iInf_maximalIdeal_pow_eq_bot
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
