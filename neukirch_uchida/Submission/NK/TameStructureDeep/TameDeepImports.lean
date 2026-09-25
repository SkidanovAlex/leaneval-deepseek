/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Aggregate imports for the `TameDeep` helper lemmas

This module only collects the commons modules used by the `TameDeep` helpers
(`ramificationIdx_data_of_pow_eq`, `inertiaDeg_dvd_of_isPrimitiveRoot`, ...), so that they can be
listed as a single dependency.
-/
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.NK.TameStructureDeep.Tame.isPrimitiveRoot_residue
import Submission.NK.TameStructureDeep.Degree.Equality
import Submission.NK.TameStructureDeep.Degree.orderOf_residueCard_pow_sub_one
import Submission.NK.TameStructureDeep.Degree.unramifiedLevels
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.exists_valuationRing_henselian
import Submission.NK.LocalStructure.Defs
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.Ramification.ramificationSubgroup_map_conj
