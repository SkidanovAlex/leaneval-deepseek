/-
Auxiliary import module: the common dependencies of the lemmas delegated for
`NK.TameStructureDeep.Tame.pow_class_unramifiedClosure`.

Having a single module that re-exports them lets the delegated lemmas be declared with
`PowClassDeps` in their `depends_on`, so that their statements (which mention
`Commons.RingTheory.Henselian.adicCompletionMap` and the adic-completion API) elaborate.
-/
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.exists_units_mul_uniformizer_zpow_adicCompletion
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.exists_pow_eq_of_pow_card_div_eq_one
import Submission.NK.TameStructureDeep.Tame.ell_mul_pow_sub_one_dvd
