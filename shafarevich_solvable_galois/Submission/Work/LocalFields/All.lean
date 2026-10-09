/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.LocalFields` : local and global field arithmetic for Shafarevich's theorem

Umbrella module importing the whole chapter.  The entry points are

* places and completions : `Work.LocalFields.FinitePrime`, `Work.LocalFields.Completion`,
  `Work.LocalFields.residueFieldOf`, `Work.LocalFields.IsLocalField`,
  `Work.LocalFields.instIsLocalFieldCompletion`, `Work.LocalFields.residueEquiv`;
* decomposition/inertia : `Work.LocalFields.decompositionGroup`,
  `Work.LocalFields.inertiaSubgroup`, `Work.LocalFields.IsUnramifiedAt`,
  `Work.LocalFields.IsSplitAt`, `Work.LocalFields.IsInertAt`;
* ramification/Frobenius : `Work.LocalFields.ramificationExactSequence`,
  `Work.LocalFields.residueFrobenius`, `Work.LocalFields.frobenius`,
  `Work.LocalFields.frobenius_spec`;
* Hensel : `Work.LocalFields.hensel_lift_root`, `Work.LocalFields.hensel_lift_root_residue`,
  `Work.LocalFields.exists_pow_eq_of_one_sub_lt_one`;
* named (unproved) inputs : `Work.LocalFields.DemushkinProPStructure`,
  `Work.LocalFields.HasUnramifiedExtensionOfDegree`,
  `Work.LocalFields.DecompositionGroupIsLocalGaloisGroup`.
-/
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionExtension
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.EmbeddingProblem
import Submission.Work.LocalFields.FundamentalIdentity
import Submission.Work.LocalFields.Hensel
import Submission.Work.LocalFields.Inputs
import Submission.Work.LocalFields.LocalExtension
import Submission.Work.LocalFields.LocalFieldAPI
import Submission.Work.LocalFields.Ramification
import Submission.Work.LocalFields.Residue
import Submission.Work.LocalFields.card_algEquiv_le_card_decompositionGroup
import Submission.Work.LocalFields.card_decompositionGroup
import Submission.Work.LocalFields.card_decompositionGroup_eq_finrank_of_unramified
import Submission.Work.LocalFields.card_decompositionGroup_le_card_algEquiv
import Submission.Work.LocalFields.card_decompositionGroup_mul_ncard
import Submission.Work.LocalFields.card_inertiaSubgroup
import Submission.Work.LocalFields.comap_ringEquiv_uniformSpace
import Submission.Work.LocalFields.completionAut_injective
import Submission.Work.LocalFields.completion_algebraMap_continuous
import Submission.Work.LocalFields.completion_algebraMap_mem_intRing
import Submission.Work.LocalFields.completion_algebra_range_eq
import Submission.Work.LocalFields.completion_galois_equiv_canonical
import Submission.Work.LocalFields.exists_algebra_completion
import Submission.Work.LocalFields.exists_monic_irreducible_reduction
import Submission.Work.LocalFields.exists_pow_eq_of_one_sub_lt_one
import Submission.Work.LocalFields.exists_pow_eq_residueFrobenius
import Submission.Work.LocalFields.finite_ramified_primes
import Submission.Work.LocalFields.finite_ramified_primes_extension
import Submission.Work.LocalFields.finrank_adjoinRoot_lift
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
import Submission.Work.LocalFields.finrank_completion_le_card_decompositionGroup
import Submission.Work.LocalFields.finrank_residueField_eq_one_of_surjective
import Submission.Work.LocalFields.frobenius_generates_of_unramified
import Submission.Work.LocalFields.frobenius_spec
import Submission.Work.LocalFields.hasExtension_completion
import Submission.Work.LocalFields.hasUnramifiedExtensionOfDegree_one
import Submission.Work.LocalFields.henselianLocalRing_intRing
import Submission.Work.LocalFields.irreducible_map_of_irreducible_reduction
import Submission.Work.LocalFields.isAdicComplete_maximalIdeal
import Submission.Work.LocalFields.isEquiv_valued_of_unit_of_exists
import Submission.Work.LocalFields.isUnramifiedAt_iff_isUnramifiedLocalExtension
import Submission.Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one
import Submission.Work.LocalFields.mk_frobenius_eq_frobeniusClass
import Submission.Work.LocalFields.ncard_primesOver_eq_index
import Submission.Work.LocalFields.nonempty_algEquiv_equiv_decompositionGroup
import Submission.Work.LocalFields.nonempty_galois_completion_equiv
import Submission.Work.LocalFields.orderOf_residueFrobenius
import Submission.Work.LocalFields.residueMap_ker
import Submission.Work.LocalFields.residueMap_surjective
import Submission.Work.LocalFields.unramifiedAt_iff_inertia_eq_bot
import Submission.Work.LocalFields.valuation_eq_one_of_val_eq_one
import Submission.Work.LocalFields.valuation_smul_of_mem_stabilizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
