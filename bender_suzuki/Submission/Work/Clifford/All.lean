import Submission.Work.Clifford.Basic
import Submission.Work.Clifford.CFun
import Submission.Work.Clifford.CharPair
import Submission.Work.Clifford.Classes
import Submission.Work.Clifford.CoherenceBridge
import Submission.Work.Clifford.FunAPI
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.ResSetup
import Submission.Work.Clifford.autChar_mem_Irr
import Submission.Work.Clifford.brauer_permutation_lemma
import Submission.Work.Clifford.card_Irr_eq_card_conjClasses
import Submission.Work.Clifford.card_charOrbit
import Submission.Work.Clifford.card_fixed_Irr_eq_card_fixed_conjClasses
import Submission.Work.Clifford.card_realClasses_eq_one_of_odd
import Submission.Work.Clifford.card_realIrr_eq_card_realClasses
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.cfInner_indFun
import Submission.Work.Clifford.cfInner_indFun_normal
import Submission.Work.Clifford.cfInner_orbitSum_eq_ite
import Submission.Work.Clifford.cfInner_orbitSum_self
import Submission.Work.Clifford.cfInner_resFun_eq_of_smul_orbitSum
import Submission.Work.Clifford.char_mem_Irr_of_isSimpleModule
import Submission.Work.Clifford.character_inv
import Submission.Work.Clifford.charpoly_pow_sub_one_roots
import Submission.Work.Clifford.charpoly_roots_pow_eq_one
import Submission.Work.Clifford.classFun_eq_zero_of_orthogonal
import Submission.Work.Clifford.clifford_constituents
import Submission.Work.Clifford.clifford_correspondence
import Submission.Work.Clifford.clifford_decomposition
import Submission.Work.Clifford.clifford_degree_eq
import Submission.Work.Clifford.clifford_induction_mem_Irr
import Submission.Work.Clifford.conjFun_mem_Irr
import Submission.Work.Clifford.conjSub_isotypicComponent
import Submission.Work.Clifford.coset_sum_char_norm
import Submission.Work.Clifford.eq_top_of_forall_conjSub_le
import Submission.Work.Clifford.exists_aut_of_isPrimitiveRoot_pow
import Submission.Work.Clifford.exists_irr_constituent_resFun
import Submission.Work.Clifford.exists_simple_fdrep_of_submodule
import Submission.Work.Clifford.gallagher
import Submission.Work.Clifford.gallagher_ind_eq
import Submission.Work.Clifford.gallagher_isometry
import Submission.Work.Clifford.gallagher_mul_inflate_irr
import Submission.Work.Clifford.galoisChar_mem_Irr
import Submission.Work.Clifford.galois_char_apply
import Submission.Work.Clifford.inertia_subgroupOf_eq_top
import Submission.Work.Clifford.irr_precomp_mulEquiv
import Submission.Work.Clifford.linearEquiv_of_subChar_eq
import Submission.Work.Clifford.nat_sum_sq_eq_imp_eq
import Submission.Work.Clifford.no_real_Irr_of_odd
import Submission.Work.Clifford.nontrivial_resMod
import Submission.Work.Clifford.powChar_mem_Irr
import Submission.Work.Clifford.principalChar_mem_Irr
import Submission.Work.Clifford.realIrr_eq_principal_of_card_one
import Submission.Work.Clifford.reverse_eq_C_mul_prod_roots_inv
import Submission.Work.Clifford.simple_of_finrank_hom_self_eq_one
import Submission.Work.Clifford.subChar_conjSub
import Submission.Work.Clifford.subChar_isotypicComponent
import Submission.Work.Clifford.sum_G_eq_sum_quotient_mul
import Submission.Work.Clifford.sum_conjFun_eq_card_inertia_smul_orbitSum
import Submission.Work.Clifford.sum_sq_eq_one_of_gram_aux
import Submission.Work.Clifford.trace_map_eq_trace_pow
import Submission.Work.Clifford.trace_mulLeft_comp_mulRight

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford`: Clifford theory, Brauer's permutation lemma, Galois action

Aggregator module for Area A7 of the Feit–Thompson drive; imports every module of
`Submission/Work/Clifford/`.  See `Submission/Work/Clifford/NOTES.md` for the design, the
conventions, and the list of main results.

The vocabulary is in `Submission.Work.Clifford.Basic`; the main results are in the
one-lemma-per-file modules named after the lemma (`character_inv`,
`cfInner_eq_ite_of_mem_Irr`, `classFun_eq_zero_of_orthogonal`, `card_Irr_eq_card_conjClasses`,
`brauer_permutation_lemma`, `cfInner_indFun`, `card_charOrbit`, `clifford_decomposition`,
`clifford_constituents`, `clifford_induction_mem_Irr`, `clifford_correspondence`,
`clifford_degree_eq`, `gallagher`, `card_fixed_Irr_eq_card_fixed_conjClasses`,
`no_real_Irr_of_odd`, `galois_char_apply`, `galoisChar_mem_Irr`, `powChar_mem_Irr`, ...).
-/
