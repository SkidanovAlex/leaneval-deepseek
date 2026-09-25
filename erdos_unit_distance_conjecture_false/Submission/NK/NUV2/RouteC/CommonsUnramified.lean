import Submission.Commons.RepresentationTheory.GroupCohomology.groupCohomology_subsingleton_of_isCyclic_of_H1_H2
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_open_subgroup_units_tate_trivial_exp
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_ramificationIdx_eq_one
import Submission.Commons.GroupTheory.Cohomology.herbrand_finite_cyclic
import Submission.Commons.GroupTheory.Cohomology.natCard_ker_sub_quotient_range_norm_eq_natCard_ker_norm_quotient_range_sub
import Submission.Commons.FieldTheory.Galois.hilbert90_cyclic
import Submission.Commons.RepresentationTheory.GroupCohomology.groupCohomology_two_int_iso_one_qmodz
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_units_of_cyclic
import Submission.Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso

/-!
# Import wrapper for the Route C (local class formation) development

Everything here is in the `Submission.Commons.*` tree, which is *self-contained* and **must not** be
mixed with `Submission.NK.NumberTheory.NumberField.Completion.H2_units_ringOfIntegers_unramified`
(that file re-declares `Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep`, so the two
trees cannot be imported together; see `HANDOFF.md` §8).  Route C therefore lives in this tree.

It provides the arithmetic inputs of the canonical unramified invariant
`H²(Gal(F_m/F), F_mˣ) ≅ ℤ/m`:
* the `Commons` local representation `adicIntegersUnitsRep` on the units of the ring of integers,
* the surjectivity of the norm on units for an unramified extension
  (`norm_units_surjective_of_ramificationIdx_eq_one`), i.e. `Ĥ⁰(𝒪ˣ) = 0`,
* the `exp`/`log` open subgroup with trivial Tate cohomology
  (`exists_open_subgroup_units_tate_trivial_exp`) and the resulting Herbrand computation,
* Herbrand's lemma for finite cyclic groups, Hilbert 90, and the group-cohomology computations
  `H²(G,ℤ) ≅ H¹(G,ℚ/ℤ)` and `Ĥ⁰(u) ≅ Fˣ ⧸ N`.
-/
