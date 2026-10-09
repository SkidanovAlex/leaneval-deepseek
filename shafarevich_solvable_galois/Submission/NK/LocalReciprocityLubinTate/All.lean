import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.FormalGroup
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Division
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isLubinTateSeries_piXAddXq
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isLubinTateCoeff_integers
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree
import Submission.NK.LocalReciprocityLubinTate.LubinTate.card_rootSet_LTpolyIter
import Submission.NK.LocalReciprocityLubinTate.LubinTate.card_rootSet_LTpolyFactor
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTpolyEis_shape
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor
import Submission.NK.LocalReciprocityLubinTate.LubinTate.mem_maximalIdeal_natCast_of_isFrobeniusPower
import Submission.NK.LocalReciprocityLubinTate.LubinTate.DivisionPoints
import Submission.NK.LocalReciprocityLubinTate.LubinTate.TorsionCardinality
import Submission.NK.LocalReciprocityLubinTate.LubinTate.finrank_adjoin_root_LTpolyEis
import Submission.NK.LocalReciprocityLubinTate.LubinTate.norm_root_LTpolyEis
import Submission.NK.LocalReciprocityLubinTate.LubinTate.finiteDimensional_LTLevel
import Submission.NK.LocalReciprocityLubinTate.LubinTate.normal_LTLevel
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isGalois_LTLevel
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ncard_fiber_LTdivisionSet
import Submission.NK.LocalReciprocityLubinTate.LubinTate.finrank_LTLevel_ge
import Submission.NK.LocalReciprocityLubinTate.LubinTate.map_mem_LTdivisionSet_of_algEquiv
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ext_of_eqOn_LTdivisionSet
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isConjRoot_of_isRoot_LTpolyEis
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LevelSimplicity
import Submission.NK.LocalReciprocityLubinTate.LubinTate.finrank_LTLevel_eq_of_isSimple
import Submission.NK.LocalReciprocityLubinTate.LubinTate.card_aut_LTLevel_eq_of_isSimple
import Submission.NK.LocalReciprocityLubinTate.LubinTate.irreducible_LTpolyFactor
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isFrobeniusPower_integers
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Setup
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Step
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Existence
import Submission.NK.LocalReciprocityLubinTate.LubinTate.existsUnique_lubinTate_solution
import Submission.NK.LocalReciprocityLubinTate.LubinTate.existsUnique_lubinTate_groupLaw
import Submission.NK.LocalReciprocityLubinTate.LubinTate.nonempty_lubinTateModule
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers
import Submission.NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits_gen
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.Basic
import Submission.NK.LocalReciprocityLubinTate.Unramified.isGalois_sup_of_commutative
import Submission.NK.Unramified.exists_unramified_level_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.isNonarchimedeanLocalField_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.subring_subset_integer_of_isCompact
import Submission.NK.LocalReciprocityLubinTate.Unramified.adicUnits_eq_higherUnits_zero
import Submission.NK.LocalReciprocityLubinTate.Unramified.unramifiedNormGroup_eq_zpowers_sup
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_pow_residueCard_sub_one_eq_of_mem_higherUnits_one
import Submission.NK.LocalReciprocityLubinTate.Unramified.normGroup_LTLevel_one_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.mem_normGroup_LTLevel_uniformizer
import Submission.NK.LocalReciprocityLubinTate.Unramified.higherUnits_le_normGroup_LTLevel
import Submission.NK.LocalReciprocityLubinTate.Unramified.normGroup_LTLevel_le_higherUnits_sup
import Submission.NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_isUniformizer
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormCorrespondence
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerWithLT
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTowerWithLT_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_normCorrespondence
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_unramifiedSymbol_family
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_nested_unramified_levels
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.existenceTheorem_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.adicResidual
import Submission.NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_towerCover
import Submission.NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_adicCompletion_of_towerCover
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_family
import Submission.NK.LocalReciprocityLubinTate.Audit.normCorrespondence_real_complex
import Submission.NK.LocalReciprocityLubinTate.Audit.normCorrespondence_hypothesis_satisfiable
import Submission.NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_level_one_residueCard_two
import Submission.NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_real
import Submission.NK.LocalReciprocityLubinTate.Audit.hondaReciprocity_padic
import Submission.NK.LocalReciprocityLubinTate.Tower
import Submission.NK.LocalReciprocityLubinTate.Level
import Submission.NK.LocalReciprocityLubinTate.Reciprocity
import Submission.NK.LocalReciprocityLubinTate.Existence
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.LocalReciprocityLubinTate.Audit.isValuativeTopology_padic
import Submission.NK.LocalReciprocityLubinTate.Audit.PadicInstance
import Submission.NK.LocalReciprocityLubinTate.Audit.residueCard_padic
import Submission.NK.LocalReciprocityLubinTate.Audit.lubinTateExistence_real_complex
import Submission.NK.LocalReciprocityLubinTate.Audit.Conventions
import Submission.NK.LocalReciprocityLubinTate.Audit.natCard_quotient_maximalIdeal_pow
import Submission.NK.LocalReciprocityLubinTate.Audit.exists_irreducible_padic
import Submission.NK.LocalReciprocityLubinTate.Audit.LTLevel_padic
import Submission.NK.LocalReciprocityLubinTate.Eval.finite_quotient_valueGroup_of_finiteDimensional
import Submission.NK.LocalReciprocityLubinTate.Eval.nonempty_orderIso_of_finite_quotient
import Submission.NK.LocalReciprocityLubinTate.Eval.nonempty_orderIso_valueGroupZero_of_localField
import Submission.NK.LocalReciprocityLubinTate.Eval.exists_valuation_extension_finite
import Submission.NK.LocalReciprocityLubinTate.Eval.exists_isNonarchimedeanLocalField_intermediateField
import Submission.NK.LocalReciprocityLubinTate.Eval.hondaReciprocity_intermediateField
import Submission.NK.LocalReciprocityLubinTate.Audit.exists_ltLevelIsSimple_padic_two_one
import Submission.NK.LocalReciprocityLubinTate.Eval.ValuationExtension
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionRing
import Submission.NK.LocalReciprocityLubinTate.Eval.isAdicComplete_adjoinRoot
import Submission.NK.LocalReciprocityLubinTate.Eval.ltpolyIter_sub_X_pow_mem_span
import Submission.NK.LocalReciprocityLubinTate.Eval.hasEval_ltTorsionRing
import Submission.NK.LocalReciprocityLubinTate.Eval.evMap_tau
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionInstances
import Submission.NK.LocalReciprocityLubinTate.Eval.continuous_algebraMap_ltTorsionRing
import Submission.NK.LocalReciprocityLubinTate.Eval.actionTau_add
import Submission.NK.LocalReciprocityLubinTate.Eval.actionTau_mul
import Submission.NK.LocalReciprocityLubinTate.Eval.evalTau_subst
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_mem
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_algEquiv
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_one
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_smul2
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_ann
import Submission.NK.LocalReciprocityLubinTate.Eval.law_factorization
import Submission.NK.LocalReciprocityLubinTate.Eval.X_one_dvd_law_sub_X_zero
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_add
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_level
import Submission.NK.LocalReciprocityLubinTate.Eval.evMap_mem_adjoin_singleton
import Submission.NK.LocalReciprocityLubinTate.Eval.natCard_principalUnits_quotient
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_compat
import Submission.NK.LocalReciprocityLubinTate.Eval.law_factorization_lubinTate
import Submission.NK.LocalReciprocityLubinTate.Eval.exists_mem_principalUnits_of_aeval_eq
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTLevel_commutative
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTLevel_commutative
import Submission.NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_autLTLevel_mulEquiv_apply_smulDiv
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_ker_eq
import Submission.NK.LocalReciprocityLubinTate.Unramified.normGroup_map_eq_of_isCyclic
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormInKernel_isCyclic
import Submission.NK.LocalReciprocityLubinTate.Unramified.normGroup_map_eq_of_isCyclic
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormInKernel_isCyclic_adic
import Submission.NK.LocalReciprocityLubinTate.GroupTheory.subgroup_eq_of_forall_map_eq_of_isCyclic_quotient
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormInKernel_cyclic_quotient_criterion
import Submission.NK.LocalReciprocityLubinTate.Audit.isCyclic_gal_LTLevel_padic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/LocalReciprocityLubinTate/` — the Lubin–Tate construction of local class field
theory

**Namespace:** `NK.LocalReciprocityLubinTate`.
**Import everything with:** `import Submission.NK.LocalReciprocityLubinTate.All`.

This is the umbrella file of the chapter.  Its contents:

* `Basic.lean` — the vocabulary: the higher unit filtration `U^n = 1 + 𝔪[F]^n` of a nonarchimedean
  local field (`principalUnits`, `higherUnits`, `residueCard`, `IsUniformizer`), and the
  **Lubin–Tate tower** `LubinTateTower F F' π U q` (the classical output of Lubin–Tate theory,
  phrased by its norm groups);
* `LubinTate/FormalGroup.lean` — the Lubin–Tate formal group law over a commutative ring and its
  `R`-module structure (`CongruentModDegTwo`, `LubinTateFormalGroupLaw`, `LubinTateModule`,
  `LubinTateFormalGroupExists`);
* `LubinTate/EisFactor.lean`, `LubinTate/DivisionPoints.lean`, `LubinTate/TorsionCardinality.lean` —
  the **division points** `Λ_n` of the standard Lubin–Tate group `f(T) = πT + T^q`, the Eisenstein
  factors `f^{[n]}(T) = f^{(n-1)}(T)^{q-1} + π`, the Lubin–Tate levels `K_n = F(Λ_n)` and the
  cardinality theorem `#Λ_n = q^n` (Milne, *CFT*, §I.3); the level fields are Galois of degree at
  least `(q-1)q^{n-1}` and the roots of `f^{[n]}` have degree exactly `(q-1)q^n` and norm `±π`;
* `LubinTate/Series.lean`, `LubinTate/Division.lean` — **the construction of the Lubin–Tate formal
  group** in the algebraic form (Milne, *CFT*, §I.1–§I.3): the Lubin–Tate series
  (`IsLubinTateSeries`, `IsLubinTateCoeff`, `IsFrobeniusResidue`, `IsFrobeniusPower`), the congruence
  vocabulary (`AgreeModDegree`, `CoeffsDivisibleBy`, `IsEndoSeries`), the standard series
  `piXAddXq π q = πX + X^q` and the division polynomials `LTpoly`, `LTpolyFactor`, `LTpolyIter`;
* `Units/*.lean` — the index computations of the higher unit filtration and the cofinality of the
  filtration among the finite-index subgroups;
* `NormIndex/normIndex_adicCompletion.lean` — the **norm index theorem**
  `[Fˣ : N_{L/F} Lˣ] = [L : F]` for `F = 𝔭.adicCompletion K`;
* `Tower.lean` — the **existence theorem** of local class field theory derived from the tower;
* `Level.lean` — the level-wise reciprocity isomorphism and the degrees `[E_{m,n} : F] = (m+1)(q-1)q^n`
  of the Lubin–Tate levels;
* `Reciprocity.lean`, `Existence.lean` — the assembly of the reciprocity datum from the tower, and
  its bundling as `LubinTateExistence`;
* `Target.lean` — the boundary theorem
  `artinReciprocity_adicCompletion : Nonempty (ArtinReciprocity (𝔭.adicCompletion K) (𝔭.adicCompletion K)̄)`;
* `Audit/*.lean` — satisfiability, non-vacuity, universe and arithmetic checks, and the axiom audit.

See `README.md` for the conventions, the reduction chain, the classical residue and the audit.
-/
