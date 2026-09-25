/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Basic
import Submission.NK.GlobalCFTdeep.Inequalities
import Submission.NK.GlobalCFTdeep.CoCore.H1
import Submission.NK.GlobalCFTdeep.CoCore.Cyclic
import Submission.NK.GlobalCFTdeep.CoCore.FundamentalClass
import Submission.NK.GlobalCFTdeep.CoCore.Reciprocity
import Submission.NK.GlobalCFTdeep.Existence
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.CoindHerbrand
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_ind_iff
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_trivial
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_trivial
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_iff_of_finite_quotient
import Submission.NK.GlobalCFTdeep.Herbrand.integralIdeles_le_TIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective
import Submission.NK.GlobalCFTdeep.Herbrand.quot_TIdeles_mulEquiv_ideleClassGroup
import Submission.NK.GlobalCFTdeep.Herbrand.Reduction
import Submission.NK.GlobalCFTdeep.Herbrand.Mul
import Submission.NK.GlobalCFTdeep.Herbrand.FourTwoExact
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_units_of_normIndex
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_units_adicCompletion_of_abelian
import Submission.NK.GlobalCFTdeep.Herbrand.milneFourTwoExact_nonempty
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandQuotient_of_cohomologicalFieldAxiom
import Submission.NK.GlobalCFTdeep.Herbrand.Assembly
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
import Submission.NK.GlobalCFTdeep.Herbrand.LocalUnits
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.NK.GlobalCFTdeep.Herbrand.RepIso
import Submission.NK.GlobalCFTdeep.Herbrand.FiberValue
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_supportedIdeles_of_insert
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_tIdeles_of_finset
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_fiberIdeles_ofInfinite
import Submission.NK.GlobalCFTdeep.Herbrand.FiberAll
import Submission.NK.GlobalCFTdeep.Herbrand.Local
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_eq_hOne_of_finite
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_coind
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_coind
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_mul_of_shortExact
import Submission.NK.GlobalCFTdeep.Corollaries.HasseNorm
import Submission.NK.GlobalCFTdeep.Corollaries.HasseInput
import Submission.NK.GlobalCFTdeep.Audit.cohomologicalFieldAxiom_self
import Submission.NK.GlobalCFTdeep.Audit.herbrandQuotient_self
import Submission.NK.GlobalCFTdeep.Audit.localHerbrand_self
import Submission.NK.GlobalCFTdeep.Audit.index_normClassSubgroup_self
import Submission.NK.GlobalCFTdeep.Audit.Satisfiability
import Submission.NK.GlobalCFTdeep.Herbrand.PeriodicComplex
import Submission.NK.GlobalCFTdeep.Herbrand.PiDefs
import Submission.NK.GlobalCFTdeep.Herbrand.PiCplxDefs
import Submission.NK.GlobalCFTdeep.Herbrand.piCplx_homology_iso
import Submission.NK.GlobalCFTdeep.Herbrand.piModuleCatMk_homology
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_piRep
import Submission.NK.GlobalCFTdeep.Herbrand.tateComplex_piRep_piCplx_iso
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_pi_congr
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_helpers
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_ofFinite
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsDefs
import Submission.NK.GlobalCFTdeep.Herbrand.fiberUnitsRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_fiberUnitsRep
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsLocal
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite
import Submission.NK.GlobalCFTdeep.Herbrand.SupportedIdelesInsert
import Submission.NK.GlobalCFTdeep.Herbrand.UnitIdelesDefs
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_supportedIdelesRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_unitIdelesOutsideRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tIdeles_mul_eq_unitIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_one_unitIdelesOutsideRep
import Submission.NK.GlobalCFTdeep.Herbrand.index_normGroup_completion_eq_finrank
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_algEquiv_completion_eq_finrank
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_decompositionSubgroup_ofInfinite_eq_finrank

/-!
# `NK.GlobalCFTdeep` — the analytic/cohomological core of global class field theory

Umbrella module: `import Submission.NK.GlobalCFTdeep.All` brings in the whole chapter
(namespace `NK.GlobalCFTdeep`), on top of the delivered chapter `Submission/Work/GlobalCFT/`
(namespace `NK.GlobalCFT`), whose idèles, idèle class group, norm map, class formation and
`H⁰`-computation are used throughout and *not* redone.

See `Submission/Work/GlobalCFTdeep/README.md` for the full account: the definitions, the main
results with their hypotheses, and the precise status (proved vs. named classical input) of every
statement.  The axiom audit is `Audit/AxiomCheck.lean` (not imported here, to keep this module
free of `#print` output); `#print axioms` for every main result gives
`{propext, Classical.choice, Quot.sound}`.
-/

/-!
# `NK.GlobalCFTdeep.Shared` — the definitions of the chapter

Aggregator for the *definitions* and the lemmas of the chapter that precede the Milne 2.7/3.1
assembly: the `T`-idèles and `T`-units, the fibres, the local units, the Herbrand toolkit, the
ladder (inequalities, class-formation axioms, reciprocity) and the Herbrand-quotient reductions.
Module `Submission.NK.GlobalCFTdeep.All` = this module plus the final assembly of Milne's
Propositions 2.7 and 3.1 (files `Herbrand/Prop27*.lean`).

This module exists so that the files of the final assembly can import the definitions without
importing `All` (which imports them back).
-/
