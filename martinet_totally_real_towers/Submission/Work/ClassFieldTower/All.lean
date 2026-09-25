import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.hasGenusLevel_witness
import Submission.Work.ClassFieldTower.ProTwo
import Submission.Work.ClassFieldTower.ProTwoWitness
import Submission.Work.ClassFieldTower.Bridge
import Submission.Work.ClassFieldTower.Wall
import Submission.Work.ClassFieldTower.WallShrunk
import Submission.Work.ClassFieldTower.FiniteModelDefs
import Submission.Work.ClassFieldTower.finiteModel_GF
import Submission.Work.ClassFieldTower.RefuteRelationBound
import Submission.Work.ClassFieldTower.DeficiencyInfinite
import Submission.Work.ClassFieldTower.ProPDeficiencyBridge
import Submission.Work.ClassFieldTower.NumericalCertificate
import Submission.Work.ClassFieldTower.TwoDescentDefs
import Submission.Work.ClassFieldTower.exists_ideal_sq_of_unramified
import Submission.Work.ClassFieldTower.kummer_expTwo_iso
import Submission.Work.ClassFieldTower.UnramifiedKummer
import Submission.Work.ClassFieldTower.realizedByUnramifiedExtensions_f2five_of_genusLevel
import Submission.Work.ClassFieldTower.realizedByUnramifiedExtensions_of_mulEquiv
import Submission.Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv
import Submission.Work.ClassFieldTower.residuallyFiniteTwoGroup_f2five
import Submission.Work.ClassFieldTower.unitTwoRank_witness_eq_one
import Submission.Work.ClassFieldTower.differentIdeal_eq_top_of_intermediateField
import Submission.Work.ClassFieldTower.describesMaximalProTwo_second_galoisGroup
import Submission.Work.ClassFieldTower.ProTwoGeneratorRank
import Submission.Work.ClassFieldTower.ResiduallyFiniteGaloisGroup
import Submission.Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified
import Submission.Work.ClassFieldTower.infiniteProTwoExtension_iff_unbounded_unramified
import Submission.Work.ClassFieldTower.unitTwoRank_le_one_iff
import Submission.Work.ClassFieldTower.unitTwoRank_eq_finrank_units_modSquares
import Submission.Work.ClassFieldTower.five_le_card_of_generates_in_finite_quotients
import Submission.Work.ClassFieldTower.hasGenusLevel_certF
import Submission.Work.ClassFieldTower.proTwoShafarevichKochInput_of_no_unramified
import Submission.Work.ClassFieldTower.proTwoShafarevichKochInput_rat
import Submission.Work.ClassFieldTower.Vacuity
import Submission.Work.ClassFieldTower.isPGroup_two_of_residuallyFiniteTwo_of_finite
import Submission.Work.ClassFieldTower.finite_of_bounded_twoQuotients
import Submission.Work.ClassFieldTower.not_hasMinimalPresentation_of_not_finiteDimensional

import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.Tower
import Submission.Work.ClassFieldTower.Api
import Submission.Work.ClassFieldTower.Invariants
import Submission.Work.ClassFieldTower.Main
import Submission.Work.ClassFieldTower.Asymptotic
import Submission.Work.ClassFieldTower.exists_maximalUnramifiedProP
import Submission.Work.ClassFieldTower.differentIdeal_eq_top_of_le_iSup_finite_unramified
import Submission.Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv
import Submission.Work.ClassFieldTower.exists_unramifiedLevel_of_infinite
import Submission.Work.ClassFieldTower.infinite_of_hasMinimalPresentation
import Submission.Work.ClassFieldTower.two_pow_classGroupTwoRank
import Submission.Work.ClassFieldTower.unitTwoRank_eq_one_of_imaginaryQuadratic
import Submission.Work.ClassFieldTower.unitTwoRank_eq_card_infinitePlace
import Submission.Work.ClassFieldTower.shafarevichKochBound_iff_deficiency
import Submission.Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN
import Submission.Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five
import Submission.Work.ClassFieldTower.card_quotient_squareSubgroup_eq_card_twoTorsion
import Submission.Work.ClassFieldTower.exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo
import Submission.Work.ClassFieldTower.GenusRoute
import Submission.Work.ClassFieldTower.Witness
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five

/-!
# `Work.ClassFieldTower.All` -- the whole class-field-tower chapter in one import

`` brings in every module of the chapter
(`Submission/Work/ClassFieldTower/`), namespace `Work.ClassFieldTower`:

* `Defs` -- the objects (`MaximalUnramifiedProP`), the invariants (`classGroupTwoRank`,
  `unitTwoRank`), presentations (`HasMinimalPresentation`), the deficiency bound
  (`ShafarevichKochBound`) and the certificate (`GolodShafarevichCertificate`);
* `Objects` -- API for `F_∅`: `isPGroup_galoisGroup_of_finite`,
  `exists_finite_galois_subfield_finrank_ge`, `infinite_galoisGroup_iff_unbounded_subfields`;
* `Tower` -- `|disc L| = |disc F| ^ [L : F]` and `rootDiscr L = rootDiscr F` for unramified
  extensions, and the tower consequence;
* `Main` -- the Golod--Shafarevich crux and the named arithmetic inputs;
* `Asymptotic` -- the asymptotically good family extracted from the wall;
* `ProTwoDefs`/`ProTwo` -- the SOUND arithmetic interface and the Golod--Shafarevich reduction;
* `ProTwoGenus`/`ProTwoWitness` -- the genus-theoretic generator half and the concrete field;
* `ProTwoGeneratorRank` -- `G_∅ ↠ (𝔽₂)^5` for `Kc`, unconditionally;
* `ResiduallyFiniteGaloisGroup` -- `G_∅` is residually a finite `2`-group, unconditionally;
* `Wall` -- **the single remaining input** (`KcWall`, `KcPresentationWall`) and all its
  consequences, plus the bundled unconditional numerical certificate;
* `hasGenusLevel_certF` -- the genus level of the second explicit certificate field
  `ℚ(√-3556995)` of `Submission/Work/QuadraticFields`, read in this chapter's vocabulary;
* `proTwoShafarevichKochInput_of_no_unramified`, `proTwoShafarevichKochInput_rat` -- the wall's
  interface is CONSISTENT (satisfiable), the positive counterpart of `Vacuity.lean`;
* `Bridge` -- the bridge to the main agent's `UnramifiedPro2TowerWall` / `BoundedRdTowerWall`;
* `WallShrunk` -- the wall SPLIT into its two classical halves: `KcModelData` (pro-`2` finite
  presentability of `G_∅` over a countable model), `KcRelationBound` (THE single classical input:
  the Shafarevich--Koch deficiency bound) and `KcShrunkInput` (a strictly weaker sufficient form,
  with the generator bound derived and the full description direction dropped);
* `FiniteModelDefs`, `finiteModel_GF` -- the explicit finite model
  `GF = FreeGroup (Fin 5) ⧸ normalClosure relF` (`≅ (𝔽₂)^5`), the test group for the refutation
  of the universally quantified deficiency bound;
* `RefuteRelationBound` -- **the universally quantified deficiency bound `KcRelationBound` is
  FALSE** (`not_kcRelationBound`), machine-checked; `kcModelData` shows the "model half" is a
  theorem (satisfied by the finite genus model), so the whole content of the wall is the relation
  count; the structural realization theorem
  `realizedByUnramifiedExtensions_f2five` (all finite `2`-quotients of `(𝔽₂)^5` are realized by
  unramified extensions of `Kc`) is unconditional;
* `DeficiencyInfinite` -- the arithmetic crux in pure group form
  (`infinite_of_deficiency_le_one`, `infinite_of_shafarevichKochBound`);
* `TwoDescentDefs` -- the Kummer classes `Kˣ/(Kˣ)²` (`Sq`, `sqClassesRank`), the first object of
  the elementary two-descent;
* `exists_ideal_sq_of_unramified` -- unramifiedness forces even valuations: if `L/K` is unramified
  and `a ∈ 𝓞 K` has a square root in `L`, then `(a)` is a square of an integral ideal;
* `kummer_expTwo_iso` -- exponent-`2` Kummer theory: for a finite Galois `L/K` with `∀ σ, σ² = 1`
  (char `≠ 2`), `Gal(L/K) ≃* Hom(U, 𝔽₂)` for the subgroup `U ≤ Kˣ/(Kˣ)²` of classes with a square
  root in `L`, and `|Gal(L/K)| = |U|`;
* `UnramifiedKummer` -- the assembly of the two-descent for unramified levels:
  `exists_kummerSubgroup_of_unramified` and `exists_kummerSubgroup_witness`;
* `NumericalCertificate` -- the assignment's consumable form as a theorem:
  `four_mul_le_sq_of_kcPresentationWall`, `four_mul_le_sq_of_kcShrunkInput`,
  `four_mul_le_sq_of_shafarevichKochBound_witness`;
* `ProPDeficiencyBridge` -- the same arithmetic input in the vocabulary of
  `Submission/Work/ProPDeficiency` (`KcProPDeficiencyInput`), with
  `infiniteProTwoExtension_of_proPDeficiencyInput`;
* `unitTwoRank_witness_eq_one` -- `d₂(O_{Kc}^×) = 1` (equality);
* `differentIdeal_eq_top_of_intermediateField` -- a subextension of an unramified extension is
  unramified;
* `describesMaximalProTwo_second_galoisGroup` -- the universal-property half of
  `DescribesMaximalProTwo` for the genuine `G_∅`;
* `realizedByUnramifiedExtensions_of_mulEquiv`, `residuallyFiniteTwoGroup_of_mulEquiv`,
  `residuallyFiniteTwoGroup_f2five` -- isomorphism transport for the interface predicates;
* `Api`, and the delegated lemmas.
-/