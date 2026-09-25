import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.Cohomology3Map
import Submission.Work.ShafarevichKoch.connecting2
import Submission.Work.ShafarevichKoch.Connecting2Def
import Submission.Work.ShafarevichKoch.exact_H2_C
import Submission.Work.ShafarevichKoch.exact_H3_A
import Submission.Work.ShafarevichKoch.CoeffZ
import Submission.Work.ShafarevichKoch.CountZ
import Submission.Work.ShafarevichKoch.WingbergDefs
import Submission.Work.ShafarevichKoch.KcArithmetic
import Submission.Work.ShafarevichKoch.card_quotient_two_eq_card_twoTorsion
import Submission.Work.ShafarevichKoch.card_twoTorsion_dual_eq_card_twoTorsion
import Submission.Work.ShafarevichKoch.card_twoTorsion_twoPrimaryPart
import Submission.Work.ShafarevichKoch.card_twoMulH2_le_of_wingbergDuality
import Submission.Work.ShafarevichKoch.card_twoTorsionH3_le_of_wingbergDuality
import Submission.Work.ShafarevichKoch.WingbergMain
import Submission.Work.ShafarevichKoch.SquareRoot
import Submission.Work.ShafarevichKoch.FracIdealOfUnit
import Submission.Work.ShafarevichKoch.count_map_eq
import Submission.Work.ShafarevichKoch.exists_sq_eq_of_forall_even_count
import Submission.Work.ShafarevichKoch.exists_integral_mul_square
import Submission.Work.ShafarevichKoch.exists_sq_generator
import Submission.Work.ShafarevichKoch.vClass_eq_mk
import Submission.Work.ShafarevichKoch.vClass_sq_eq_one
import Submission.Work.ShafarevichKoch.vClass_mul
import Submission.Work.ShafarevichKoch.vClass_eq_one_iff
import Submission.Work.ShafarevichKoch.vClass_surjective_twoTorsion
import Submission.Work.ShafarevichKoch.RelationBound
import Submission.Work.ShafarevichKoch.Kc_unit_eq_or_eq_neg
import Submission.Work.ShafarevichKoch.no_sqrt_neg_one_in_maximalUnramified
import Submission.Work.ShafarevichKoch.CardKc
import Submission.Work.ShafarevichKoch.classGroupTwoRank_Kc_le
import Submission.Work.ShafarevichKoch.KcRank
import Submission.Work.ShafarevichKoch.mem_VTwo_of_unramified
import Submission.Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le
import Submission.Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le_classGroupTwoRank
import Submission.Work.ShafarevichKoch.vTwo_rank_two_refutation
import Submission.Work.ShafarevichKoch.vTwo_rank_two_corrected
import Submission.Work.ShafarevichKoch.card_vTwo_mod_squares
import Submission.Work.ShafarevichKoch.infiniteProTwoExtension_of_hasProTwoPresentation
import Submission.Work.ShafarevichKoch.Kc
import Submission.Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented
import Submission.Work.ShafarevichKoch.exists_quotient_of_finite_unramified
import Submission.Work.ShafarevichKoch.isGalois_of_finrank_eq_two
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.twoTorsion_card_sub_one
import Submission.Work.ShafarevichKoch.nonempty_embedding_quadraticLevel_twoTorsion
import Submission.Work.ShafarevichKoch.nonempty_proTwoCharEquiv_option_quadraticLevel
import Submission.Work.ShafarevichKoch.exists_embedding_fin31_quadraticLevel_Kc
import Submission.Work.ShafarevichKoch.GeneratorRankKc
import Submission.Work.ShafarevichKoch.exists_isOpen_index_two_le_of_isClosed
import Submission.Work.ShafarevichKoch.le_of_isOpen_index_two_Kc
import Submission.Work.ShafarevichKoch.exists_generatingSet_card_five_Kc
import Submission.Work.ShafarevichKoch.KummerPairing
import Submission.Work.ShafarevichKoch.exists_kummerChar
import Submission.Work.ShafarevichKoch.towerUnit_fixed_mem_base
import Submission.Work.ShafarevichKoch.exists_kummerChar_of_quadraticLevel
import Submission.Work.ShafarevichKoch.kummerChar_eq_one_iff
import Submission.Work.ShafarevichKoch.Crux
import Submission.Work.ShafarevichKoch.card_le_rel_card_of_finite_abelianization
import Submission.Work.ShafarevichKoch.proTwoShafarevichKochInput_Kc_of_presentation_and_quotients
import Submission.Work.ShafarevichKoch.ProTwoClosed
import Submission.Work.ShafarevichKoch.KcClosedBound
import Submission.Work.ShafarevichKoch.le_normalClosure_sup_relFrattini_of_finiteTwoQuotient
import Submission.Work.ShafarevichKoch.not_relFrattiniAttainment_of_nontrivial_finiteTwoQuotient
import Submission.Work.ShafarevichKoch.card_relFrattiniQuotient_le_of_le_normalClosure_sup
import Submission.Work.ShafarevichKoch.wall_of_kcClosedRelationCount_and_gaschutzDictionary
import Submission.Work.ShafarevichKoch.wall_corollaries
import Submission.Work.ShafarevichKoch.hasProTwoPresentation_of_denseEmbedding
import Submission.Work.ShafarevichKoch.hasProTwoPresentationClosed_mono
import Submission.Work.ShafarevichKoch.frattini_not_determine_normalClosure
import Submission.Work.ShafarevichKoch.frattini_twoGroup_counterexample
import Submission.Work.ShafarevichKoch.neg_one_kummer_slack_Kc
import Submission.Work.ShafarevichKoch.VTwoUnramified
import Submission.Work.ShafarevichKoch.card_VTwoUnramified_mod_squares_Kc
import Submission.Work.ShafarevichKoch.VTwo_eq_VTwoUnramified_sup_neg_one_Kc
import Submission.Work.ShafarevichKoch.unrClassTwoTor_surjective
import Submission.Work.ShafarevichKoch.freeGroup_H2_vanishes
import Submission.Work.ShafarevichKoch.exists_hasProTwoPresentation_of_finite
import Submission.Work.ShafarevichKoch.CohomologyAction
import Submission.Work.ShafarevichKoch.conjKer_mem_cocycles1
import Submission.Work.ShafarevichKoch.conjKer_mem_coboundaries1
import Submission.Work.ShafarevichKoch.KcCohomology
import Submission.Work.ShafarevichKoch.natCard_dual_VTwoQuot_Kc
import Submission.Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection
import Submission.Work.ShafarevichKoch.KcKochInjection
import Submission.Work.ShafarevichKoch.KcRealization
import Submission.Work.ShafarevichKoch.kochInjection_of_contH2DimLe
import Submission.Work.ShafarevichKoch.KochInjectionEquiv
import Submission.Work.ShafarevichKoch.mem_H1Invariants_iff_commutator
import Submission.Work.ShafarevichKoch.H1Invariants_eq_range_H1Res
import Submission.Work.ShafarevichKoch.natCard_H1_le_two_pow_of_normalClosure
import Submission.Work.ShafarevichKoch.natCard_H2_le_two_pow_of_inflation_eq_zero
import Submission.Work.ShafarevichKoch.natCard_ker_H2Res_le_two_pow_of_continuousSection
import Submission.Work.ShafarevichKoch.SupportedTower
import Submission.Work.ShafarevichKoch.SupportedComparison
import Submission.Work.ShafarevichKoch.kSupported_universal
import Submission.Work.ShafarevichKoch.kSupported_isPGroup_and_unramified
import Submission.Work.ShafarevichKoch.kEmptyMaximalProP
import Submission.Work.ShafarevichKoch.SupportedGroupExt
import Submission.Work.ShafarevichKoch.continuous_restrictToEmpty

import Submission.Work.ShafarevichKoch.isOpenMap_restrictToEmpty
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction
import Submission.Work.ShafarevichKoch.natCard_ker_H2Res_le_two_pow
import Submission.Work.ShafarevichKoch.SupportedInfUnramified
import Submission.Work.ShafarevichKoch.SupportedInertia
import Submission.Work.ShafarevichKoch.fixingSubgroup_le_iSup_inertia
import Submission.Work.ShafarevichKoch.SupportedInertiaGeneration
import Submission.Work.ShafarevichKoch.Conj
import Submission.Work.ShafarevichKoch.InertiaCount
import Submission.Work.ShafarevichKoch.natCard_ker_H2Res_le_card_Z1
import Submission.Work.ShafarevichKoch.natCard_contHom_le_of_quotients
import Submission.Work.ShafarevichKoch.natCard_invariantHom_le_of_quotients
import Submission.Work.ShafarevichKoch.finite_primesOver_finset
import Submission.Work.ShafarevichKoch.SupportedSubextensions
import Submission.Work.ShafarevichKoch.SupportedLevel
import Submission.Work.ShafarevichKoch.isCyclic_inertia_of_tame
import Submission.Work.ShafarevichKoch.natCard_ker_H2Res_le_card_invariantHom
import Submission.Work.ShafarevichKoch.ConjBridge
import Submission.Work.ShafarevichKoch.natCard_invariantHom_HSupported_le
import Submission.Work.ShafarevichKoch.KcShrunkBridge
import Submission.Work.ShafarevichKoch.Cohomology3
import Submission.Work.ShafarevichKoch.ItemOneEquality
import Submission.Work.ShafarevichKoch.finite_quadraticLevel
import Submission.Work.ShafarevichKoch.card_quadraticLevel_ge_of_hasGenusLevel
import Submission.Work.ShafarevichKoch.hunits_of_unit_dichotomy
import Submission.Work.ShafarevichKoch.card_quadraticLevel_le_of_unit_dichotomy
import Submission.Work.ShafarevichKoch.exists_sq_or_neg_sq_of_totallyComplex_quadratic
import Submission.Work.ShafarevichKoch.ItemOneGeneral
import Submission.Work.ShafarevichKoch.TorsionCokernel.natCard_quot_two_le_natCard_twoTorsion
import Submission.Work.ShafarevichKoch.RatCoeff
import Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat
import Submission.Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc
import Submission.Work.ShafarevichKoch.UnitHalf.kcProTwoPresentationInput_of_unitDuality
import Submission.Work.ShafarevichKoch.Gaschutz.RelModule
import Submission.Work.ShafarevichKoch.Gaschutz.Kc
import Submission.Work.ShafarevichKoch.Gaschutz.Card
import Submission.Work.ShafarevichKoch.Gaschutz.exists_mulEquiv_pi_zmodTwo_of_natCard_le
import Submission.Work.ShafarevichKoch.Gaschutz.natCard_le_two_pow_of_closure_eq_top
import Submission.Work.ShafarevichKoch.Gaschutz.exists_words_spanning_of_relFrattiniIn_card
import Submission.Work.ShafarevichKoch.Gaschutz.natCard_relFrattiniQuotient_eq_two_pow_of_spanning
import Submission.Work.ShafarevichKoch.Gaschutz.WeakUnitInput
import Submission.Work.ShafarevichKoch.Gaschutz.Cup
import Submission.Work.ShafarevichKoch.Gaschutz.CupTwo
import Submission.Work.ShafarevichKoch.CupInflationRefutation
import Submission.Work.ShafarevichKoch.CruxOneByte.crux_iff_twoTorsionH3_le_two
import Submission.Work.ShafarevichKoch.Bockstein.exists_two_smul_eq
import Submission.Work.ShafarevichKoch.Bockstein.two_smul_eq_zero_iff
import Submission.Work.ShafarevichKoch.Bockstein.SES
import Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H3_rat
import Submission.Work.ShafarevichKoch.Bockstein.twoTorsionH3_natCard_eq_quot_bockstein
import Submission.Work.ShafarevichKoch.RatVanishing.finite_threeCocycle_coboundary_rat
import Submission.Work.ShafarevichKoch.RatVanishing.openNormal_three_slot_invariant
import Submission.Work.ShafarevichKoch.GenusAux
import Submission.Work.ShafarevichKoch.GenusConj
import Submission.Work.ShafarevichKoch.absNorm_conjR
import Submission.Work.ShafarevichKoch.absNorm_span_sc
import Submission.Work.ShafarevichKoch.card_divisors_filter_le
import Submission.Work.ShafarevichKoch.card_twoTorsion_le_32
import Submission.Work.ShafarevichKoch.conjInv_ideal_structure
import Submission.Work.ShafarevichKoch.conjR_mul_self
import Submission.Work.ShafarevichKoch.differentIdeal_eq_top_of_le_kEmpty
import Submission.Work.ShafarevichKoch.eq_one_of_squarefree_mul_sq_eq_sq
import Submission.Work.ShafarevichKoch.exists_coords_even_of_sq_add_sq_mem_four
import Submission.Work.ShafarevichKoch.exists_mk0Span_eq_of_twoTorsion
import Submission.Work.ShafarevichKoch.exists_two_mul_eq_of_mem_ringOfIntegers
import Submission.Work.ShafarevichKoch.freeGroup_twoCocycle_is_coboundary
import Submission.Work.ShafarevichKoch.isCyclic_inertia_of_le_kSupported
import Submission.Work.ShafarevichKoch.lift_le_kEmpty_of_isGalois_differentIdeal_eq_top
import Submission.Work.ShafarevichKoch.minpoly_ringOfIntegers_adjoin_sq_eq_neg_one
import Submission.Work.ShafarevichKoch.nat_eq_of_span_singleton_eq
import Submission.Work.ShafarevichKoch.norm_int_pos
import Submission.Work.ShafarevichKoch.parity_of_four_dvd_sq_add
import Submission.Work.ShafarevichKoch.span_sc_mul_span_sc
import Submission.Work.ShafarevichKoch.span_sc_prod_certPrime_mul_two
import Submission.Work.ShafarevichKoch.span_sc_sq_eq_of_dvd
import Submission.Work.ShafarevichKoch.GaschutzClosedBridge

import Submission.Work.ShafarevichKoch.not_residualTwoFinitenessPresentations_of_card_two

import Submission.Work.ShafarevichKoch.isGalois_sup_kSupported_adjoin_sqrt

import Submission.Work.ShafarevichKoch.sqrtField
import Submission.Work.ShafarevichKoch.sqrtField_kSupported_iff
import Submission.Work.ShafarevichKoch.card_quotient_VTwo_VTwoUnramified_Kc
import Submission.Work.ShafarevichKoch.card_quotient_VTwo_VTwoUnramified_eq_two_pow
import Submission.Work.ShafarevichKoch.VTwoUnramified_eq_of_maximal
import Submission.Work.ShafarevichKoch.sqrtField_ne_kSupported_iff_neg_mem_VTwoUnramified
import Submission.Work.ShafarevichKoch.exists_openNormal_factorization_of_locallyConstant
import Submission.Work.ShafarevichKoch.cochainInflation
import Submission.Work.ShafarevichKoch.zmodTwoInstances
import Submission.Work.ShafarevichKoch.exists_H2Infl_with_kernel
import Submission.Work.ShafarevichKoch.exists_factored_of_mem_H2Infl_kernel
import Submission.Work.ShafarevichKoch.exists_openNormal_H2_lift
import Submission.Work.ShafarevichKoch.ValueTheorem.Basic
import Submission.Work.ShafarevichKoch.ValueTheorem.InflSystem
import Submission.Work.ShafarevichKoch.ValueTheorem.exists_finer_quotient_h2Res_eq_zero
import Submission.Work.ShafarevichKoch.ValueTheorem.LevelFormula

/-!
# `Work.ShafarevichKoch.All` -- the Shafarevich--Koch chapter

One import for the whole area:

```lean
import Submission.Work.ShafarevichKoch.All
```

* `Defs.lean` -- Koch's group `V_∅ = VTwo F`, the induced fractional ideal `FracIdealOf`, and the
  Kummer two-descent class `vClass`.
* `SquareRoot.lean` -- squaring is injective on the group of fractional ideals.
* `Descent.lean` (results in `vClass_*.lean`) -- the exact sequence
  `1 → O_F^×/(O_F^×)² → V_∅/Fˣ² → Cl(F)[2] → 1`: choice-independence of `vClass`
  (`vClass_eq_mk`), `2`-torsion (`vClass_sq_eq_one`), multiplicativity (`vClass_mul`), the kernel
  (`vClass_eq_one_iff`) and surjectivity (`vClass_surjective_twoTorsion`); the exact dimension
  count is `vTwo_rank_two`.
* `count_map_eq`, `exists_sq_eq_of_forall_even_count`, `exists_integral_mul_square`,
  `exists_sq_generator` -- the ramification-theoretic and Kummer-theoretic inputs.
* `mem_VTwo_of_unramified` -- an element whose square root lives in an unramified extension
  generates a square fractional ideal.
* `card_unramifiedQuadraticLevels_le` -- the Kummer upper bound for the number of unramified
  quadratic extensions of `F`: the generator half `d(G_∅) ≤ rank₂ Cl(F) + d₂(O_F^×)` of the
  Shafarevich--Koch identification.
* `RelationBound.lean` -- the classical relation bound, isolated as `HasProTwoPresentation`, with
  `residuallyFiniteTwoGroup_presented` and `exists_quotient_of_finite_unramified` deriving the
  group-theoretic description of the abstract presented group from it.
* `GeneratorRank.lean` -- the definition layer of item (1) of the deliverable: the quadratic levels
  `QuadraticLevel F M` of `F_∅/F` and the continuous character group
  `ProTwoChar F M = H¹(G_∅, 𝔽₂)`.
* `isGalois_of_finrank_eq_two` -- every degree-`2` intermediate field is Galois (characteristic
  zero), so quadratic levels carry a Galois group of order `2`.
* `twoTorsion_card_sub_one` -- `#{c ∈ Cl(F) : c² = 1, c ≠ 1} = 2 ^ rank₂ Cl(F) - 1`, the target
  of the sharpened Kummer embedding.
* `nonempty_embedding_quadraticLevel_twoTorsion` -- the sharpened Kummer two-descent: the
  quadratic levels embed into the *nontrivial* `2`-torsion of the class group.
* `exists_embedding_fin31_quadraticLevel_Kc` -- the matching lower bound: the genus level of `Kc`
  produces `31` distinct quadratic levels.
* `nonempty_proTwoCharEquiv_option_quadraticLevel` -- the infinite Galois correspondence:
  characters correspond to quadratic levels plus the base field.
* `GeneratorRankKc` -- **item (1) of the deliverable**: `Kc` has exactly `31` unramified quadratic
  extensions and `#ProTwoChar Kc M = 2 ^ rank₂ Cl(Kc) = 32`, i.e. `d(G_∅) = rank₂ Cl(Kc) = 5`.
* `exists_generatingSet_card_five_Kc` -- the generator-set form of item (1): `G_∅` is topologically
  generated by `5` elements, and by no fewer.
* `exists_isOpen_index_two_le_of_isClosed` -- the pro-`2` fundamental used for that: every proper
  closed subgroup of `G_∅` lies in an open subgroup of index `2` (equivalently: `G_∅/Φ(G_∅)` is
  detected by the index-`2` subgroups), the profinite form of "every proper subgroup of a finite
  `2`-group has index `2` over it".
* `KummerPairing` -- `kummerPairing_sq`: the Kummer pairing `G_∅ × V_∅ → μ_2` is `μ_2`-valued
  (`σ b = ± b` whenever `b² ∈ F`), the first node of the road towards the relation count.
* `exists_kummerChar` -- the Kummer pairing packaged as a continuous character of `G_∅` with
  **kernel exactly** the stabiliser of `b`, i.e. `x ↦ χ_x ∈ H¹(G_∅,𝔽₂)` for `x` with `√x ∈ F_∅`.
* `exists_kummerChar_of_quadraticLevel` -- step (3) of the road: every unramified quadratic level
  `L` is `F(√x)` for a `V_∅`-class `x` and is cut out by the Kummer character of `√x` (kernel = the
  stabiliser of the square root), i.e. the quadratic levels are parameterised by Kummer characters.
* `towerUnit_fixed_mem_base` -- step (1) of the road: a `G_∅`-fixed unit of the integral closure
  `O_{F_∅} = integralClosure (𝓞 F) M.K` is the image of a unit of `𝓞 F`; i.e.
  `Ĥ⁰(G_∅, E_∅) = (𝓞 F)ˣ`.
* `kummerChar_eq_one_iff` -- the Kummer character is pointwise trivial exactly on the square classes:
  the Kummer map `V_∅/Fˣ² → H¹(G_∅,𝔽₂)` has trivial kernel, so `dim H¹(G_∅,𝔽₂)` is the number of
  independent unramified quadratic levels.
* `card_le_rel_card_of_finite_abelianization` -- the *lower* half `0 ≤ df` of the classical
  Shafarevich inequality, in the general form "the deficiency of a finitely generated group is at
  most the rank of its abelianization": any presentation `⟨α | rel⟩` of a group with finite
  abelianization satisfies `Fintype.card α ≤ rel.card`.  Generalises
  `Work.ProPDeficiency.card_le_rel_card_of_finite`; it is the pro-`2` lower half `0 ≤ df(G_∅)` of
  the Shafarevich bound.  (It does *not* apply to the dense-subgroup presentation of
  `HasProTwoPresentation`, whose presented group may have infinite abelianization: see README
  §9.3.)
* `ProTwoClosed.lean` -- the **closed (pro-`2`) form** `HasProTwoPresentationClosed` of the relation
  bound (the form in which the classical theorems of Koch/Salle/Wingberg are stated), the bridge
  `ker_eq_normalClosure_of_closed`, and the theorem that the closed form and the abstract form are
  **equivalent** (`hasProTwoPresentation_iff_closed`) once the presented group is residually a
  finite `2`-group -- so the workspace's interface is not artificially stronger than the classical
  theorem.  Consequences in both forms for `Kc` (`kcProTwoPresentationInput_iff_closed`,
  `infiniteProTwoExtension_Kc_of_closed`, `unramifiedPro2TowerWall_of_closed`,
  `boundedRdTowerWall_of_closed`).
* `hasProTwoPresentation_of_denseEmbedding` -- the interface through which a *constructive*
  presentation lands: an abstract group with a `d`-generator/`r`-relator presentation and an
  injective dense homomorphism into `G_∅` gives `HasProTwoPresentation F d r`.
* `frattini_not_determine_normalClosure` -- the machine-checked **refutation** of the tempting
  shortcut "it suffices to exhibit the relations modulo `[ker,F]·ker²`" in the abstract setting:
  in `ℤ` the subgroup `2ℤ` is `6ℤ ⊔ [2ℤ,ℤ] ⊔ (2ℤ)²` but is not `6ℤ`.  The Frattini/Nakayama
  argument needs the acting group to be a pro-`2` group (see README §9.2).
* `frattini_twoGroup_counterexample` -- the sharpened form: there is a **nontrivial normal
  `2`-subgroup** `R` (the Klein four group inside `S₄`) with `R ≤ [R,⊤]·R²`, so the failure is not
  caused by odd torsion in `R/H` but by the ambient group not being pro-`2` (README §9.2).
* `VTwoUnramified.lean` -- the **unramified** Kummer radical
  `V^{unr} = {x : √x ∈ F_∅} ≤ V_∅= VTwo`, with `VTwoUnramified_le_VTwo` (unramified implies the
  square ideal), `sq_mem_VTwoUnramified` (so `(Fˣ)² ≤ V^{unr}`) and
  `neg_one_not_mem_VTwoUnramified_Kc` (`-1 ∉ V^{unr}` for `Kc`).  The *slack* of the relation bound
  -- `dim V_∅/Kc^{×2} - dim V^{unr}/Kc^{×2} = 6 - 5 = 1` -- is exactly this single unit class;
  see README §9.4.
* `exists_hasProTwoPresentation_of_finite` -- the interface's **finite case**: if `G_∅` is finite
  then `∃ d r, HasProTwoPresentation F d r`.  Together with the finite-`2`-group Golod--Shafarevich
  inequality this shows that the *numerical* clause `rel.card ≤ rank₂ Cl + d₂(O^×)` of the
  interface can only hold for infinite `G_∅`, i.e. no numerical information about `Kc` alone can
  force `r ≤ 6` (README §9.9).
* `CohomologyAction.lean` -- the group-theoretic core of the **Hochschild--Serre five-term
  sequence**: `conjKer π g n` (conjugation `g n g⁻¹` inside `ker π`), its API, and the conjugation
  action `conjAction π : G →* MulAut (ker π)`.  Shared infrastructure for this chapter's relation
  count, the sibling tame route, and the Gaschütz dictionary `r = dim H²`.  The associated action on `H¹(ker π, A)` is
  `conjKer_mem_cocycles1` / `conjKer_mem_coboundaries1`: the conjugation `g·f := (n ↦ A.ρ g (f (g⁻¹ng)))`
  preserves 1-cocycles and 1-coboundaries, i.e. descends to the cohomology.  (The transgression
  `H¹(N,A)^Q → H²(Q,A^N)` is the next step.)
* `freeGroup_H2_vanishes` -- **`H^i(FreeGroup α, M) = 0` for every `i ≥ 2`** and every
  `𝔽₂`-representation `M` (i.e. the cohomological dimension of a free group is `≤ 1`): the
  vanishing of `H²` of the free group, which is the input the Gaschütz relation-rank dictionary
  (`r = dim H²`) and the classical five-term-sequence computations both need.  Proved here from
  scratch (cocycle computation + the coinduced-representation dimension shift); Mathlib has no
  such statement.
* `unrClassTwoTor_surjective` -- the *generator half* in ideal-class form: the two-descent
  `unrClassTwoTor : V^{unr}/Kc^{×2} → Cl(Kc)[2]` of `card_VTwoUnramified_mod_squares_Kc` is
  **surjective** (hence, with `unrClassTwoTor_injective`, an isomorphism): every class of order
  `2` in `Cl(Kc)` is the class attached to an unramified quadratic extension.  Combined with the
  count `#(V^{unr}/Kc^{×2}) = 32` this is `V^{unr}/Kc^{×2} ≅ Cl(Kc)[2]`, i.e. the "unramified
  Hilbert 90" half of the classical theorem at `p = 2`, in ideal language and with no class field
  theory.
* `neg_one_kummer_slack_Kc` -- the arithmetic of the *slack*: `-1` is a nonsquare element of Koch's
  radical `V_∅` whose square root is not in `Kc_∅`, so the extra `𝔽₂`-dimension of `V_∅/Kc^{×2}`
  (dimension `6`) over the Kummer image `H¹(G_∅,𝔽₂)` (dimension `d(G_∅) = 5`) is exactly the class
  of the unit `-1` (README §9.4).
* `Gaschutz/RelModule.lean` -- **the relation-module form of the crux**: the Crux *is equivalent*
  to the statement that the relation module `K ⧸ K²[K,F]` of the presentation map is generated by
  `r` elements (`HasRelModulePresentation`), the form in which the classical theorem
  (Koch Ch. 11 Thm 11.3, Shafarevich 1963, HMR arXiv:2103.09508) is *proved*; hence the arithmetic
  input may be supplied in either normalisation, and the cohomological dictionary (Gaschütz) is
  bypassed (`hasProTwoPresentation_iff_hasRelModulePresentation`).
* `Gaschutz/Kc.lean` -- the `Kc` instance `KcRelModuleBound`, its equivalence with
  `KcProTwoPresentationInput` (`kcRelModuleBound_iff_input`), the walls
  (`infiniteProTwoExtension_Kc_of_relModuleBound`, `unramifiedPro2TowerWall_of_relModuleBound`,
  `boundedRdTowerWall_of_relModuleBound`, `exists_unramifiedLevel_rootDiscr_of_relModuleBound`) and
  item (3) (`proTwoShafarevichKochInput_Kc_of_relModuleBound_and_realization`).
* `Gaschutz/Card.lean` -- the *cardinality* form `Nat.card (K ⧸ K²[K,F]) = 2 ^ k`, `k ≤ r`
  (`natCard_relFrattiniQuotient_Kc_of_relModuleBound`, `= 2^k` with `k ≤ 6` for `Kc`), with the two
  implications between the cardinality condition and the spanning clause of the crux.
* `Gaschutz/Cup.lean` -- **the cup product of continuous cohomology**: for a commutative ring `R`
  with trivial `G`-action, the cup product of two `1`-cochains satisfies the Leibniz rule
  `d²(f ∪ g) = (d¹f)*g - f*(d¹g)`, hence takes `1`-cocycles to `2`-cocycles and (because `B¹ = 0`
  for a trivial action) descends to a bilinear pairing `H¹(G,R) × H¹(G,R) → H²(G,R)`.  Mathlib has
  no cup product at all; this and `CupTwo` are the first primitives of the classical Koch/Wingberg
  pairings of the relation count.
* `Gaschutz/CupTwo.lean` -- the next degree of that construction: the cup product `H¹ × H² → H³`,
  with Leibniz rule `d³(f ∪ g) = (d¹f)*g - f*(d²g)`; the descent in the `H²`-variable is the
  Leibniz computation `f ∪ d¹u = d³(f ∪ u)` (up to sign, using the cocycle condition on `f`),
  which is exactly the shape in which a `2`-cocycle of `G_∅` would be paired with Koch's radical.
* `CupInflationRefutation.lean` -- a **machine-checked counterexample**: for the surjection
  `ℤ/4 × ℤ/2 ↠ ℤ/2 × ℤ/2` of groups of the same generator rank, the inflation
  `H²(Q,𝔽₂) → H²(G,𝔽₂)` has a non-trivial kernel (`cupInflationAlpha` is a `2`-cocycle of `Q` that
  is not a coboundary, but whose pullback to `G` is the coboundary of the carry function `⌊·/2⌋`).
  This refutes the argument recorded in README §8.7 (see §25.6): `H¹(Q) ≅ H¹(G)` does *not* force
  `H²(Q) ↪ H²(G)`; the correct exactness is `ker(inf) = im(tg)`.
* `Crux.lean` -- the crux in *normal form*: `hasProTwoPresentation_mono` (relator lists may be
  padded) makes `KcProTwoPresentationInput ↔ HasProTwoPresentation Kc 5 6`
  (`kcProTwoPresentationInput_iff_five_six`), i.e. the whole chapter has exactly one open
  proposition, with no `∃ r ≤ 6` slack; `shafarevichKochBound_Kc` records the same numbers as
  `ShafarevichKochBound Kc 5 6`, i.e. the classical bound `r ≤ d + d₂(O_K^×)` at `d = 5`, `d₂ = 1`.
-/

/-! The remaining arithmetic input is the classical Shafarevich--Koch *relation bound*; see
`README.md` §3 and §8 for its exact form, its literature, and the precise reason it is not
reachable inside this workspace (it needs global class field theory: Koch Ch. 11 Thm 11.3,
Wingberg's duality / NSW Ch. VIII §8 Thm 8.8.1, or idèlic reciprocity). -/

/-! ### `ValueTheorem/`: the pro-`2` value theorem (`d(G_∅) = r(G_∅)` = `dim H²_cont`)

* `ValueTheorem/Basic.lean` -- the `𝔽₂`-module structure of `H¹(Γ,𝔽₂)`, `H²(Γ,𝔽₂)` (they have
  exponent two), the two normalisations of a dimension bound
  (`Work.RelatorRank.ContH2DimLe ↔ finrank ≤ r`), the identification of `H¹` with the group of
  continuous characters, and finiteness of `H¹`/`H²` at a finite level.
* `ValueTheorem/InflSystem.lean` -- the colimit system of `H²(Γ,𝔽₂)`: the canonical inflation
  `H2InflTwo U : H²(Γ ⧸ U) →+ H²(Γ)`, its covering property, **monotonicity in the level**
  (`H2InflTwo_range_mono`: the finer level sees more), the directedness of the family of ranges,
  the finiteness of each range, and the bound
  `Work.ShafarevichKoch.contH2DimLe_of_range_finrank`.  A bound on the *levels* would not suffice
  (`H²(Γ ⧸ Φ(Γ),𝔽₂)` is much bigger than `H²(Γ,𝔽₂)` for `Γ = ℤ₂`); the correct statement is the
  bound on the level *ranges*, which is the form in which the classical transgression computation
  is consumed. -/
