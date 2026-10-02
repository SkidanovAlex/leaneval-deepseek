import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.Euler
import Submission.Work.Thom.Gysin
import Submission.Work.Thom.CharClasses
import Submission.Work.Thom.Glue
import Submission.Work.Thom.Glue2
import Submission.Work.Thom.ATools
import Submission.Work.Thom.Relocate.TrivProductHomeo
import Submission.Work.Thom.localThom_line
import Submission.Work.Thom.subsingleton_PieceCohA
import Submission.Work.Thom.thomClass_of_cover_gen
import Submission.Work.Thom.nonempty_thomClass_of_compatible_local
import Submission.Work.Thom.thomClassTrivialEuclideanA
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.localThom_genFibre
import Submission.Work.Thom.nonempty_thomClass_of_oriented_genFibre
import Submission.Work.Thom.subsingleton_PieceCoh_genFibre
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.exists_path_GL_complex
import Submission.Work.Thom.isOrientedOver_of_gauge_homotopy
import Submission.Work.Thom.exists_gauge_homotopy_of_complex
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.complexDet
import Submission.Work.Thom.complexBundleAux
import Submission.Work.Thom.complexification
import Submission.Work.Thom.complexOrientation
import Submission.Work.Thom.topPontryagin
import Submission.Work.Thom.QuotientLin
import Submission.Work.Thom.tautologicalQuotient
import Submission.Work.Thom.FiniteCover
import Submission.Work.Thom.localThom_union
import Submission.Work.Thom.Coh_zero_cover_injective
import Submission.Work.Thom.thomClass_of_finite_cover
import Submission.Work.Thom.thomClass_of_complex_fintype
import Submission.Work.Thom.bijective_proj_zeroComplementA
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.smooth8
import Submission.Work.Thom.cappedAgreement
import Submission.Work.Thom.chernClass_eq_zero_of_lt
import Submission.Work.Thom.chernClass_rank_zero_of_ne
import Submission.Work.Thom.chernClass_zero_eq_oneH
import Submission.Work.Thom.pontryaginClass_one
import Submission.Work.Thom.nonempty_closedOrientedSmooth8
import Submission.Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection
import Submission.Work.Thom.pontryaginClass_zero
import Submission.Work.Thom.cappedCongruenceTangent_of_hirzebruchCongruence8
import Submission.Work.Thom.cappedAgreement_of_cappedAgreementPontryagin
import Submission.Work.Thom.no_cappingDiffeo_of_hirzebruchCongruence8
import Submission.Work.Thom.cappedAgreementPontryagin_of_cappedAgreement
import Submission.Work.Thom.p1Tangent_eq_zero_of_finrank_le_one
import Submission.Work.Thom.exists_tautQuotientCore
import Submission.Work.Thom.pdCohMap_finInter_eq_zero
import Submission.Work.Thom.exists_unique_pieceClass
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.tautQuotientComap
import Submission.Work.Thom.tautQuotientCore_comap
import Submission.Work.Thom.pieceMap
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.trivialChern
import Submission.Work.Thom.continuous_totalSpaceMap_field
import Submission.Work.Thom.section_injective
import Submission.Work.Thom.exists_coreMapFibre
import Submission.Work.Thom.sumEps
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.pontryagin1_comap
import Submission.Work.Thom.pontryaginClass_comap
import Submission.Work.Thom.whitney
import Submission.Work.Thom.chernClass_BundleIso
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Thom.sumStableDefs
import Submission.Work.Thom.sumStableMain
import Submission.Work.Thom.sumToZ_sumToQ
import Submission.Work.Thom.sumToQ_sumToZ
import Submission.Work.Thom.sumEps_coordChange_Epart
import Submission.Work.Thom.sumQuotient_baseSet
import Submission.Work.Thom.sumStableCorollaries
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Thom.thomClass_of_oriented_fintype
import Submission.Work.Thom.p1Tangent_sphere_eq_zero
import Submission.Work.Thom.realSumStableDefs
import Submission.Work.Thom.exists_rhoC_compat
import Submission.Work.Thom.realSumStable

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000
-- NOTE (import islands): `Submission.Work.Thom.bijective_proj_zeroComplement_gen` and
-- `Submission.Work.Thom.subsingleton_PieceCoh_iUnion_finInter` are deliberately NOT imported here:
-- they lie in the island of `Submission.Work.Cohomology.subsingleton_pdCohSub_union` (via
-- `subsingleton_PieceCohA` / `prod_sphere_aux`), which clashes with this module's island (via
-- `ATools` / `CompatTrans.proj_pair_injective`).  Import them directly when they are needed.

/-!
# The Thom isomorphism, the Euler class and characteristic classes: the entry point

**This is the module to import.**  It gathers everything the chapter
`Submission/Work/Thom/` delivers, in the *island* of the workspace that contains
`Submission/Work/Cohomology/localCohomology.lean`, `Submission/Work/Cohomology/CompatTrans/proj_pair_injective.lean`
and `Submission/Work/Cohomology/Crux/ovlRestrictionSurjective.lean` — the island of
`Submission/Work/TangentClasses/`, `Submission/Work/SignatureBordism/`,
`Submission/Work/CharacteristicClasses/`, `Submission/Work/Milnor/` and this directory's
`Interface.lean` / `CappedInterface.lean`.  (The workspace as delivered is the union of several
mutually incompatible such islands; see `README.md`, ADDENDUM 16.)

## 1. The bundle, the Thom pair, and the Thom class

* `Work.TangentClasses.RealBundle B F ι` — a real vector bundle as gluing data
  (Mathlib's `VectorBundleCore`), with `Work.TangentClasses.RealBundle.pullback` (pullback along a
  base map), `Work.TangentClasses.RealBundle.sum` (Whitney sum),
  `Work.TangentClasses.RealBundle.trivial` (the trivial bundle); the total space is
  `Z.TotalSpace`, the projection `Work.Thom.bundleProj Z`, the zero section `Work.Thom.zeroSection Z`,
  and the complement of the zero section `Work.Thom.zeroComplement Z` — the pair
  `(Z.TotalSpace, Z.zeroComplement)` is the *open* Thom pair, and its relative cohomology is
  `Work.Thom.OpenThom Z n`.
* `Work.Thom.thomMap Z n τ k : H^k(B;ℤ) → H^{k+n}(E,E∖0;ℤ)`, `x ↦ π^*(x) ⌣ τ`.
* `Work.Thom.ThomClass Z n` — a **Thom class** of a rank-`n` bundle: a class `τ ∈ H^n(E,E∖0;ℤ)`
  for which `thomMap Z n τ` is bijective in every degree.  A `ThomClass` *is* the chapter's notion
  of an oriented bundle of rank `n` together with the Thom isomorphism
  `H^k(B;ℤ) ≅ H^{k+n}(E,E∖0;ℤ)` (`Work.Thom.ThomClass.thomEquiv`).
* `Work.Thom.ThomClass.eulerClass` — the **Euler class** `e(E) = z^*(τ) ∈ H^n(B;ℤ)`, with
  `Work.Thom.ThomClass.eulerClass_eq_zero_of_nowhereZeroSection`: it vanishes as soon as the bundle
  admits a nowhere-zero continuous section.  The **Gysin sequence** of the sphere bundle is
  `Work.Thom.gysinEuler` / `Work.Thom.gysinπ` / `Work.Thom.gysinδ` with the exactness statements
  `Work.Thom.gysin_exact_at_base` / `_at_sphere` / `_at_cobase` (`Submission/Work/Thom/Gysin.lean`),
  and `Work.Thom.gysinEuler_eq_cupEuler`: `gysinEuler` *is* the cup product with the Euler class.

## 2. The Thom isomorphism theorem

* `Work.Thom.thomClass_of_cover_gen` (`Submission/Work/Thom/thomClass_of_cover_gen.lean`) — **the
  Thom isomorphism theorem for a general (not necessarily trivial) bundle**: if `X = U ∪ V` is an
  open cover of the base, a class `τ` of the Thom pair restricts to *local* Thom data over `U`, `V`
  and `U ∩ V` (`Work.Thom.LocalThom`), and the overlap's relative cohomology vanishes in degree
  `n - 1`, then `τ` is a Thom class of the bundle: `∀ k, Function.Bijective (thomMap Z n τ k)`.
* `Work.Thom.nonempty_thomClass_of_cover` — the same with the conclusion
  `Nonempty (ThomClass Z n)`.
* `Work.Thom.nonempty_thomClass_of_compatible_local`
  (`Submission/Work/Thom/nonempty_thomClass_of_compatible_local.lean`) — **the local-to-global
  form**: *given* local Thom data `hUloc`, `hVloc` over the two pieces and `hUVloc` over the
  overlap, *compatible* (`hUloc.τ` and `hVloc.τ` restrict to `hUVloc.τ` — this is the chapter's
  model of an **orientation** of the bundle over the cover), and the vanishing of
  `H^{n-1}(X|_{U∩V}, X|_{U∩V}∖0)`, a Thom class exists.  The global class is produced by the
  glueing `Work.Thom.exists_glue` (middle exactness of the honest relative Mayer–Vietoris sequence).

## 3. Producing the local Thom data (the local step of the induction)

* `Work.Thom.nonempty_localThom_of_subset_baseSet_of_trivial`
  (`Submission/Work/Thom/localThom_line.lean`) — **the local step**: for a bundle `Z` with model
  fibre `F` and a set `U ⊆ B` contained in a chart `Z.baseSet i`, a Thom class of the *trivial*
  bundle `U × F → U` of the same rank transports along the chart homeomorphism of the piece
  (`Work.Thom.pieceChartA`) to `Work.Thom.LocalThom Z n U`.
* `Work.Thom.nonempty_localThom_of_subset_baseSet` (`Submission/Work/Thom/localThom_full.lean`) —
  **the producer in every rank and unconditional**: the trivial bundle's Thom class is
  `Work.Thom.thomClassTrivialEuclideanA` (`Submission/Work/Thom/thomClassTrivialEuclideanA.lean`,
  the island-compatible copy of `nonempty_thomClass_trivial_euclidean`, built from the island
  copies `Submission/Work/Thom/ModelThomA.lean`, `CapChainA.lean`, `capRelCohIsoA.lean`,
  `spherePuncturedA.lean`, `discFullA.lean`).
* `Work.Thom.localThom_genFibre` (`Submission/Work/Thom/localThom_genFibre.lean`) — the same
  producer for an **arbitrary finite-dimensional real fibre** `F` (`Module.finrank ℝ F = n`), which
  is the form needed for the *realification* `Work.Thom.realification` of a complex bundle.
* `Work.Thom.nonempty_localThom_of_line` — the unconditional line-bundle case (`F = ℝ`, `n = 1`).
* `Work.Thom.nonempty_thomClass_of_oriented` / `nonempty_thomClass_of_charts`
  (`Submission/Work/Thom/localThom_full.lean`) — **the assembled theorem**: for a bundle trivial
  over a two-piece open cover which is **oriented** over it (`Work.Thom.IsOrientedOver`, i.e. the
  local data over the two pieces restrict to common data over the overlap — the algebraic form of
  the classical condition on the transition functions), a Thom class exists; for a cover by two
  charts the low-degree vanishing is automatic.
* `Work.Thom.subsingleton_PieceCoh_of_lt_rankA` (`Submission/Work/Thom/subsingleton_PieceCohA.lean`)
  — **the low-degree vanishing** `H^m(X|_W, X|_W∖0) = 0` for `m < n` and `W` in a chart, the other
  input of the theorem of §2.

## 4. Characteristic classes

* `Work.Thom.CharClasses` (`Submission/Work/Thom/CharClasses.lean`) — `eulerClassGen`, the mod-2
  class `stiefelWhitney`, the predicate `IsThomClass₂`, and `p1Presentation_unique`.
* `Submission/Work/Thom/Euler.lean` — the vanishing theorems for the Euler class
  (odd rank, nowhere-zero section, ...).

## 5. The Chern classes, the Pontryagin classes, and the repaired interface (ADDENDUM 20)

* `Work.Thom.chernClass m j Z` (`Submission/Work/Thom/chernClass.lean`) — **the Chern classes**
  `c_j(V) ∈ H^{2j}(B;ℤ)` of a complex bundle `V` of rank `m` over a finite gluing-data cover, by
  recursion on the rank: `c_m = e(V_ℝ)` (the top class), `c_j(V) = (π^*)^{-1} c_j(Q)` for `j < m`
  (`Q` the tautological quotient of `Work.Thom.tautQuotient` over the punctured total space, using
  the Gysin descent `Work.Thom.bijective_proj_zeroComplementA`), `c_j = 0` for `j > m`, `c_0 = 1`.
  See `Work.Thom.chernClass_succ_of_le`, `Work.Thom.chernClass_succ_top`, `chernClass_succ_top'`,
  `Work.Thom.chernClass_succ_of_gt`, and the rank-uniform API `Work.Thom.chernClass_eq_zero_of_lt`,
  `Work.Thom.chernClass_rank_zero_of_ne`, `Work.Thom.chernClass_zero_eq_oneH` (i.e. `c_0 = 1` in
  every rank) and `Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection`.
* `Work.Thom.pontryagin1`, `Work.Thom.pontryaginClass` (`Submission/Work/Thom/manifoldP1.lean`) —
  **the Pontryagin classes of a real bundle**, `p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)`.
* `Work.Thom.p1Tangent'`, `Work.Thom.p2Tangent'` — **`p₁(TM)`, `p₂(TM)` of a compact smooth
  manifold** (item (4) of the deliverable): the four-step construction
  `tangentBundle → mapFibre → reindex (finite chart cover) → complexificationCore → chernClass`.
  These are *defined* classes, functions of `M` alone.
* `Work.Thom.ClosedOrientedSmooth8` (`Submission/Work/Thom/smooth8.lean`) — **the repaired
  interface (option F2 of NOTES §15.10)**: a closed oriented smooth `8`-manifold with a generating
  fundamental class, whose Pontryagin classes `.p1`, `.p2` are **definitions**
  (`p1Tangent'`, `p2Tangent'`), never free data; with `.sigma`, `.p1Sq`, `.p2Num`, `.hirzebruch`,
  `.congruence`, and the global statements `Work.Thom.HirzebruchIdentity8`,
  `Work.Thom.HirzebruchCongruence8` and the proof
  `Work.Thom.congruence8_of_hirzebruch8` that the first implies the second.

## 6. The G1 enablers: canonicalisation of the choice points

* `Work.Thom.exists_glue_unique` (`Submission/Work/Thom/exists_glue_unique.lean`, **import it
  directly**: it lies in the island of `Submission.Work.Cohomology.prod_sphere_aux`, so it is
  deliberately *not* in this module) — **uniqueness** of the Mayer--Vietoris glueing
  (`Work.Thom.exists_glue` upgraded to `∃!`) under the vanishing of the overlap in degree `n-1`,
  with the reusable base case `Work.Thom.honestF_injective_of_subsingleton_overlap`.  This is what
  makes `Classical.choose` of the glueing *canonical* (any two witnesses are equal), hence
  natural.
* `Work.Thom.exists_tautQuotientCore` and `Work.Thom.tautQuotientCore_*` — the tautological quotient
  with an explicit index map, removing one `Classical.choose` from the critical path.
* `Work.Thom.pdCohMap_finInter_eq_zero` — a class of `PieceCoh Z (⋃ k, U k) n` restricting to `0`
  on every `finInter U S` is `0` (under the ladder's own vanishing hypothesis `hlowU`): the
  "separation on a finite cover" that makes the Mayer–Vietoris witness of
  `Work.Thom.thomClass_of_finite_cover` **unique**;
* **`Work.Thom.exists_unique_pieceClass`** — the `∃!` form of `Work.Thom.thomClass_of_finite_cover`,
  so its `Classical.choose` is canonical;
* **`Work.Thom.thomClassOf`, `Work.Thom.localThomOfComplexCover`, `Work.Thom.thomClassOf_spec`**
  (`thomClassOf.lean`) — the **canonical** Thom class of the realification of a complex bundle,
  built from the two `∃!`-statements above; `Work.Thom.thomClassRank` **is** this construction
  (`thomClassRank_def`), so `chernClass`, `pontryagin1`, `pontryaginClass`, `p1Tangent'`,
  `p2Tangent'` are all canonical;
* `Work.Thom.punctMap`, `Work.Thom.punctMap_apply` (`tautQuotientComap.lean`) — the canonical map of
  punctured total spaces over `f : B' → B`, from the delegated `Work.Thom.exists_punctMap`;
* **`Work.Thom.tautQuotientCore_comap`** — the tautological quotient **commutes with pullback**:
  `bundleComap (tautQuotientCore Z) (punctMap Z f) = tautQuotientCore (bundleComap Z f)`.  This is
  G2a, the first rung of the splitting principle (ADDENDUM 21.8);
* `Work.Thom.pieceMap`, `Work.Thom.pieceMap_apply` — the same for an arbitrary piece `proj ⁻¹' W`;
* **`Work.Thom.chernClass_comap`** (`chernClass_comap.lean`) — **G2b: the Chern classes are natural
  under pullback**: `chernClass m j (bundleComap Z f) = (CohMap f ℤ (2*j)).hom (chernClass m j Z)`.
  With it: `Work.Thom.thomClassRank_eulerClass_comap` (the Euler class of the canonical Thom class
  is natural), `Work.Thom.descent_symm_general` (the Gysin descent commutes with pullback), and
  `Work.Thom.thomClassOf_comap_via_cover` (`thomClassOf_comapAux.lean`);
* **`Work.Thom.pontryagin1_comap`**, **`Work.Thom.pontryaginClass_comap`** — the Pontryagin classes
  are natural under pullback: `p_i(f^*E) = f^*(p_i(E))`;
* `Work.Thom.bundleSum` (`whitney.lean`) — **the Whitney sum of gluing data over an arbitrary
  field** (in particular over `ℂ`), with `bundleSum_baseSet/_indexAt/_coordChange`,
  `bundleComap_bundleSum` and `bundleSum_trivial_coordChange` (the bundle-level statement of
  stability).  This is the first building block of the Whitney formula (G2c).

## 7. What is *not* here

* the **Whitney formula** `p(E ⊕ F) = p(E)p(F)` and **stability** `p(E ⊕ ε^k) = p(E)`, and hence
  (via `TSⁿ ⊕ ε¹ ≅ ε^{n+1}`) `p₁(TSⁿ) = 0`.  What *is* proved is the **vanishing principle**
  (`Work.Thom.trivialChern`): `c_j` of a pullback vanishes whenever the target has vanishing
  `H^{2j}`; in particular `c_j` of a *trivial* complex bundle is `0` for `j ≠ 0`
  (`Work.Thom.chernClass_trivial`), so `p₁` and `p_i` of a trivial real bundle vanish.  The exact
  remaining content — isomorphism-invariance of `chernClass` and the reduction of stability to it —
  is `README.md` ADDENDUM 23;
* the agreement `Work.Thom.CappedAgreement'` of `p1Tangent'` with
  `Work.Milnor.cappedPontryaginClass` on the capped `8`-manifold (ADDENDUM 22.2/23.5);
* the general (not only complexified) orientation of a real bundle, the Stiefel–Whitney classes over
  `ℤ/2`, and `⟨e(TB),[B]⟩ = χ(B)` (items 2–3 of the chapter's deliverable).

## 8. What is here for the structure of bundles

* `Work.Thom.BundleIso` (`Iso.lean`) — **isomorphisms of vector bundles** (fibrewise linear inverse
  pairs with continuous total-space maps), with `refl`, `symm`, `trans`, `ofEq`, `toHomeomorph`;
* `Work.Thom.BundleIso.punctMap`, `Work.Thom.BundleIso.punctHomeomorph`,
  `Work.Thom.BundleIso.relCohMap_punct_bijective` (`IsoPunct.lean`) — the induced homeomorphism of
  the punctured total spaces and the induced isomorphism of the relative cohomology of the Thom
  pairs;
* `Work.Thom.continuous_totalSpaceMap_field` — the `⟨x,v⟩ ↦ ⟨f x,v⟩` total-space continuity lemma
  for an arbitrary field of scalars;
* `Work.Thom.injective_CohMap_of_section` (`section_injective.lean`) — **a map with a continuous
  section has injective pullback on cohomology**, the elementary input of the reduction of stability
  to isomorphism-invariance (ADDENDUM 23.3);
* `Work.Thom.exists_coreMapFibre` (`exists_coreMapFibre.lean`) — **the transport of a bundle along a
  continuous linear equivalence of fibres** (the `ℂ`-version of `RealBundle.mapFibre`), together
  with a `Work.Thom.BundleIso` between the bundle and its transport;
* `Work.Thom.prodFinEquiv`, **`Work.Thom.sumEps`** (`sumEps.lean`) — **the Whitney sum `Z ⊕ ε¹`
  presented in the standard fibre `EuclideanSpace ℂ (Fin (m+1))`** (via `exists_coreMapFibre` along
  `prodFinEquiv`), with `sumEps_baseSet`, `sumEps_indexAt`, `sumEps_coordChange` and
  `nonempty_bundleIso_sumEps`.  This is the bookkeeping that makes *stability* `c_j(Z ⊕ ε¹) = c_j(Z)`
  a statement about a bundle to which the Chern recursion applies (ADDENDUM 23.3).
-/

namespace Work.Thom

end Work.Thom
