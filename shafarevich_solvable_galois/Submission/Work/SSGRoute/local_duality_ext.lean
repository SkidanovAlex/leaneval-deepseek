import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_zmod_prime_iso_corrected
import Submission.Work.SSGRoute.mapExactFunctor_id
import Submission.Work.SSGRoute.levelPair_id
import Submission.Work.SSGRoute.extHMap_id
import Submission.Work.SSGRoute.phi1_defs
import Submission.Work.SSGRoute.e0b_bridge
import Submission.NK.HassePrinciple.subsingleton_classGroupRep_one
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_fiberIdelesRep_eq_one
import Submission.NK.HassePrinciple.LocalUnits
-- NOTE (2026-09-27): `e0b_bridge_structure` supplies a term of
-- `SSGRoute.Phi1.ExtGroupCohomologyBridge` but its import chain through
-- `e0b_delta → ExtMkCompExtClass.yoneda_extClass` is being edited by a colleague; the module is
-- re-imported once that chain is green.  An independent copy of the same construction is
-- delegated as `Work.SSGRoute.nonempty_extGroupCohomologyBridge`
-- (`SSGRoute/nonempty_extGroupCohomologyBridge.lean`, from `Work.SSGRoute.extH_groupCohomology_iso`).
-- import Submission.Work.SSGRoute.e0b_bridge_structure
import Submission.Work.SSGRoute.powHomRepDefs
import Submission.Work.SSGRoute.cyclicNormCriterion_rep
import Submission.Work.SSGRoute.normCriterion_quotient
import Submission.Work.SSGRoute.hilbert90_localUnitsRep
import Submission.Work.SSGRoute.nonempty_extGroupCohomologyBridge
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.exists_H1_inflated_ne_zero
import Submission.Work.SSGRoute.CFTSide.cyclicNormCriterion_classesK
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic
import Submission.Work.SSGRoute.normImage_at_level_proper
import Submission.Work.SSGRoute.cyclic_quotient_of_H1_ne_zero
import Submission.Work.SSGRoute.normImage_at_level_proper_K
import Submission.Work.SSGRoute.rightDetect_fixed_functional
import Submission.Work.SSGRoute.detectAbove_sub_step
import Submission.Work.SSGRoute.rightDetect_of_sylow
import Submission.Work.SSGRoute.ext_two_trivial_ptors
import Submission.Work.SSGRoute.decompK_restrict_surjective
import Submission.Work.SSGRoute.local_pTorsion_card
import Submission.Work.SSGRoute.local_duality_ext_extH_finite
import Submission.Work.SSGRoute.exists_level_above_quotientNorm_avoids
import Submission.Work.SSGRoute.sylow_in_defs
import Submission.Work.SSGRoute.levelPair_baseChange_in
import Submission.Work.SSGRoute.phi1_mono_base
import Submission.Work.SSGRoute.natCard_cokernel_lt
import Submission.Work.SSGRoute.levelPair_comp_extHMap
import Submission.Work.SSGRoute.localUnits_infl_injective
import Submission.Work.SSGRoute.extCor_two_injective_pTorsion
import Submission.Work.SSGRoute.local_duality_ext_core_imports
import Submission.Work.SSGRoute.exists_section_of_fixed_generator
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.E6Calc.extCor_levelPair
import Submission.Work.SSGRoute.extCor_yoneda_comp
import Submission.Work.SSGRoute.Z8.SylowSetup
import Submission.Work.SSGRoute.Z8.levelPair_vanish_of_vanish_closure
import Submission.Work.SSGRoute.Z8.localUnits_extH_pTorsion_card_gcd
import Submission.Work.SSGRoute.Z8.extCor_injective_pTorsion_gcd
import Submission.Work.SSGRoute.E7bZ8Step1
import Submission.Work.SSGRoute.exists_galoisClosure_level
import Submission.Work.SSGRoute.extRes_injective_of_index
import Submission.Work.SSGRoute.exists_localZetaCoeff
import Submission.Work.SSGRoute.pgroup_fixes_primitiveRoot
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.pTorsion_card_sylowLevel
import Submission.Work.SSGRoute.exists_smul_eq_of_annihilator
import Submission.Work.SSGRoute.extH_natCard_smul_eq_zero
import Submission.Work.SSGRoute.lde_stabIncl
import Submission.Work.SSGRoute.arch_quotientNorm_avoids
import Submission.Work.SSGRoute.exists_fixed_element_of_connecting_eq_zero
import Submission.Work.SSGRoute.E8Helpers
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.ext_res_mulEquiv
import Submission.Work.SSGRoute.extH_congr
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.Work.SSGRoute.E7bZ8.Y3FullC
import Submission.Work.SSGRoute.e6_util

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E7b `local_duality_ext` — canonical local Tate duality, in `Ext` form

## Mathematical content of the statement

Fix `w : Place K`.  Writing `D = D_w = decompK w` and `D' = D_{w'} ≤ Gal(L/k)` for `w' ∣ w`,
`M' = Rep.res (decompK w).subtype M`, the pairing of the statement is the Yoneda product
`levelPair f ι : Ext¹_D(M', K_wˣ) × H¹(D', M') → H²(D', L_{w'}ˣ) = Br(L_{w'}/k_v)`
(`f = ` restriction `D' → D`, `ι : K_wˣ → L_{w'}ˣ` the canonical local embedding).  Since `|D_{w'}|`
acts trivially on `M`, `H¹(D',M')` is killed by `p`, so the `p`-torsion hypothesis on `lam` in (ii)
is automatic (`p_smul_lam_eq_zero` below).

This is local Tate duality at a *finite* level in the "extended" form: the left variable is
`Ext¹_D(M, K_wˣ)`, not the Tate twist `H¹(D, M^∨(1))`.  The two differ by the coefficient sequence
of `0 → ℤ --p--> ℤ → 𝔽_p → 0`, and the arithmetic content is that after passing to all levels
`L ⊇ K` the pairing is perfect: (i) says the joint left kernel over all levels vanishes, (ii) says
that at a level with `p ∣ [L_{w'} : k_v]` every functional is realised already by a class at the
level `K`.

## What is proved in this file

* `extRes_add`, `extRes_zero`, `extHMap_add`, `extHMap_zero`, `levelPair_add`, `levelPair_zero`,
  `levelPair_add_h`, `levelPair_zero_h`: the pairing is bilinear (`levelPairFunctional`,
  `range_levelPairFunctional` record the realisation clause as a range statement);
* `comp_assoc_of_first_deg_zero`: the `Ext`-associativity law with a degree-`0` first factor, and
  `levelPair_extHMap`: **the pairing at a level is the restriction of the pairings at all higher
  levels** — for `h = extHMap f (id _) h₀` one has `levelPair f ι x h = extHMap f ι (yonedaPair x h₀)`;
* `Rep.nsmul_id_eq_zero`, `ext_nsmul_p_torsion`, `ext_nsmul_p_torsion_left`: `Ext` of a module
  killed by `p` is killed by `p` (both variables), and `p_smul_lam_eq_zero` (the `p`-torsion
  hypothesis of clause (ii) is free).

### The base case `M = 𝔽_p` (subsequently added, all axiom-clean)

* `hilbert90_localUnits_extH`: **local Hilbert 90 in the `Ext` vocabulary**,
  `Subsingleton (extH (localUnitsK w) 1)`, i.e. `H¹(D_w, K_wˣ) = 0`.  Route:
  `NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_of_injective_ringAut` (Hilbert 90 for
  a faithful action on the units of a field, applied to `NK.HassePrinciple.localAutHom`, whose
  injectivity is `NK.HassePrinciple.localAutHom_injective`), then
  `NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary Coeff` (change of the
  coefficient ring from `ℤ` to `Coeff = ULift ℤ`), then
  `Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology` (`e0b_bridge.lean`, the
  *bare* half of E0b: `Hⁿ(G,A) ≃+ extH A n` for any projective resolution, via the bar resolution).
* `local_duality_ext_base_source_uncond`: the source of the base case,
  `Ext¹_{D_w}(𝔽_p, K_wˣ) ≃+ H⁰(D_w,K_wˣ)/p·H⁰(D_w,K_wˣ)` (`= k_vˣ/k_vˣ^p`), with the Hilbert 90
  hypothesis of `local_duality_ext_base_source` discharged.
* `pushClass_lde`, `pushClass_add`, `pushClass_surjective`, `localUnits_pushClass_surjective`: the class
  of the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` pushed out along `φ : ℤ → C`; additivity;
  surjectivity of the construction (`H¹ = 0`); and its local instantiation (every class of
  `Ext¹_{D_w}(𝔽_p, K_wˣ)` is such a class).  `Work.SSGRoute.pushClass_eq_zero_iff_factors`
  (delegated, `SSGRoute/pushClass_eq_zero_iff_factors.lean`) is the kernel: `pushClass_lde φ = 0` iff
  `φ` factors through multiplication by `p` on `ℤ`.
* `levelPair_pushClass`: **the `Ext`-algebra heart of the base case.**  For `x = pushClass_lde p A φ`
  and `h ∈ H¹(H, 𝔽_p)` at a finer level `f : H →* G`,
  `levelPair f ι x h = (h.comp (coeffSES_H.extClass) rfl).comp (mk₀ (res f φ ≫ ι)) _` — the level
  pairing is the Yoneda product of `h` with the *level-`H`* coefficient sequence followed by the
  coefficient map.  (Local, coefficient-agnostic counterpart of `E3Base.phiAt_pushClass_eq`.)
* `levelPair_pushClass_bridge`: the same identity *modulo* the `Ext`/group-cohomology bridge
  `SSGRoute.Phi1.ExtGroupCohomologyBridge` (`b`): `levelPair f ι (pushClass_lde p A φ) h = 0` iff
  `groupCohomology.map (id) (res φ ≫ ι) 2 (δ χ) = 0`, where `χ = b⁻¹ h`.  This is the interface at
  which the arithmetic input (Kummer / cyclic norm criterion,
  `NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic`) is consumed.
  Note: both proofs need `set_option backward.isDefEq.respectTransparency false` (scoped to
  `section PushClassSpine`), without which `Ext`-rewrites stall on transparency.

## Session 3 (2026-09-27): the base case `M = 𝔽_p` at a prime cyclic level is now reduced

New in this file (all axiom-clean; the only `sorry` left in the file is the target itself):

* `powHomRep_eq_of_apply_one` / `pushClass_coeff_eq_powHomRep`: a `G`-map `unitRep G ⟶ A` is
  `powHomRep a` for `a` its value on `1` (so the coefficient map of any `pushClass_lde` class is a
  `powHomRep`);
* `rep_hom_apply_one_fixed`: that value on `1` is `G`-fixed;
* `cyclicNormCriterion_rep_apply_one`: the arithmetic input `Work.SSGRoute.cyclicNormCriterion_rep`
  (delegated, `SSGRoute/cyclicNormCriterion_rep.lean`, a port of
  `CFTSide.cyclicNormCriterion_classesK` to an arbitrary `Rep Coeff G`) in the form in which the
  coefficient map is an arbitrary `unitRep G ⟶ A`;
* `levelPair_trivial_eq_zero_iff_norm`: **the base case of E7b at a prime cyclic level.**  For a
  level `L ⊇ K`, a place `w' ∣ w` with `D_{w'} = Gal(L_{w'}/k_v)` cyclic of order `p`, the level
  pairing of a class `pushClass_lde p K_wˣ φ` with a nonzero character `h` vanishes iff the local unit
  `a = ι(φ 1)` lies in the image of the norm endomorphism of `L_{w'}ˣ` over `D_{w'}`.  Proof:
  `levelPair_pushClass_bridge` (the cup product with `δχ`) + `cyclicNormCriterion_rep_apply_one`.
  **Everything remaining in the base case is now arithmetic.**

Infrastructure added for that (in `SSGRoute/powHomRepDefs.lean`): `powHomRep`, the `H⁰`-slot
coefficient map `ℤ → A`, `1 ↦ a`, for an arbitrary `Coeff`-linear `G`-representation.  Its
definition (and every use in this file) needs the standard instance fix
`attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass …`
together with `attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module`, cf.
`E2_STATUS.md`; without it `a • m` resolves to `ULift.smulLeft` and *every* elementwise
computation fails.

Also on disk (delegated, axiom-clean, importable):

* `Work.SSGRoute.cyclicNormCriterion_rep` (`SSGRoute/cyclicNormCriterion_rep.lean`): the cyclic
  norm criterion `a ∪ δh = 0 ↔ a ∈ N(A)` for `G` cyclic of order `p` and an *arbitrary*
  `Coeff`-representation `A`;
* `Work.SSGRoute.hilbert90_localUnitsRep` (`SSGRoute/hilbert90_localUnitsRep.lean`): Hilbert 90,
  `H¹(N, L_wˣ) = 0`, for any subgroup `N` of the decomposition group — the hypothesis of the
  general-level criterion below;
* `Work.SSGRoute.normCriterion_quotient` (`SSGRoute/normCriterion_quotient.lean`): the
  **general-level** criterion: for `N ⊴ G` with `G ⧸ N` cyclic of order `p`, `H¹(N,A) = 0` and
  `h ∈ H¹(G,𝔽_p)` inflated from `G ⧸ N` (so `N = ker h`), `a ∪ δh = 0` iff `a` is the
  `G ⧸ N`-norm `∑_{x : G ⧸ N} out x · b` of an `N`-fixed `b`.  (The hypothesis `H¹(N,A) = 0` is
  essential: without it inflation `H²(G ⧸ N, A^N) → H²(G,A)` is not injective and the statement
  is *false*, e.g. `G = ℤ/4`, `N = ℤ/2`, `A = ℤ/2` trivial, `a = 1`.)
* `Work.SSGRoute.exists_level_normGroup_eq_of_index_prime`
  (`SSGRoute/exists_level_normGroup_eq_of_index_prime.lean`): for `F = Q.adicCompletion K`, every
  subgroup `U ≤ Fˣ` of index `p` is `N_{E/F}Eˣ` for a finite Galois `E/F` of degree `p` — the
  "existence + norm-group correspondence" half of local CFT at index `p` (uses
  `NK.NUV2.Final.nonempty_kernelCondition_of_L7`, `normIndex_adicCompletion`,
  `existenceTheorem_adicCompletion`).

### The remaining path, precisely

1. **The general-level assembly** (mechanical, from `normCriterion_quotient`): at any level
   `L ⊇ K`, `w' ∣ w`, `h ≠ 0` in `H¹(D_{w'},𝔽_p)`, the level pairing of `pushClass_lde p K_wˣ φ`
   vanishes iff `ι(φ 1) ∈ N_{E'/k_v}(E'ˣ)`, `E' = L_{w'}^{ker h}` (degree `p` over `k_v = L_{w'}^{D_{w'}}`).
   Ingredients: `levelPair_pushClass_bridge`, the identification `ι(φ 1) = a` with the
   `H¹(N,L_{w'}ˣ) = 0` from `hilbert90_localUnitsRep`, and the identification `A^N = E'ˣ`,
   `A^{D_{w'}} = k_vˣ`, `∑_{x : D_{w'}/N} out x · b = N_{E'/k_v}(b)`.
2. **Clause (i), base case.**  `y ≠ 0` in `Ext¹_{D_w}(𝔽_p, K_wˣ)` is `a ∈ k_vˣ/k_vˣ^p`, `a ≠ 0`;
   by `exists_level_normGroup_eq_of_index_prime` there is an index-`p` subgroup `U ≤ k_vˣ` with
   `a ∉ U` and a degree-`p` `E/k_v` with `N_{E/k_v}Eˣ = U`; one then needs a *global* level
   `L ⊇ K` (Galois over `k`) with `E ⊆ L_{w'}` and `w' ∣ w` — this is the one genuinely missing
   input, "every finite local extension is the completion of a finite global one" (it follows from
   the surjectivity of `G_k → G_{k_v}`, or from the localisation `(k^{ab})_{w'} = k_v^{ab}`, which
   in turn is the local–global compatibility that `DESIGN_EXT.md` §2 records as *absent from NK*).
   The workspace's `Work.SSGRoute.classField_exists_ramified` (global existence at prime index)
   plus weak approximation is the natural route.
3. **Clause (ii), base case.**  By the general-level assembly, clause (ii) reduces to
   `N_{E'/k_v}E'ˣ ⊊ k_vˣ` for the (given) level's cyclic degree-`p` subfields `E'`, which is the
   *norm index theorem* `[k_vˣ : N_{E'/k_v}E'ˣ] = [E':k_v] = p` (`Commons.…abelian_local_norm_index_at_base`,
   `NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`) transported to the
   `localUnitsRep`/`Rep.norm` vocabulary.
4. **General finite `p`-torsion `M`:** dévissage over `p`-groups, as in E5/E6, using the base case
   and the `Ext`-exact sequences of `PTDefs`, plus counting
   (`local_pTorsion_card`, `eb_loc_card`, `extH_localUnits_generator`) to turn two injections into
   perfectness.  The archimedean places are handled separately: `D_w` has order `≤ 2`, both clauses
   are trivial for odd `p`, and for `p = 2` the target is `Br(ℂ/ℝ) = ℤ/2`.

## What still has to be proved (the remaining, arithmetic part of E7b)

The statement is *true*; its proof needs the following chapter, none of which exists in the
workspace yet:

1. **Ext ↔ cohomology.**  `Extⁿ_G(ℤ, A) ≅ Hⁿ(G,A)` in the `PTExt` vocabulary.  Per the project
   lead: do this through `ProjectiveResolution.extEquivCohomologyClass` / `Ext.extMk` with the *bar
   resolution*, **not** through `groupCohomologyIsoExt` (the `HasExt` instance that the latter
   resolves is not defeq to `PTDefs.hasExt`, see `PT/PT_ext_cohomology.lean`).  Needed to import
   NK's `H¹`/`H²` theorems into this vocabulary.
2. **The coefficient sequence.**  For `M` killed by `p`, the Grothendieck/5-term sequence
   `0 → H¹(D, Hom(M, Lˣ)) → Ext¹_D(M, Lˣ) → H⁰(D, Ext¹_ℤ(M, Lˣ)) → H²(D, Hom(M, Lˣ)) → …`, together
   with Hilbert 90 (`H¹(D, Lˣ) = 0`) and `Ext¹_ℤ(M, Lˣ) = Hom(M, Lˣ/pLˣ)`.
   The *base case* `M = 𝔽_p` (trivial coefficients) is the long exact sequence of
   `0 → ℤ --p--> ℤ → ℤ/p → 0` in `Rep Coeff G` in the first variable: with Hilbert 90,
   `H¹(G,X) = Ext¹_G(ℤ,X) = 0`, and then
   `Ext¹_G(𝔽_p, X) ≃+ H⁰(G,X) / p·H⁰(G,X)`
   This base case is **proved** in `SSGRoute/ext_zmod_prime_iso_corrected.lean`
   (`Work.SSGRoute.ext_zmod_prime_iso_corrected`), and `local_duality_ext_base_source` below
   specialises it to the E7b data (`X = K_wˣ`, `G = D_w`).  Warning recorded there: the quotient
   must be by the *range of multiplication by `p`* inside `H⁰`; writing `p • ⊤` on `Submodule`
   picks up the *additive* `nsmul` of the submodule lattice (whose addition is `⊔`), which gives
   `⊤` and makes the statement false.  The coefficient sequence itself is available in the
   workspace as `SSGRoute.Phi1.coeffSES` with `SSGRoute.Phi1.coeffSES_shortExact`.
3. **Finite-level local Tate duality.**  `H¹(D,M) × H¹(D, M^∨(1)) → H²(D, Lˣ) = ℤ/|D|` is perfect,
   plus the local Euler characteristic (equality of the two `H¹`-dimensions).  For `𝔽_p`-coefficients
   this is the perfectness of the Kummer pairing `k_vˣ/p × Hom(G_{k_v}, μ_p) → μ_p`, i.e. local
   class field theory (`NK.LocalCFT`, `NK.NUV2.kernelCondition_all`, and the cyclic criterion
   `NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic`).
4. **Dévissage** over `p`-groups (as in E5/E6) reducing a general finite `p`-torsion `M` to the
   rank-one case, plus the Sylow descent that produces the detection at all levels (clause (i)).

## State of play and the precise remaining work (2026-09-27)

After the additions above, the remaining content of E7b is:

* **(A) The arithmetic input, in group cohomology.**  For the base case `C = K_wˣ` (or any module of
  units) one needs: for `0 ≠ φ ∈ H⁰(D_w, K_wˣ)/p` and any level `L ⊇ K` with `p ∣ |D_{w'}|`, there is
  a class `χ ∈ H¹(D_{w'}, 𝔽_p)` with `⟨φ, χ⟩ ≠ 0` (clause (i)'s detection), and dually every
  `p`-torsion functional `H¹(D_{w'},𝔽_p) → H²(D_{w'},L_{w'}ˣ)` is realised (clause (ii)).  With
  `levelPair_pushClass_bridge` and `pushClass_surjective` this is *exactly* the statement that the
  Kummer pairing `k_vˣ/p × H¹(D_{w'},𝔽_p) → H²(D_{w'},L_{w'}ˣ)` is perfect, i.e. the classical
  "`a ∪ δχ = 0` iff `a` is a norm" for the cyclic subextensions cut out by `χ`
  (`NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic`), together with the local existence theorem
  (all index-`p` norm subgroups arise, `NK.LocalCFT` / `NK.NUV2.kernelCondition_all`).
* **(B) The bridge.**  `SSGRoute.Phi1.ExtGroupCohomologyBridge` (naturality + compatibility with
  connecting maps) is the packaging of node `E0b` used by `levelPair_pushClass_bridge`.  Its *bare*
  half is on disk (`SSGRoute/e0b_bridge.lean`, used by `hilbert90_localUnits_extH`); the naturality
  and `δ`-compatibility clauses still have to be assembled.  Note the coefficient-sequence case of
  `δ`-compatibility can be attacked directly in the inhomogeneous cochain model.
* **(C) Levels are not the base level.**  The pairing *at the base level* `L = K` (where `f = id`,
  and `ι` is forced to be the canonical local embedding `localAlgebraMapUnits w w hw`) is in general
  degenerate *in the `y` variable* whenever `p ∤ |D_w|`, e.g.`D_w = 1` where `Ext¹(𝔽_p, k_vˣ) = k_vˣ/k_vˣ^p ≠ 0`
  but `H¹(1, 𝔽_p) = 0`.  Hence clause (i) is genuinely a statement about *all* levels: for `y ≠ 0`
  one must exhibit a level `L ⊇ K` (a number field with a place `w' ∣ w` whose decomposition group
  `D_{w'}` carries a suitable character) that detects `y`.  The workspace's global-lane tools
  (`Work.SSGRoute.classField_exists_ramified`, which realises any finite-index open subgroup of
  `C_K` as a norm class subgroup, and `NK.CFTLib.Existence.exists_cyclotomicExtension_galois_isCyclic`)
  are the natural means of *constructing* that level; the arithmetic via Artin reciprocity is the
  same input as (A).
* **(D) Dévissage** over finite `p`-torsion `M` (the local analogue of `E5`/`E6`), and the counting
  that converts two injections into perfectness.

**Technical debt (formal, no mathematics).**  Two `Rep`-morphism extensionality facts are needed
whenever one wants to conclude that two coefficient maps `ι, ι'` with the same values on
`Additive.ofMul u` are equal (`ι = 𝟙` at the base level, i.e. that the E7b datum `ι` is canonical):
`Rep.hom_ext` followed by `Representation.IntertwiningMap.ext` gets stuck on the
`ULift.module`/`hV2` instance diamond, exactly as in `Rep.nsmul_id_eq_zero` (where `letI := X.hV2`
fixes it).  Also on disk for that purpose: `Work.SSGRoute.localAlgebraMapUnits_self`
(`SSGRoute/localAlgebraMapUnits_self.lean`), the fact that the canonical local embedding at the same
place is the identity on units (it needs `NK.LocalInputs.Degree.adicCompletionMap_self` in the finite
case and a density argument in the archimedean case, cf. the private `completionMap_self` of
`NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self`).

## Assets available in the workspace for this proof (checked 2026-09-26)

* `Work.SSGRoute.mapExactFunctor_id` (`SSGRoute/mapExactFunctor_id.lean`, proved): the missing
  Mathlib identity law `x.mapExactFunctor (𝟭 _) = x`, hence (here) `extRes_id`; with it the siblings
  `Work.SSGRoute.extHMap_id` (`SSGRoute/extHMap_id.lean`) and `Work.SSGRoute.levelPair_id`
  (`SSGRoute/levelPair_id.lean`) are proved, closing the base-level specialisation of the pairing.
* E0b progress (siblings, in flight): `SSGRoute/e0b_core_ext.lean`,
  `SSGRoute/projRes_homologyAddEquiv_extMk.lean` are sorry-free; `E0bDefs.lean`,
  `extH_groupCohomology_addEquiv.lean`, `extH_groupCohomology_bridge_nonempty.lean`,
  `groupCohomologyIsoExt_natural_coefficient.lean` are in progress.
* `SSGRoute/phi1_defs.lean`: `unitMulByP`, `unitToZMod`, `coeffSES`, `coeffSES_shortExact` — the
  coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` in `Rep Coeff G`.
* `Work.SSGRoute.ext_zmod_prime_iso_corrected` (`SSGRoute/ext_zmod_prime_iso_corrected.lean`,
  proved): the base-case algebra `Ext¹_G(𝔽_p,X) ≃+ H⁰(G,X)/p·H⁰(G,X)` for `H¹(G,X) = 0`, used here
  as `local_duality_ext_base_source`.  (Its `ext_zmod_prime_iso_refutation.lean` records why the
  naive `p • ⊤` on `Submodule` is wrong: that is the *additive* nsmul of the lattice, so it is `⊤`.)
* `SSGRoute/ext_corestriction.lean`: `ext_mapExactFunctor_comp_functor_aux`,
  `ext_mapExactFunctor_naturality_aux`, `extCor`, `ext_corestriction` — corestriction on `Ext`,
  which is the input for the Sylow descent in clause (i).
* `Ext ↔ group cohomology` (E0b) is being built by a sibling; the project lead's route is
  `ProjectiveResolution.extEquivCohomologyClass` / `Ext.extMk` with the bar resolution.

Known formal gap when reducing clause (i)/(ii) to the *base level* `L = K`, `w' = w`, `f = id`:
`x.mapExactFunctor (𝟭 C) = x` was missing from Mathlib and is now proved in the workspace
(`Work.SSGRoute.mapExactFunctor_id`), giving `extRes_id` below and hence the base-level
specialisations `extHMap_id`, `levelPair_id` (`levelPair_id_of_extRes_id` records the reduction,
and the unconditional forms are proved in the sibling files `SSGRoute/extHMap_id.lean`,
`SSGRoute/levelPair_id.lean`).  Note that this is *not* on the critical path: the interesting
pairings of E7b live at levels with `D_{w'} ⊋ D_w`, where `f ≠ id` and `extRes f x` can be kept
un-simplified.

## SESSION 4 (2026-09-27): the exact reduction of E7b to arithmetic

The following is the *complete* reduction; it names precisely what is still missing.

### The pairing is the norm criterion (done here)

`Work.SSGRoute.normCriterion_quotient` (proved, `SSGRoute/normCriterion_quotient.lean`) plus the
`powHomRep` conversion give, for `M = 𝔽_p` and a level `L ⊇ K`, `w' ∣ w`, `N ⊴ D_{w'}` with
`D_{w'} ⧸ N` cyclic of order `p`, and a non-zero character `h` inflated from `D_{w'} ⧸ N`:

  `levelPair f ι (pushClass_lde p K_wˣ φ) h = 0  ↔  a ∈ N_{E'/k_v}(E'ˣ)`,

where `a = ι(φ 1) ∈ k_vˣ = (K_wˣ)^{D_w}` and `E' = L_{w'}^N` is the fixed field of `N`
(`levelPair_trivial_eq_zero_iff_normB` below, the "general level" form of the criterion; the
`D_{w'}`-cyclic form is `levelPair_trivial_eq_zero_iff_norm`).  No Kummer theory, no explicit
`inv` map and no Brauer-group computation enters here: the criterion *is* the Kummer/norm-residue
duality in the norm-group form.

Consequences (this is the whole content of E7b at `M = 𝔽_p`):

* write `A = k_vˣ/k_v^{×p}` (so `Ext¹_{D_w}(𝔽_p, K_wˣ) ≅ A` by `local_duality_ext_base_source_uncond`)
  and `B_L = H¹(D_{w'}, 𝔽_p) = Hom(D_{w'}^{ab}, ℤ/p) = (D_{w'}^{ab}/p)^∨` at the level `L`;
* the criterion says that for `h ≠ 0` the functional `A ∋ y ↦ levelPair y h` has kernel
  `N_{E'_h}(E'_hˣ)/k_v^{×p}`, of index `p`; the pairing is additive in `h`
  (`levelPair_add_h`), so `h ↦ (the scalar making the functional canonical)` is a homomorphism
  `D_{w'}^{ab}/p → (ℤ/p)^* = 1`, hence the functional is *canonically* the one induced by the dual
  of `D_{w'}^{ab}/p ↪ A^∨` — i.e. by the local Artin map;
* **clause (ii)** is therefore the surjectivity of `A ↠ D_{w'}^{ab}/p`, i.e. local CFT
  (`Gal(k_v)^{ab} ↠ Gal(L_{w'}/k_v)^{ab}`);
* **clause (i)** is the joint injectivity of `A → ∏_L (D_{w'}^{ab}/p)^∨`, i.e. the statement that
  the intersection over all levels of the norm groups is `k_v^{×p}`.  Since
  `∩_E N_{E/k_v}(Eˣ) = k_v^{×p}` over the degree-`p` cyclic `E/k_v` (local CFT: every index-`p`
  subgroup of `k_vˣ` is a norm group, `Work.SSGRoute.exists_level_normGroup_eq_of_index_prime`),
  it suffices that **every** degree-`p` cyclic extension `E/k_v` be contained in `L_{w'}` for some
  global `L ⊇ K` — the local–global compatibility `(k^{ab})_v = k_v^{ab}` in its degree-`p` form.

### What is delegated (parallel children)

* `Work.SSGRoute.decompK_restrict_exists` — the canonical `f : D_{w'} →* D_w` (restriction) with
  `hf`.  (`SSGRoute/decompK_restrict_exists.lean`)
* `Work.SSGRoute.localUnitsMap_exists` — the canonical `ι : K_wˣ → L_{w'}ˣ` with `hι`.
  (`SSGRoute/localUnitsMap_exists.lean`)
* `Work.SSGRoute.exists_H1_inflated_ne_zero` — a non-zero class of `H¹(D_{w'}⧸N, 𝔽_p)` whose
  inflation to `H¹(D_{w'}, 𝔽_p)` is still non-zero (so that the character `h` of the criterion can
  be produced at a level returned by the arithmetic input).
  (`SSGRoute/exists_H1_inflated_ne_zero.lean`)
* `Work.SSGRoute.exists_level_normGroup_not_mem_of_not_pthPower` — local CFT at a completion:
  `a ∉ (Fˣ)^p ⟹ ∃ E/F` cyclic of degree `p` with `a ∉ N_{E/F}(Eˣ)`.
  (`SSGRoute/exists_level_normGroup_not_mem_of_not_pthPower.lean`)
* `Work.SSGRoute.exists_level_quotientNorm_avoids` — **the arithmetic input of clause (i)**: for
  `a ∈ k_vˣ` which is not a `p`-th power *of a `k_v`-element* (`ha` below), there are a level
  `L ⊇ K`, a place `w' ∣ w` and `N ⊴ D_{w'}` with `D_{w'} ⧸ N ≅ ℤ/p` whose quotient-norm
  condition (the right-hand side of the criterion) *fails* at the image of `a` in `L_{w'}ˣ`.
  This is the Grünwald/weak-approximation step (every finite cyclic `p`-extension of `k_v` is
  contained in `L_{w'}` for some global `L ⊇ K`); it is the single genuinely missing arithmetic
  input of clause (i) at `M = 𝔽_p`.  (`SSGRoute/exists_level_quotientNorm_avoids.lean`)

### Clause (ii) at `M = 𝔽_p`: the reduction (analysis)

Write `A = Ext¹_{D_w}(𝔽_p, K_wˣ) ≅ k_vˣ/k_v^{×p}` (so `A` is an `𝔽_p`-vector space),
`B = H¹(D_{w'}, 𝔽_p) = (D_{w'}^{ab}/p)^∨` and `T = H²(D_{w'}, L_{w'}ˣ)`, whose `p`-torsion is
one-dimensional over `𝔽_p` (`T[p] ≅ ℤ/p`, cf. `Work.SSGRoute.local_pTorsion_card` and its level
companions).  The pairing `P : A × B → T` is additive in each variable (`levelPair_add`,
`levelPair_add_h`) and takes values in `T[p]`.  Then:

* the transpose `P^* : B → A^∨`, `h ↦ P(·, h)`, is **injective**: `P(·,h) = 0` says
  `k_vˣ ⊆ N_{E'_h}(E'_hˣ)`, impossible for the proper index-`p` subgroup cut out by `h ≠ 0`
  (norm index theorem, local CFT);
* hence the map `Φ : A → B^∨ = Hom(B, T[p])`, `y ↦ P(y, ·)`, is **surjective** — this is pure
  finite-dimensional `𝔽_p`-linear algebra (`Φ` surjective ⟺ `Φ^*` injective, rank-nullity), and it
  is *exactly* clause (ii): every `p`-torsion functional `lam : B → T` is `Φ(y)` for some `y`.

So clause (ii) at `M = 𝔽_p` needs no Kummer-theoretic computation of the pairing's *values*: the
vanishing pattern (the norm criterion) plus additivity plus `T[p] ≅ ℤ/p` determine everything.
The formal ingredients missing are `T[p] ≅ ℤ/p` at an arbitrary level and the "properness" of the
norm group `N_{E'_h}` (for `h ≠ 0`).

### The parallel lane in the workspace (found 2026-09-27)

A colleague is attacking the *same* statement in parallel, and their lane contains two assets that
this file should use:

* `Work.SSGRoute.local_duality_ext_realization_of_detection`
  (`SSGRoute/local_duality_ext_realization_of_detection.lean`, **sorry-free**) — **clause (ii)
  from detection, for arbitrary finite `p`-torsion `M`**: given the level data, `p ∣ |D_{w'}|` and
  the hypothesis
  `hdet : ∀ h ≠ 0, ∃ y, levelPair f ι y h ≠ 0`,
  it produces `y` with `levelPair f ι y · = lam` for every `p`-torsion `lam`.  The proof is the
  finite duality `LinearMap.flip_injective_iff₂` after identifying the `p`-torsion of
  `H²(D_{w'}, L_{w'}ˣ)` with `ℤ/p` (`Work.SSGRoute.local_pTorsion_card`) and using
  `Work.SSGRoute.local_duality_ext_extH_finite`.
* `Work.SSGRoute.levelPair_coeff_naturality` and `Work.SSGRoute.detect_of_quotient`
  (`SSGRoute/local_duality_ext_detect_h.lean`, sorry-free) — naturality of the pairing in the
  coefficient module, the engine of any dévissage.
* `Work.SSGRoute.detect_trivial_cyclic_of_norm_notMem` (same file, sorry-free) — the `M = 𝔽_p`
  detection at a *cyclic* level of order `p`, from `levelPair_trivial_eq_zero_iff_norm` (this file)
  and the norm-index properness input.

Their lane's `Work.SSGRoute.local_duality_ext_in` (`SSGRoute/local_duality_ext_in.lean`) has
*exactly this file's statement* (up to the `_in` suffix) and assembles it as
`⟨local_duality_ext_detect_levels, local_duality_ext_realization_of_detection +
local_duality_ext_detect_h⟩`; both of those two inputs still carry a `sorry`.

**The obstruction to the general `M` (recorded by that lane, and confirmed by inspection).**
The dévissage of clause (i)/(ii) to the base case `M = 𝔽_p` *fails*: for `M` irreducible over
`𝔽_p[D_w]` of `𝔽_p`-dimension `≥ 2` (possible when `D_w` has a quotient of order coprime to `p`,
e.g. `p = 2`, `D_w = C₃`) there is no proper nonzero subquotient of `M` to induct on, so the
dévissage hypothesis is inert and the statement must be proved outright for such `M`.  That case
needs local Tate duality for *arbitrary* finite `p`-torsion coefficients (Milne, *ADT*, I.1.8 /
I.2.1, the form used by I.2.3), which is not in this workspace.  For the *twisted* 1-dimensional
`M = 𝔽_p(χ)` the same chapter is needed in the twisted form; this is the additional node the
parallel lane names.

### Still to be done (not delegated)

* the **assembly** of clause (i) at `M = 𝔽_p` from `exists_level_quotientNorm_avoids` + the three
  formal children + the criterion (see the docstring of `clause_i_trivial_of_arithmetic` below);
* clause (ii) at `M = 𝔽_p`: the "value" form of the criterion (the character argument above) plus
  local CFT (`k_vˣ/p ≅ Gal(k_v)^{ab}/p`, `D_{w'}^{ab}/p ≅ k_vˣ/N_{L_{w'}}`);
* **dévissage** from `M = 𝔽_p` to an arbitrary finite `p`-torsion `M : Rep Coeff (K ≃ₐ[k] K)`:
  filter `M` by `𝔽_p[Gal(K/k)]`-submodules with simple quotients (which may be *twisted*, i.e.
  `M = 𝔽_p(χ)` for a character `χ` of `Gal(K/k)`), and use the `Ext`-exact sequences of `PTDefs`
  (equivalently, the analogue of the `E5`/`E6` dévissage of the global lane, with `D_w` in place
  of `G` and Sylow descent);
* the **archimedean** places: `|D_w| ≤ 2`, `p` odd trivial, `p = 2` has
  `H²(ℤ/2, ℂˣ) = Br(ℂ/ℝ) = ℤ/2` and the pairing is the quaternion pairing; a direct computation.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-! ## The pairing calculus for `levelPair` -/

section Calculus

variable {G H : Type} [Group G] [Group H]

/-- Associativity of `Ext.comp` when the second factor has degree `0`: the "first degree zero"
companion of Mathlib's `Ext.comp_assoc_of_second_deg_zero` / `comp_assoc_of_third_deg_zero`. -/
theorem comp_assoc_of_first_deg_zero {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {X Y Z T : C} {a₂ a₃ : ℕ} (α : Abelian.Ext X Y 0) (β : Abelian.Ext Y Z a₂)
    (γ : Abelian.Ext Z T a₃) :
    (α.comp β (zero_add a₂)).comp γ rfl = α.comp (β.comp γ rfl) (zero_add (a₂ + a₃)) := by
  exact Abelian.Ext.comp_assoc α β γ (zero_add a₂) rfl (by omega)

/-- **The identity case of `extRes`**: change of group along the identity (with the identity
coefficient map) is the identity on `Ext`.  Uses the Mathlib-gap lemma
`Work.SSGRoute.mapExactFunctor_id` (`x.mapExactFunctor (𝟭 _) = x`), since
`Rep.resFunctor (MonoidHom.id G) = 𝟭 _` holds by `rfl`. -/
theorem extRes_id {G : Type} [Group G] {X Y : Rep.{0} Coeff G} {n : ℕ}
    (x : Abelian.Ext.{0} X Y n) : extRes (MonoidHom.id G) x = x := by
  rw [show extRes (MonoidHom.id G) x = x.mapExactFunctor (𝟭 (Rep.{0} Coeff G)) from rfl]
  exact mapExactFunctor_id x

/-- **Compatibility of the level pairing with inflation.**  If `h = extHMap f (id _) h₀` is the
class at the level `H` obtained by inflation along `f : H →* G` from the class `h₀` at the level
`G`, then the level pairing at `H` of `x` with `h` is the inflation of the Yoneda pairing of `x`
with `h₀` at the level `G`.  (In the intended application `G = D_w` and `H = D_{w'}` for `w' ∣ w`,
so the pairing at a level is the restriction of the pairings at all higher levels.) -/
theorem levelPair_extHMap {G H : Type} [Group G] [Group H] (f : H →* G) {M A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h₀ : extH M s) :
    levelPair f ι x (extHMap f (CategoryTheory.CategoryStruct.id (Rep.res f M)) h₀) =
      extHMap f ι (yonedaPair x h₀) := by
  simp only [levelPair, extHMap, yonedaPair, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.comp_mk₀_id]
  exact comp_assoc_of_first_deg_zero _ _ _

/-- `extRes` (change of group on `Ext`) is additive. -/
theorem extRes_add (f : H →* G) {X Y : Rep.{0} Coeff G} {n : ℕ}
    (x x' : Abelian.Ext.{0} X Y n) : extRes f (x + x') = extRes f x + extRes f x' := by
  simpa only [extRes] using Abelian.Ext.mapExactFunctor_add (Rep.resFunctor f) X Y n x x'

/-- `extRes` kills the zero class. -/
theorem extRes_zero (f : H →* G) {X Y : Rep.{0} Coeff G} {n : ℕ} :
    extRes f (0 : Abelian.Ext.{0} X Y n) = 0 := by
  simpa only [extRes] using Abelian.Ext.mapExactFunctor_zero (Rep.resFunctor f) X Y n

/-- `extHMap` (change of group plus coefficient map on `Hⁿ = Extⁿ(ℤ, ·)`) is additive. -/
theorem extHMap_add (f : H →* G) {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {n : ℕ} (y y' : extH A n) :
    extHMap f ι (y + y') = extHMap f ι y + extHMap f ι y' := by
  simp only [extHMap]
  rw [extRes_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

/-- `extHMap` kills the zero class. -/
theorem extHMap_zero (f : H →* G) {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {n : ℕ} : extHMap f ι (0 : extH A n) = 0 := by
  simp only [extHMap]
  rw [extRes_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

/-- **The level pairing is additive in the `Ext`-variable.** -/
theorem levelPair_add (f : H →* G) {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (x x' : Abelian.Ext.{0} M A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι (x + x') h = levelPair f ι x h + levelPair f ι x' h := by
  simp only [levelPair, extRes_add, Abelian.Ext.comp_add, Abelian.Ext.add_comp]

/-- The level pairing kills the zero `Ext`-class. -/
theorem levelPair_zero (f : H →* G) {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (h : extH (Rep.res f M) s) :
    levelPair f ι (0 : Abelian.Ext.{0} M A r) h = 0 := by
  simp only [levelPair, extRes_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

/-- **The level pairing is additive in the `Hˢ`-variable.** -/
theorem levelPair_add_h (f : H →* G) {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h h' : extH (Rep.res f M) s) :
    levelPair f ι x (h + h') = levelPair f ι x h + levelPair f ι x h' := by
  simp only [levelPair, Abelian.Ext.add_comp]

/-- The level pairing kills the zero `Hˢ`-class. -/
theorem levelPair_zero_h (f : H →* G) {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r) :
    levelPair f ι x (0 : extH (Rep.res f M) s) = 0 := by
  simp only [levelPair, Abelian.Ext.zero_comp]

/-- **Naturality of the level pairing in the coefficient morphism.**  Composing the coefficient
map `ι : K_wˣ → L_{w'}ˣ` with a further map `ι'` postcomposes the pairing value with `ι'`.  Together
with `levelPair_extHMap` this says that the level pairings form a compatible system as the level
grows. -/
theorem levelPair_comp (f : H →* G) {M A : Rep.{0} Coeff G} {B B' : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) (ι' : B ⟶ B') {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h : extH (Rep.res f M) s) :
    levelPair f (ι ≫ ι') x h =
      (levelPair f ι x h).comp (Abelian.Ext.mk₀ ι') (add_zero (s + r)) := by
  simp only [levelPair]
  rw [← Abelian.Ext.mk₀_comp_mk₀ ι ι']
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [← Abelian.Ext.comp_assoc, ← Abelian.Ext.comp_assoc] <;> omega

/-- **The base-level pairing, reduced to the identity case of `extRes`.**  Given
`extRes (MonoidHom.id G) x = x` — which is now proved unconditionally as `extRes_id` above, via
`Work.SSGRoute.mapExactFunctor_id` — the level pairing at the identity data is the Yoneda pairing.
The unconditional form is `Work.SSGRoute.levelPair_id` (`SSGRoute/levelPair_id.lean`); this
reduction records the one-line dependence on `extRes_id`. -/
theorem levelPair_id_of_extRes_id {G : Type} [Group G] {M A : Rep.{0} Coeff G} {r s : ℕ}
    (x : Abelian.Ext.{0} M A r) (h : extH M s)
    (hx : extRes (MonoidHom.id G) (X := M) (Y := A) x = x) :
    levelPair (MonoidHom.id G) (CategoryTheory.CategoryStruct.id A) x h = yonedaPair x h := by
  simp only [levelPair, yonedaPair]
  rw [hx]
  rw [show (x.comp (Abelian.Ext.mk₀ (CategoryTheory.CategoryStruct.id A)) (add_zero r)) = x from
    Abelian.Ext.comp_mk₀_id x]

/-- **The level pairing, as a bilinear map**: for fixed `x`, `h ↦ levelPair f ι x h` is an additive
homomorphism.  This is the object the realisation clause of E7b is about. -/
noncomputable def levelPairFunctional (f : H →* G) {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r) :
    extH (Rep.res f M) s →+ extH B (s + r) where
  toFun := fun h => levelPair f ι x h
  map_zero' := levelPair_zero_h f ι x
  map_add' := levelPair_add_h f ι x

@[simp] theorem levelPairFunctional_apply (f : H →* G) {M A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h : extH (Rep.res f M) s) : levelPairFunctional f ι x h = levelPair f ι x h := rfl

/-- **The realisation clause of E7b, reformulated.**  For the data of E7b, the assertion
"every `p`-torsion functional `lam` is `levelPair f ι y ·` for some `y`" says exactly that `lam`
lies in the range of the linear map `x ↦ levelPairFunctional f ι x`. -/
theorem range_levelPairFunctional {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    {r s : ℕ} (f : H →* G) (ι : Rep.res f A ⟶ B)
    (lam : extH (Rep.res f M) s →+ extH B (s + r)) :
    (∃ x : Abelian.Ext.{0} M A r, levelPairFunctional f ι x = lam) ↔
      ∃ x : Abelian.Ext.{0} M A r, ∀ h, levelPair f ι x h = lam h := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun h => by rw [← hx]; rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, AddMonoidHom.ext (fun h => by rw [levelPairFunctional_apply, hx h])⟩

end Calculus

/-! ## `Ext` of a `p`-torsion module is `p`-torsion

These are the `p`-torsion facts that every `p`-adic argument about the pairing uses: both variables
of `Ext` are "additive", so a module killed by `p` kills the `Ext`-groups it occurs in. -/

section PTorsion

variable {G : Type} [Group G]

/-- A morphism of representations which is pointwise `0` is `0`.  (`Rep.nsmul_hom`,
`Rep.zero_hom` and `Representation.IntertwiningMap` pointwise lemmas; the `letI` pins the module
structure carried by the representation, avoiding the `ULift.module`/`hV2` instance diamond.) -/
theorem Rep.nsmul_id_eq_zero {X : Rep.{0} Coeff G} (p : ℕ) (hX : ∀ x : X, p • x = 0) :
    (p : ℕ) • (CategoryTheory.CategoryStruct.id X) = 0 := by
  letI := X.hV2
  refine Rep.hom_ext ?_
  rw [Rep.nsmul_hom, Rep.zero_hom]
  refine Representation.IntertwiningMap.ext ?_
  ext x
  rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.coe_nsmul,
    Pi.smul_apply, Representation.IntertwiningMap.toLinearMap_apply]
  show p • ((𝟙 X : X ⟶ X) x) = 0
  rw [Rep.id_apply]
  exact hX x

/-- **`Ext` with `p`-torsion coefficients is killed by `p`** (second-variable form): if the
`G`-module `A` satisfies `p • a = 0` for all `a`, then `p • h = 0` for all
`h ∈ Hⁿ(G, A) = Extⁿ_G(ℤ, A)`. -/
theorem ext_nsmul_p_torsion (p : ℕ) {A : Rep.{0} Coeff G}
    (hA : ∀ a : A, p • a = 0) {n : ℕ} (h : extH A n) : p • h = 0 := by
  have hzero := Rep.nsmul_id_eq_zero (G := G) p hA
  have key : ∀ k : ℕ, h.comp (Abelian.Ext.mk₀ (k • (CategoryTheory.CategoryStruct.id A)))
      (add_zero n) = k • h := by
    intro k
    induction k with
    | zero => rw [zero_nsmul, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, zero_nsmul]
    | succ k ih =>
        rw [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, ih, Abelian.Ext.comp_mk₀_id,
          succ_nsmul]
  rw [← key p, hzero, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

/-- **`Ext` of a `p`-torsion module is killed by `p`** (first-variable form): if the `G`-module `X`
satisfies `p • x = 0` for all `x`, then `p • h = 0` for all `h ∈ Extⁿ_G(X, Y)`. -/
theorem ext_nsmul_p_torsion_left (p : ℕ) {X Y : Rep.{0} Coeff G}
    (hX : ∀ x : X, p • x = 0) {n : ℕ} (h : Abelian.Ext X Y n) : p • h = 0 := by
  have hzero := Rep.nsmul_id_eq_zero (G := G) p hX
  have key : ∀ k : ℕ, (Abelian.Ext.mk₀ (k • (CategoryTheory.CategoryStruct.id X))).comp h
      (zero_add n) = k • h := by
    intro k
    induction k with
    | zero => rw [zero_nsmul, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp, zero_nsmul]
    | succ k ih =>
        rw [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.add_comp, ih, Abelian.Ext.mk₀_id_comp,
          succ_nsmul]
  rw [← key p, hzero, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]

end PTorsion

/-! ## The `p`-torsion hypothesis of clause (ii) is automatic

In clause (ii) of E7b the functional `lam` is assumed to be `p`-torsion.  Since `M` is `p`-torsion,
`H¹(D_{w'}, M)` is `p`-torsion by `ext_nsmul_p_torsion`, so this hypothesis is implied by the
additivity of `lam`: `p • lam h = lam (p • h) = lam 0 = 0`.  Recorded for the assembly. -/

theorem p_smul_lam_eq_zero {H : Type} [Group H] {P Q : Type} [AddCommGroup Q]
    (p : ℕ) {A : Rep.{0} Coeff H} (hA : ∀ a : A, p • a = 0) {n : ℕ}
    (lam : extH A n →+ Q) (h : extH A n) : p • lam h = 0 := by
  rw [← map_nsmul, ext_nsmul_p_torsion p hA h, map_zero]

/-! ## The base case `M = 𝔽_p`: the source of the pairing

The trivial `Gal(K/k)`-module `𝔽_p` restricted to `D_w` is the trivial `D_w`-module, and for it the
source of the E7b pairing is computed by the coefficient sequence
`0 → ℤ --p--> ℤ → 𝔽_p → 0` of `SSGRoute.Phi1.coeffSES`: with Hilbert 90
(`H¹(D_w, K_wˣ) = 0`, the hypothesis `hH90`) one has

`Ext¹_{D_w}(𝔽_p, K_wˣ) ≃+ H⁰(D_w, K_wˣ) / p·H⁰(D_w, K_wˣ)`,

i.e. the `k_vˣ/p` of the design (since `H⁰(D_w, K_wˣ) = k_vˣ` is the fixed field's units).  This is
`Work.SSGRoute.ext_zmod_prime_iso_corrected` (proved in `SSGRoute/ext_zmod_prime_iso_corrected.lean`)
specialised to the E7b data.  Note that the quotient must be by the *range of multiplication by `p`*
inside `H⁰`: the naive `p • ⊤` on `Submodule` is the additive `nsmul` of the lattice, which is `⊤`. -/
theorem local_duality_ext_base_source (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (hH90 : Subsingleton (extH (localUnitsK (k := k) w) 1)) :
    Nonempty (Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1 ≃+
      (extH (localUnitsK (k := k) w) 0 ⧸
        ((Abelian.Ext.mk₀ (SSGRoute.Phi1.unitMulByP (decompK (k := k) w) p)).precomp
          (localUnitsK (k := k) w) (zero_add 0)).range)) :=
  ext_zmod_prime_iso_corrected p (localUnitsK (k := k) w) hH90

/-! ## Local Hilbert 90 in the `Ext` vocabulary

`NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_of_injective_ringAut` is Hilbert 90
for the units of a field under a *faithful* action (`H¹(G, Fˣ) = 0` whenever `G` acts on `Fˣ`
through an injective homomorphism into the ring automorphisms of `F`), and the local units
`K_wˣ` under the decomposition group `D_w = Gal(K_w/k_v)` are exactly of this shape:
`NK.HassePrinciple.localAutHom` is injective and `NK.HassePrinciple.localUnitsEquiv` is the
transported action.  `NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary` moves
the vanishing from `ℤ`-coefficients to the coefficient ring `Coeff = ULift ℤ` of `PTDefs`, and
`Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology` moves it from group
cohomology to `extH`.  The outcome is the local Hilbert 90 of the design, in the exact form in
which the base case of E7b (and node E7a) needs it. -/

theorem hilbert90_localUnits_extH (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K) :
    Subsingleton (extH (localUnitsK (k := k) w) 1) := by
  haveI : Fintype ↥(decompK (k := k) w) := Fintype.ofFinite _
  have h : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction (decompK (k := k) w)
      ((NK.GlobalCFT.Place.localField K w)ˣ)) 1) :=
    NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_of_injective_ringAut
      (G := decompK (k := k) w) (F := NK.GlobalCFT.Place.localField K w)
      (NK.HassePrinciple.localAutHom (K := k) (L := K) w)
      (NK.HassePrinciple.localAutHom_injective (K := k) (L := K) w)
      (fun σ u => by
        show NK.HassePrinciple.localUnitsEquiv (K := k) w σ u
          = Units.map ((NK.HassePrinciple.localAutHom (K := k) (L := K) w) σ).toMonoidHom u
        ext
        rw [NK.HassePrinciple.coe_localUnitsEquiv]
        rfl)
  exact Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology 1
    (decompK (k := k) w) (localUnitsK (k := k) w)
    (NK.HassePrinciple.subsingleton_groupCohomology_one_of_mulCoboundary Coeff
      (NK.HassePrinciple.mulCoboundary_of_subsingleton_groupCohomology_one h))

/-- **The E7b coefficient map `ι` is determined by its values on the local units.**  Any two
morphisms out of `localUnitsK w` which agree on `Additive.ofMul u` for every unit `u` of the local
field coincide.  (In E7b the hypothesis `hι` prescribes exactly those values, so the datum `ι` of
the statement is *canonical*.)  The two `letI`s pin the `Module Coeff` structures of the source and
the target, avoiding the `ULift.module`/`hV2` instance diamond.) -/
theorem localUnits_hom_ext (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    {B : Rep.{0} Coeff (decompK (k := k) w)}
    (ι ι' : localUnitsK (k := k) w ⟶ B)
    (h : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) = ι'.hom (Additive.ofMul u)) :
    ι = ι' := by
  letI := (localUnitsK (k := k) w).hV2
  letI := B.hV2
  refine Rep.hom_ext ?_
  refine Representation.IntertwiningMap.ext ?_
  ext x
  obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
  exact h u

/-- **The base-case source of E7b, unconditionally.**  With `H¹(D_w, K_wˣ) = 0` now available
(`hilbert90_localUnits_extH`), the source of the E7b pairing for the trivial module `𝔽_p` is
`H⁰(D_w,K_wˣ) / p·H⁰(D_w,K_wˣ) = k_vˣ / k_vˣ^p`, via
`Work.SSGRoute.ext_zmod_prime_iso_corrected`.  This is `local_duality_ext_base_source` with its
Hilbert 90 hypothesis discharged. -/
theorem local_duality_ext_base_source_uncond (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (w : NK.GlobalCFT.Place K) :
    Nonempty (Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1 ≃+
      (extH (localUnitsK (k := k) w) 0 ⧸
        ((Abelian.Ext.mk₀ (SSGRoute.Phi1.unitMulByP (decompK (k := k) w) p)).precomp
          (localUnitsK (k := k) w) (zero_add 0)).range)) :=
  local_duality_ext_base_source p k K w (hilbert90_localUnits_extH k K w)

/-! ## The base case of the local pairing: the class of the coefficient sequence

The base case of E7b pairs `Ext¹_{D_w}(𝔽_p, K_wˣ)` with `H¹(D_{w'}, 𝔽_p)`.  The source has a
canonical generator over `𝔽_p`: the class of the coefficient sequence
`0 → ℤ --p--> ℤ → 𝔽_p → 0` (`SSGRoute.Phi1.coeffSES`), pushed out along a `D_w`-map
`φ : ℤ → K_wˣ`, i.e. an element of `H⁰(D_w, K_wˣ) = k_vˣ`.  The two lemmas below compute the level
pairing on such a class, and rewrite its vanishing as a statement in group cohomology (modulo the
`Ext`/group-cohomology bridge `ExtGroupCohomologyBridge`), which is the interface at which the
local class field theory input (Kummer duality / the cyclic norm criterion
`NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic`) is consumed.  They are the local and
coefficient-agnostic counterparts of `E3Base.phiAt_pushClass_eq` / `E3Base.bridge_pairing_eq_zero_iff`
of the global lane, and specialise to the E7b data by
`G = decompK w`, `H = MulAction.stabilizer (L ≃ₐ[k] L) w'`, `A = localUnitsK w`,
`B = localUnitsRep k L w'`. -/

/-- The **pushout** of the coefficient sequence along a `G`-map `φ : ℤ → C`: the class of
`0 → C → E → 𝔽_p → 0` in `Ext¹_G(𝔽_p, C)`.  (Same definition as `E3Base.pushClass`; reproduced
here so that this file depends only on `PTDefs` and `phi1_defs`.) -/
noncomputable def pushClass_lde {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (C : Rep Coeff G)
    (φ : unitRep G ⟶ C) : Abelian.Ext (Rep.trivial Coeff G (ZMod p)) C 1 :=
  ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass).comp (Abelian.Ext.mk₀ φ) (add_zero 1)

section PushClassSpine

set_option backward.isDefEq.respectTransparency false

/-- **The `Ext`-algebra heart of the local base case.**  For a class `x = pushClass_lde p A φ` of the
coefficient sequence and a class `h ∈ H¹(H, 𝔽_p)` at a finer level `f : H →* G`, the level pairing
is the Yoneda product of `h` with the coefficient sequence *at the level `H`*, followed by the
coefficient map `res f φ ≫ ι : ℤ → B`.  Everything reduces to associativity of `Abelian.Ext.comp`
and the change-of-group law for `Ext` (`mapExactFunctor_extClass`). -/
theorem levelPair_pushClass {G H : Type} [Group G] [Group H] (p : ℕ) [Fact p.Prime]
    (f : H →* G) {A : Rep Coeff G} {B : Rep Coeff H} (ι : Rep.res f A ⟶ B)
    (φ : unitRep G ⟶ A)
    (h : extH (Rep.res f (Rep.trivial Coeff G (ZMod p))) 1) :
    levelPair f ι (pushClass_lde p A φ) h =
      (h.comp ((SSGRoute.Phi1.coeffSES_shortExact H p).extClass) rfl).comp
        (Abelian.Ext.mk₀ ((Rep.resFunctor f).map φ ≫ ι)) (add_zero (1 + 1)) := by
  have hext : ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass).mapExactFunctor
      (Rep.resFunctor f) = (SSGRoute.Phi1.coeffSES_shortExact H p).extClass := by
    rw [Abelian.Ext.mapExactFunctor_extClass]
  simp only [levelPair, pushClass_lde, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, hext,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- `pushClass_lde` is additive in the coefficient map `φ`. -/
theorem pushClass_add {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (C : Rep Coeff G)
    (φ φ' : unitRep G ⟶ C) :
    pushClass_lde p C (φ + φ') = pushClass_lde p C φ + pushClass_lde p C φ' := by
  rw [pushClass_lde, pushClass_lde, pushClass_lde, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]

/-- **The source of the base case is generated by the classes of the coefficient sequence**:
if `H¹(G, C) = 0` then every class in `Ext¹_G(𝔽_p, C)` is a `pushClass_lde` class.  This is the
surjectivity half of `Ext¹_G(𝔽_p, C) ≅ H⁰(G,C)/p·H⁰(G,C)` and follows from the long exact
sequence of `SSGRoute.Phi1.coeffSES` (proved for the global lane as `E3Base.exists_pushClass`,
which this file does not import in order to stay independent of the CFT lane). -/
theorem pushClass_surjective {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (C : Rep Coeff G)
    (hs : Subsingleton (extH C 1))
    (x : Abelian.Ext (Rep.trivial Coeff G (ZMod p)) C 1) :
    ∃ φ : unitRep G ⟶ C, x = pushClass_lde p C φ := by
  have hs' : Subsingleton (Abelian.Ext (SSGRoute.Phi1.coeffSES G p).X₂ C 1) := hs
  haveI := hs'
  have h0 : ((Abelian.Ext.mk₀ ((SSGRoute.Phi1.coeffSES G p).g)).comp x (zero_add 1)) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (S := SSGRoute.Phi1.coeffSES G p) (SSGRoute.Phi1.coeffSES_shortExact G p) C x h0
    (n₀ := 0) (by rfl)
  refine ⟨Abelian.Ext.addEquiv₀ x₁, ?_⟩
  rw [pushClass_lde]
  exact hx₁.symm.trans (congrArg (fun t =>
    ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass).comp t (add_zero 1))
    (Abelian.Ext.mk₀_addEquiv₀_apply x₁).symm)

/-- **The source of the base case of E7b, generated**: every class in
`Ext¹_{D_w}(𝔽_p, K_wˣ)` is the class of the coefficient sequence pushed out along a `D_w`-map
`ℤ → K_wˣ` (i.e. along an element of `k_vˣ = H⁰(D_w, K_wˣ)`).  This is Hilbert 90
(`hilbert90_localUnits_extH`) plus `pushClass_surjective`. -/
theorem localUnits_pushClass_surjective (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (w : NK.GlobalCFT.Place K) :
    ∀ x : Abelian.Ext (Rep.trivial Coeff (decompK (k := k) w) (ZMod p))
        (localUnitsK (k := k) w) 1,
      ∃ φ : unitRep (decompK (k := k) w) ⟶ localUnitsK (k := k) w,
        x = pushClass_lde p (localUnitsK (k := k) w) φ :=
  pushClass_surjective p (localUnitsK (k := k) w)
    (hilbert90_localUnits_extH k K w)

/-- **A local copy of `Work.SSGRoute.pushClass_eq_zero_iff_factors`**: `pushClass_lde p C φ` vanishes
exactly when `φ` factors through multiplication by `p` on the trivial representation.  (The sibling
file `SSGRoute/pushClass_eq_zero_iff_factors.lean` proves this, but it imports *this* file, so the
statement is reproduced here in order to stay independent of it.) -/
theorem pushClass_lde_eq_zero_iff_factors (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (C : Rep.{0} Coeff G) (φ : unitRep G ⟶ C) :
    pushClass_lde p C φ = 0 ↔ ∃ ψ : unitRep G ⟶ C, φ = SSGRoute.Phi1.unitMulByP G p ≫ ψ := by
  have hS : (SSGRoute.Phi1.coeffSES G p).ShortExact := SSGRoute.Phi1.coeffSES_shortExact G p
  have happly : ∀ a : (SSGRoute.Phi1.coeffSES G p).X₁ ⟶ C,
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ a) = a := by
    intro a
    rw [← Abelian.Ext.addEquiv₀_symm_apply a, Abelian.Ext.addEquiv₀.apply_symm_apply]
  constructor
  · intro h
    have h0 : hS.extClass.comp (Abelian.Ext.mk₀ φ) (add_zero 1) = 0 := by
      simpa only [pushClass_lde] using h
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS C (Abelian.Ext.mk₀ φ)
      (n₁ := 1) (by norm_num) h0
    refine ⟨Abelian.Ext.addEquiv₀ x₂, ?_⟩
    have hc := congrArg Abelian.Ext.addEquiv₀ hx₂
    rw [← Abelian.Ext.mk₀_addEquiv₀_apply x₂] at hc
    rw [Abelian.Ext.mk₀_comp_mk₀] at hc
    rw [happly, happly] at hc
    exact hc.symm
  · rintro ⟨ψ, rfl⟩
    rw [pushClass_lde]
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Abelian.Ext.mk₀ ψ) (n := 0)


/-- **The base case of the local pairing, in group cohomology.**  Modulo the
`Ext`/group-cohomology bridge `b` (`E0b`), the level pairing of a class of the coefficient sequence
vanishes exactly when its group-cohomology counterpart
`groupCohomology.map (id) (res φ ≫ ι) 2 (δ χ)` vanishes, where `χ` is the class of `h` under the
bridge and `δ` is the connecting map of the coefficient sequence.  This is the form in which the
arithmetic input is fed in: for `A = K_wˣ` it is `k_vˣ ∋ φ(1)` paired with the Kummer character
`χ`, i.e. the Kummer/cyclic-norm criterion. -/
theorem levelPair_pushClass_bridge (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    {G H : Type} [Group G] [Group H] (p : ℕ) [Fact p.Prime]
    (f : H →* G) {A : Rep Coeff G} {B : Rep Coeff H} (ι : Rep.res f A ⟶ B)
    (φ : unitRep G ⟶ A)
    (h : extH (Rep.res f (Rep.trivial Coeff G (ZMod p))) 1) :
    levelPair f ι (pushClass_lde p A φ) h = 0 ↔
      groupCohomology.map (MonoidHom.id H) ((Rep.resFunctor f).map φ ≫ ι) 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact H p) 1 2 rfl).hom
          ((b.e 1 H (Rep.trivial Coeff H (ZMod p))).symm h)) = 0 := by
  set χ : groupCohomology (Rep.trivial Coeff H (ZMod p)) 1 :=
    (b.e 1 H (Rep.trivial Coeff H (ZMod p))).symm h with hχ
  have hχe : b.e 1 H (Rep.trivial Coeff H (ZMod p)) χ = h := by
    rw [hχ]; exact (b.e 1 H (Rep.trivial Coeff H (ZMod p))).apply_symm_apply h
  have hχe' : b.e 1 H (SSGRoute.Phi1.coeffSES H p).X₃ χ = h := hχe
  have hd := b.delta 1 H (SSGRoute.Phi1.coeffSES H p)
    (SSGRoute.Phi1.coeffSES_shortExact H p) χ
  have hnat := b.naturality 2 H (SSGRoute.Phi1.coeffSES H p).X₁ B
    ((Rep.resFunctor f).map φ ≫ ι)
    ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact H p) 1 2 rfl).hom χ)
  have hval : (b.e 2 H B)
        (groupCohomology.map (MonoidHom.id H) ((Rep.resFunctor f).map φ ≫ ι) 2
          ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact H p) 1 2 rfl).hom χ)) =
        ((h.comp ((SSGRoute.Phi1.coeffSES_shortExact H p).extClass) rfl).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor f).map φ ≫ ι)) (add_zero (1 + 1))) ∨
      (b.e 2 H B)
        (groupCohomology.map (MonoidHom.id H) ((Rep.resFunctor f).map φ ≫ ι) 2
          ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact H p) 1 2 rfl).hom χ)) =
        -(((h.comp ((SSGRoute.Phi1.coeffSES_shortExact H p).extClass) rfl).comp
          (Abelian.Ext.mk₀ ((Rep.resFunctor f).map φ ≫ ι)) (add_zero (1 + 1)))) := by
    rw [hnat]
    rcases hd with hh | hh
    · left; rw [hh, hχe']
    · right; rw [hh, hχe']
      exact Abelian.Ext.neg_comp (h.comp ((SSGRoute.Phi1.coeffSES_shortExact H p).extClass) rfl)
        (Abelian.Ext.mk₀ ((Rep.resFunctor f).map φ ≫ ι)) (add_zero (1 + 1))
  rw [levelPair_pushClass (p := p) (f := f) (ι := ι) φ h]
  constructor
  · intro hzero
    rcases hval with hv | hv
    · rw [hzero] at hv
      exact (b.e 2 H B).injective (by rw [hv, map_zero])
    · rw [hzero, neg_zero] at hv
      exact (b.e 2 H B).injective (by rw [hv, map_zero])
  · intro hzero
    rcases hval with hv | hv
    · rw [hzero, map_zero] at hv
      exact hv.symm
    · rw [hzero, map_zero] at hv
      exact neg_eq_zero.mp hv.symm

end PushClassSpine

section PowHomRepSpine

/-! ## The coefficient map of a `pushClass_lde` class is `powHomRep`

`levelPair_pushClass_bridge` produces the group-cohomology class
`groupCohomology.map (id) ((Rep.resFunctor f).map φ ≫ ι) 2 (δ χ)`, i.e. the cup product of `δχ`
with the coefficient map `unitRep H ⟶ B` determined by the `H`-fixed element
`a = ((Rep.resFunctor f).map φ ≫ ι) 1`.  To feed the row into the arithmetic input
(`Work.SSGRoute.cyclicNormCriterion_rep`, which is stated for `Work.SSGRoute.powHomRep a _`), the
coefficient map must be identified with `powHomRep`.  That identification is what this section
provides: a `G`-map out of the trivial representation is determined by its value on `1`. -/

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

variable {G : Type} [Group G]

/-- **A `G`-map `unitRep G ⟶ A` is determined by its value on `1`**: `ψ = powHomRep (ψ 1)`. -/
theorem powHomRep_eq_of_apply_one {A : Rep Coeff G} (ψ : unitRep G ⟶ A)
    (hfix : ∀ σ : G, A.ρ σ (Rep.Hom.hom ψ 1) = Rep.Hom.hom ψ 1) :
    ψ = powHomRep (Rep.Hom.hom ψ 1) hfix := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  show (Rep.Hom.hom ψ).toLinearMap n =
    (Rep.Hom.hom (powHomRep (Rep.Hom.hom ψ 1) hfix)) n
  rw [powHomRep_apply]
  calc (Rep.Hom.hom ψ).toLinearMap n
      = (Rep.Hom.hom ψ).toLinearMap (n • (1 : Coeff)) := by rw [smul_eq_mul, mul_one]
    _ = n • (Rep.Hom.hom ψ).toLinearMap 1 := map_smul _ n 1

/-- **The value of a `G`-map out of the trivial representation on `1` is `G`-fixed.** -/
theorem rep_hom_apply_one_fixed {A : Rep Coeff G} (ψ : unitRep G ⟶ A) (σ : G) :
    A.ρ σ (Rep.Hom.hom ψ 1) = Rep.Hom.hom ψ 1 := by
  have h := Rep.hom_comm_apply ψ σ (1 : Coeff)
  rw [Rep.trivial_ρ] at h
  simpa using h.symm

/-- **The coefficient map of `pushClass_lde`**: for `φ : unitRep G ⟶ A` whose value `a = φ 1` is
`G`-fixed, `φ` is `powHomRep a`. -/
theorem pushClass_coeff_eq_powHomRep {A : Rep Coeff G} (φ : unitRep G ⟶ A)
    (hfix : ∀ σ : G, A.ρ σ (Rep.Hom.hom φ 1) = Rep.Hom.hom φ 1) :
    φ = powHomRep (Rep.Hom.hom φ 1) hfix :=
  powHomRep_eq_of_apply_one φ hfix

/-- **The cyclic norm criterion for an arbitrary coefficient map out of the trivial
representation**: the version of `Work.SSGRoute.cyclicNormCriterion_rep` in which the coefficient
map is given as `ψ : unitRep G ⟶ A` (with `ψ 1` `G`-fixed) rather than as `powHomRep`. -/
theorem cyclicNormCriterion_rep_apply_one {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (hcyc : IsCyclic G) (hcard : Nat.card G = p) {A : Rep Coeff G} (ψ : unitRep G ⟶ A)
    (hfix : ∀ σ : G, A.ρ σ (Rep.Hom.hom ψ 1) = Rep.Hom.hom ψ 1)
    (h : groupCohomology (Rep.trivial Coeff G (ZMod p)) 1) (hne : h ≠ 0) :
    (groupCohomology.map (MonoidHom.id G) ψ 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h) = 0) ↔
      Rep.Hom.hom ψ 1 ∈ Set.range (Rep.Hom.hom A.norm) := by
  have hval : (groupCohomology.map (MonoidHom.id G) ψ 2)
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h)
      = (groupCohomology.map (MonoidHom.id G) (powHomRep (Rep.Hom.hom ψ 1) hfix) 2)
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h) := by
    rw [show powHomRep (Rep.Hom.hom ψ 1) hfix = ψ from (powHomRep_eq_of_apply_one ψ hfix).symm]
  have hone : (Rep.Hom.hom (powHomRep (Rep.Hom.hom ψ 1) hfix)) (1 : SSGRoute.PTExt.Coeff)
      = Rep.Hom.hom ψ 1 := by
    rw [powHomRep_apply, one_smul]
  rw [hval]
  exact (cyclicNormCriterion_rep p hcyc hcard A (Rep.Hom.hom ψ 1) hfix h hne).trans
    ⟨fun hh => hone ▸ hh, fun hh => hone.symm ▸ hh⟩

end PowHomRepSpine

section LevelPairTrivial

set_option maxHeartbeats 4000000

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

/-- **E7b, base case `M = 𝔽_p`, at a prime cyclic level.**

At a level `L ⊇ K` and a place `w' ∣ w` whose decomposition group `D_{w'} = Gal(L_{w'}/k_v)` is
cyclic of order `p`, the level pairing of a class `y = pushClass_lde p K_wˣ φ` of the trivial module
`𝔽_p` with a *nonzero* character `h ∈ H¹(D_{w'}, 𝔽_p)` vanishes if and only if the local unit
`a = ι(φ 1)` is a norm for the local representation `L_{w'}ˣ` over `D_{w'}` (i.e. lies in the image
of its norm endomorphism, which here is the local field norm of the cyclic degree-`p` extension
`L_{w'}/k_v`).

Modulo the `Ext`/group-cohomology bridge `b` (`E0b`) this is
`Work.SSGRoute.levelPair_pushClass_bridge` — the pairing is the cup product with `δχ` — combined
with the arithmetic input `Work.SSGRoute.cyclicNormCriterion_rep` (`A = L_{w'}ˣ`, `G = D_{w'}`),
via `Work.SSGRoute.powHomRep_eq_of_apply_one` (a `D_{w'}`-map out of the trivial representation is
determined by its value on `1`). -/
theorem levelPair_trivial_eq_zero_iff_norm
    (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w')]
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (φ : unitRep (decompK (k := k) w) ⟶ localUnitsK (k := k) w)
    (hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') = p)
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1) (hne : h ≠ 0) :
    levelPair f ι (pushClass_lde p (localUnitsK (k := k) w) φ) h = 0 ↔
      (Rep.Hom.hom (((Rep.resFunctor f).map φ) ≫ ι) 1) ∈
        Set.range (Rep.Hom.hom (NK.HassePrinciple.localUnitsRep k L w').norm) := by
  classical
  set a : NK.HassePrinciple.localUnitsRep k L w' :=
    Rep.Hom.hom (((Rep.resFunctor f).map φ) ≫ ι) 1 with ha
  have hafix : ∀ σ : MulAction.stabilizer (L ≃ₐ[k] L) w',
      (NK.HassePrinciple.localUnitsRep k L w').ρ σ a = a :=
    fun σ => rep_hom_apply_one_fixed _ σ
  rw [levelPair_pushClass_bridge b p f ι φ h]
  set χ : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h with hχ
  have hχne : χ ≠ 0 := by
    rw [hχ]
    intro h0
    have h1 : (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)))
        ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h) = h :=
      (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).apply_symm_apply h
    rw [h0, map_zero] at h1
    exact hne h1.symm
  exact cyclicNormCriterion_rep_apply_one p hcyc hcard
    (((Rep.resFunctor f).map φ) ≫ ι) hafix χ hχne


/-- **The general-level norm criterion for an arbitrary coefficient map.**  The version of
`Work.SSGRoute.normCriterion_quotient` in which the coefficient map is an arbitrary
`G`-map `ψ : ℤ → A` (with `ψ 1` `G`-fixed) rather than the canonical `powHomRep`.

The parameter order (the coefficient map *before* the subgroup `N`) is deliberate: it lets the
caller pass a composite morphism such as `(Rep.resFunctor f).map φ ≫ ι` whose source object is only
propositionally, not definitionally, equal to `unitRep G`. -/
theorem normCriterion_quotient_apply_one' {G : Type} [Group G] [Fintype G]
    {A : Rep Coeff G} (ψ : unitRep G ⟶ A)
    (hfix : ∀ σ : G, A.ρ σ (Rep.Hom.hom ψ 1) = Rep.Hom.hom ψ 1)
    (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)] (p : ℕ) [Fact p.Prime]
    (hcyc : IsCyclic (G ⧸ N)) (hcard : Nat.card (G ⧸ N) = p)
    (hH1 : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (h : groupCohomology (Rep.trivial Coeff G (ZMod p)) 1)
    (hlift : ∃ hb : groupCohomology (Rep.trivial Coeff (G ⧸ N) (ZMod p)) 1,
      (groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb = h)
    (hne : h ≠ 0) :
    (groupCohomology.map (MonoidHom.id G) ψ 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h) = 0) ↔
      ∃ b : A, (∀ n : N, A.ρ (n : G) b = b) ∧
        (∑ x : G ⧸ N, A.ρ (Quotient.out x) b) = Rep.Hom.hom ψ 1 := by
  have hpow : ψ = powHomRep (Rep.Hom.hom ψ 1) hfix := powHomRep_eq_of_apply_one ψ hfix
  conv_lhs => rw [hpow]
  exact normCriterion_quotient N p hcyc hcard A (Rep.Hom.hom ψ 1) hfix hH1 h hlift hne

/-- **E7b, base case `M = 𝔽_p`, general level.**  At a level `L ⊇ K` and a place `w' ∣ w`, for a
nonzero `h ∈ H¹(D_{w'}, 𝔽_p)` whose kernel `N = ker h` has cyclic quotient `D_{w'} ⧸ N` of order
`p` (so that `h` is inflated from `D_{w'} ⧸ N`, hypothesis `hlift`), the level pairing of a class
`y = pushClass_lde p K_wˣ φ` vanishes if and only if the unit `a = ι(φ 1)` is a *norm for the
quotiented level* `D_{w'} ⧸ N`, i.e. lies in the image of the `D_{w'} ⧸ N`-norm on the `N`-fixed
points of `L_{w'}ˣ`.  In the local application `a ∈ k_vˣ` and the condition is
`a ∈ N_{E'/k_v}(E'ˣ)` for the degree-`p` subfield `E' = L_{w'}^{ker h}`.

This is `Work.SSGRoute.levelPair_pushClass_bridge` (the pairing is the cup product with `δχ`)
composed with the general-level norm criterion `Work.SSGRoute.normCriterion_quotient` for the
`D_{w'}`-module `A = L_{w'}ˣ` (whose `H¹(ker h, ·)` vanishes by Hilbert 90,
`Work.SSGRoute.hilbert90_localUnitsRep`). -/
theorem levelPair_trivial_eq_zero_iff_normB
    (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w')]
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (φ : unitRep (decompK (k := k) w) ⟶ localUnitsK (k := k) w)
    (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) [N.Normal]
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)]
    (hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p)
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1) (hne : h ≠ 0)
    (hlift : ∃ hb : groupCohomology
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) (ZMod p)) 1,
      (groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb
        = (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
            (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h) :
    levelPair f ι (pushClass_lde p (localUnitsK (k := k) w) φ) h = 0 ↔
      ∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ
            (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Rep.Hom.hom (((Rep.resFunctor f).map φ) ≫ ι) 1 := by
  classical
  rw [levelPair_pushClass_bridge b p f ι φ h]
  set χ : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h with hχ
  have hχne : χ ≠ 0 := by
    rw [hχ]
    intro h0
    have h1 : (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)))
        ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h) = h :=
      (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).apply_symm_apply h
    rw [h0, map_zero] at h1
    exact hne h1.symm
  exact normCriterion_quotient_apply_one' (((Rep.resFunctor f).map φ) ≫ ι)
    (fun σ => rep_hom_apply_one_fixed _ σ) N p hcyc hcard
    (hilbert90_localUnitsRep (k := k) (L := L) w' N) χ hlift hχne


/-- **E7b, detection at a level by a class whose value misses the quotient-norm section.**

Let `L ⊇ K` be a level, `w' ∣ w`, `N ⊴ D_{w'}` a normal subgroup with `D_{w'}/N` cyclic of order `p`
(such `N` is `ker h` for a nontrivial character `h` of `D_{w'}`).  If the value of the pushout
coefficient map `res_f φ ≫ ι` on `1` is **not** in the image of the quotient-norm endomorphism
`∑_{x ∈ D_{w'}/N} ρ (out x) ·` of `L_{w'}ˣ` restricted to the `N`-fixed units, then the class
`pushClass_lde p K_wˣ φ ∈ Ext¹_{D_w}(𝔽_p, K_wˣ)` detects `h`, whenever `h ≠ 0` is inflated from
`H¹(D_{w'}/N, 𝔽_p)`.

This is the general-`N` form of `Work.SSGRoute.detect_trivial_cyclic_of_norm_notMem` (which is the
case `D_{w'}` cyclic of order `p`): the content is `levelPair_trivial_eq_zero_iff_normB`. -/
theorem detect_trivial_of_norm_notMem
    (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w')]
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (φ : unitRep (decompK (k := k) w) ⟶ localUnitsK (k := k) w)
    (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) [N.Normal]
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)]
    (hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p)
    (hnot : ¬ ∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ
            (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Rep.Hom.hom (((Rep.resFunctor f).map φ) ≫ ι) 1)
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1)
    (hne : h ≠ 0)
    (hlift : ∃ hb : groupCohomology
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) (ZMod p)) 1,
      (groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb
        = (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
            (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h) :
    ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1,
      levelPair f ι y h ≠ 0 := by
  refine ⟨pushClass_lde p (localUnitsK (k := k) w) φ, fun hzero => hnot ?_⟩
  exact (levelPair_trivial_eq_zero_iff_normB b p k K w L w' hw' f ι φ N hcyc hcard
    h hne hlift).mp hzero

section ClauseITrivial

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

/-- **E7b, clause (i) at `M = 𝔽_p`, modulo the arithmetic input.**

This is the exact assembly of clause (i) of `local_duality_ext` in the special case `M = 𝔽_p`,
with the three number-theoretic inputs kept as hypotheses:

* `hAI` is `Work.SSGRoute.exists_level_quotientNorm_avoids`, the Grünwald/local-CFT input;
* `hchar` is `Work.SSGRoute.exists_H1_inflated_ne_zero`, the non-zero inflated character;
* `hnotpow` is `Work.SSGRoute.not_pow_of_pushClass_lde_ne_zero`, the translation of `y ≠ 0` into
  "`φ 1` is not a `p`-th power of a `D_w`-fixed unit".

The formal steps (all available here) are: `y = pushClass_lde p K_wˣ φ`
(`localUnits_pushClass_surjective`); the level datum from `hAI`; the canonical restriction
`f` and local embedding `ι` (`decompK_restrict_exists`, `localUnitsMap_exists`); the bridge `b`
turns the constructed character into `h ∈ H¹(D_{w'}, 𝔽_p)` with the inflation property `hlift`;
and `levelPair_trivial_eq_zero_iff_normB` converts vanishing of the pairing into the norm
condition, which `hAI` has arranged to fail. -/
theorem clause_i_trivial_of_arithmetic
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    (hnotpow : ∀ (φ : unitRep (decompK (k := k) w) ⟶ localUnitsK (k := k) w),
        pushClass_lde p (localUnitsK (k := k) w) φ ≠ 0 →
        ¬ ∃ bb : (NK.GlobalCFT.Place.localField K w)ˣ,
          (∀ σ : decompK (k := k) w,
            NK.HassePrinciple.localUnitsEquiv (K := k) w σ bb = bb) ∧
          Rep.Hom.hom φ (1 : Coeff) = Additive.ofMul (bb ^ p))
    (hAI : ∀ a : (NK.GlobalCFT.Place.localField K w)ˣ,
        (∀ σ : decompK (k := k) w,
          NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a) →
        (¬ ∃ bb : (NK.GlobalCFT.Place.localField K w)ˣ,
          (∀ σ : decompK (k := k) w,
            NK.HassePrinciple.localUnitsEquiv (K := k) w σ bb = bb) ∧ bb ^ p = a) →
        ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
          (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
          (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
          (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
          (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
          IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
          Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
          ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
            (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
              (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
            (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
              (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
              Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' a))) :
    ∀ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1,
      (∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
        [FiniteDimensional k L] [IsGalois k L]
        (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
        (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
        (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
        (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
        (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
          ι.hom (Additive.ofMul u) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
        (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
            (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1),
        levelPair f ι y h = 0) → y = 0 := by
  classical
  intro y hy
  by_contra hyne
  obtain ⟨φ, hφ⟩ := localUnits_pushClass_surjective p k K w y
  rw [hφ] at hyne
  let av : Additive (NK.GlobalCFT.Place.localField K w)ˣ := Rep.Hom.hom φ (1 : Coeff)
  let a : (NK.GlobalCFT.Place.localField K w)ˣ := Additive.toMul av
  have hof : (Rep.Hom.hom φ (1 : Coeff) : NK.HassePrinciple.localUnitsRep k K w)
      = Additive.ofMul a := rfl
  have hafix : ∀ σ : decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a := by
    intro σ
    have h2 : Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) w σ a) =
        Additive.ofMul a := rep_hom_apply_one_fixed φ σ
    exact Additive.ofMul.injective h2
  have ha : ¬ ∃ bb : (NK.GlobalCFT.Place.localField K w)ˣ,
      (∀ σ : decompK (k := k) w,
        NK.HassePrinciple.localUnitsEquiv (K := k) w σ bb = bb) ∧ bb ^ p = a := by
    rintro ⟨bb, hbb, hbbp⟩
    refine hnotpow φ hyne ⟨bb, hbb, ?_⟩
    rw [hbbp]
    exact hof
  obtain ⟨L, hLf, hLn, hAL, hAK, hST, hfd, hgal, w', hw', N, hN, hF, hcyc, hcard, hfail⟩ :=
    hAI a hafix ha
  letI : Field L := hLf
  letI : NumberField L := hLn
  letI : Algebra k L := hAL
  letI : Algebra K L := hAK
  letI : IsScalarTower k K L := hST
  letI : FiniteDimensional k L := hfd
  letI : IsGalois k L := hgal
  letI : N.Normal := hN
  letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) := hF
  letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w') := Fintype.ofFinite _
  obtain ⟨f, hf⟩ := decompK_restrict_exists k K L w w' hw'
  obtain ⟨ι, hι⟩ := localUnitsMap_exists k K L w w' hw' f hf
  obtain ⟨χ, hχne, hχinfl⟩ := exists_H1_inflated_ne_zero N p hcyc hcard
  set hb : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (groupCohomology.map (QuotientGroup.mk' N)
      (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom χ with hbdef
  set h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
      (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))) hb with hh
  have hne : h ≠ 0 := by
    rw [hh]
    intro h0
    exact hχinfl ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).injective
      (by rw [h0]; exact (map_zero _).symm))
  have hlift : ∃ hb' : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) (ZMod p)) 1,
      (groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb' =
        (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h := by
    refine ⟨χ, ?_⟩
    rw [hh, hbdef]
    exact ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm_apply_apply
      ((groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom χ)).symm
  have hcomp : Rep.Hom.hom ((Rep.resFunctor f).map φ ≫ ι) (1 : Coeff)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' a) := by
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_apply]
    exact hι a
  have hzero : levelPair f ι (pushClass_lde p (localUnitsK (k := k) w) φ) h = 0 := by
    rw [← hφ]
    exact hy L w' hw' f hf ι hι h
  have hrhs := (levelPair_trivial_eq_zero_iff_normB b p k K w L w' hw' f ι φ N hcyc hcard
    h hne hlift).mp hzero
  rw [hcomp] at hrhs
  exact hfail hrhs



section NotPowAux
set_option backward.isDefEq.respectTransparency false

theorem pushClass_lde_eq_zero_of_eq_smul_local {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    {A : Rep.{0} SSGRoute.PTExt.Coeff G} (φ : SSGRoute.PTExt.unitRep G ⟶ A)
    (a : A.V) (hafix : ∀ σ : G, A.ρ σ a = a)
    (h1 : Rep.Hom.hom φ (1 : SSGRoute.PTExt.Coeff) = (p : SSGRoute.PTExt.Coeff) • a) :
    Work.SSGRoute.pushClass_lde p A φ = 0 := by
  rw [Work.SSGRoute.pushClass_lde_eq_zero_iff_factors p A φ]
  refine ⟨Work.SSGRoute.powHomRep a hafix, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  show (Rep.Hom.hom φ).toLinearMap n = ((p : SSGRoute.PTExt.Coeff) * n) • a
  have hφn : (Rep.Hom.hom φ).toLinearMap n = n • (Rep.Hom.hom φ).toLinearMap 1 := by
    calc (Rep.Hom.hom φ).toLinearMap n
        = (Rep.Hom.hom φ).toLinearMap (n • (1 : SSGRoute.PTExt.Coeff)) := by
          rw [smul_eq_mul, mul_one]
      _ = n • (Rep.Hom.hom φ).toLinearMap 1 := map_smul _ n 1
  calc (Rep.Hom.hom φ).toLinearMap n
      = n • (Rep.Hom.hom φ).toLinearMap 1 := hφn
    _ = n • ((p : SSGRoute.PTExt.Coeff) • a) := by
          rw [show (Rep.Hom.hom φ).toLinearMap 1 = (Rep.Hom.hom φ) 1 from rfl, h1]
    _ = (n * (p : SSGRoute.PTExt.Coeff)) • a := smul_smul n (p : SSGRoute.PTExt.Coeff) a
    _ = ((p : SSGRoute.PTExt.Coeff) * n) • a := by rw [mul_comm]

/-- **`pushClass_lde p K_wˣ φ` is non-zero unless the value of `φ` on `1` is a `p`-th power of a
`D_w`-fixed local unit.**

If there is a unit `b ∈ K_wˣ` fixed by the decomposition group `D_w` (with
`NK.HassePrinciple.localUnitsEquiv` the action) such that `φ 1 = b ^ p`, then `φ 1 = p • b` in the
additive group `K_wˣ`, the corresponding `G`-map `ψ = powHomRep (Additive.ofMul b)` satisfies
`φ = unitMulByP ≫ ψ`, and `pushClass_lde_eq_zero_of_eq_smul_local` gives `pushClass_lde p K_wˣ φ = 0`. -/
theorem not_pow_of_pushClass_lde_ne_zero_local
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (φ : SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) w)
      ⟶ SSGRoute.PTExt.localUnitsK (k := k) w)
    (hne : Work.SSGRoute.pushClass_lde p (SSGRoute.PTExt.localUnitsK (k := k) w) φ ≠ 0) :
    ¬ ∃ b : (NK.GlobalCFT.Place.localField K w)ˣ,
      (∀ σ : SSGRoute.PTExt.decompK (k := k) w,
        NK.HassePrinciple.localUnitsEquiv (K := k) w σ b = b) ∧
      Rep.Hom.hom φ (1 : SSGRoute.PTExt.Coeff) = Additive.ofMul (b ^ p) := by
  rintro ⟨b, hb, h1⟩
  -- `Additive.ofMul b` is fixed by the decomposition group
  have hfix : ∀ σ : SSGRoute.PTExt.decompK (k := k) w,
      (SSGRoute.PTExt.localUnitsK (k := k) w).ρ σ (Additive.ofMul b) = Additive.ofMul b := by
    intro σ
    rw [show (SSGRoute.PTExt.localUnitsK (k := k) w).ρ σ (Additive.ofMul b)
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) w σ b) from rfl, hb σ]
  -- `p`-th powers of units are `p`-multiples of the corresponding element of `K_wˣ` as a
  -- `Coeff = ℤ`-module
  have hkeyall : ∀ x : (SSGRoute.PTExt.localUnitsK (k := k) w).V,
      x = (Additive.ofMul b : (SSGRoute.PTExt.localUnitsK (k := k) w).V) →
      (p : SSGRoute.PTExt.Coeff) • x = Additive.ofMul (b ^ p) := by
    intro x hx
    rw [hx, ULift.smul_def]
    rw [show ((p : SSGRoute.PTExt.Coeff).down : ℤ) = (p : ℤ) from rfl]
    rw [← zpow_natCast b p]
    exact (ofMul_zpow (p : ℤ) b).symm
  exact hne (pushClass_lde_eq_zero_of_eq_smul_local p φ (Additive.ofMul b) hfix
    (h1.trans (hkeyall (Additive.ofMul b : (SSGRoute.PTExt.localUnitsK (k := k) w).V) rfl).symm))

end NotPowAux

/-- **E7b clause (i) at `M = 𝔽_p`, modulo only the Grünwald/local-CFT input `hAI`.**

`clause_i_trivial_of_arithmetic` with the bridge `b` discharged from
`Work.SSGRoute.nonempty_extGroupCohomologyBridge` and the `p`-th-power translation `hnotpow` from
`Work.SSGRoute.not_pow_of_pushClass_lde_ne_zero`. -/
theorem clause_i_trivial
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (hAI : ∀ a : (NK.GlobalCFT.Place.localField K w)ˣ,
        (∀ σ : decompK (k := k) w,
          NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a) →
        (¬ ∃ bb : (NK.GlobalCFT.Place.localField K w)ˣ,
          (∀ σ : decompK (k := k) w,
            NK.HassePrinciple.localUnitsEquiv (K := k) w σ bb = bb) ∧ bb ^ p = a) →
        ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
          (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
          (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
          (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
          (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
          IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
          Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
          ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
            (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
              (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
            (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
              (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
              Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' a))) :
    ∀ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1,
      (∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
        [FiniteDimensional k L] [IsGalois k L]
        (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
        (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
        (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
        (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
        (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
          ι.hom (Additive.ofMul u) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
        (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
            (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1),
        levelPair f ι y h = 0) → y = 0 := by
  obtain ⟨b⟩ := nonempty_extGroupCohomologyBridge
  exact clause_i_trivial_of_arithmetic p k K w b
    (fun φ hne => not_pow_of_pushClass_lde_ne_zero_local p k K w φ hne) hAI

end ClauseITrivial


section DetectHTrivial

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

/-- **Y1: `𝔽_p`-detection at an arbitrary level.**  At a level `L ⊇ K`, a place `w' ∣ w`, every
nonzero `h ∈ H¹(D_{w'}, 𝔽_p)` is detected by some `y ∈ Ext¹_{D_w}(𝔽_p, K_wˣ)`.

Proof: `cyclic_quotient_of_H1_ne_zero` produces `N ⊴ D_{w'}` with `D_{w'}/N` cyclic of order `p`
and `h` inflated from `H¹(D_{w'}/N, 𝔽_p)`; `normImage_at_level_proper_K` produces a `D_w`-fixed unit
`v ∈ K_wˣ` whose image by `Place.localAlgebraMapUnits w' w` is not a quotient-norm over `N`; then
`detect_trivial_of_norm_notMem` applies with `φ := powHomRep (Additive.ofMul v)`. -/
theorem detect_h_trivial_K
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1) (hne : h ≠ 0) :
    ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1,
      levelPair f ι y h ≠ 0 := by
  classical
  obtain ⟨b⟩ := nonempty_extGroupCohomologyBridge
  haveI : Fintype (L ≃ₐ[k] L) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w') := Fintype.ofFinite _
  -- the corresponding class in group cohomology
  set hz : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h with hzdef
  have hz_ne : hz ≠ 0 := by
    intro h0
    apply hne
    have h1 : (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))) hz = 0 := by
      rw [h0, map_zero]
    rw [hzdef] at h1
    rwa [AddEquiv.apply_symm_apply] at h1
  obtain ⟨N, hNnorm, hNfin, hcyc, hcard, hb, hinfl⟩ :=
    cyclic_quotient_of_H1_ne_zero p hz hz_ne
  haveI : N.Normal := hNnorm
  haveI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) := hNfin
  -- the norm-image witness
  obtain ⟨v, hvfix, hvnorm⟩ := normImage_at_level_proper_K (p := p) k K w L w' hw' N hcyc hcard
  -- the coefficient map
  have hfixv : ∀ σ : decompK (k := k) w,
      (localUnitsK (k := k) w).ρ σ (Additive.ofMul v) = Additive.ofMul v := by
    intro σ
    rw [show (localUnitsK (k := k) w).ρ σ (Additive.ofMul v)
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) w σ v) from rfl,
      hvfix σ]
  -- the value of the composite coefficient map on `1`
  have hval : Rep.Hom.hom
      (((Rep.resFunctor f).map (powHomRep (Additive.ofMul v) hfixv)) ≫ ι)
      (1 : SSGRoute.PTExt.Coeff) =
      Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' v) := by
    have hcomp : ι.hom (Additive.ofMul v) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' v) := hι v
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_apply]
    show ι.hom (1 • (Additive.ofMul v)) =
      Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' v)
    rw [one_smul]
    exact hcomp
  refine detect_trivial_of_norm_notMem b p k K w L w' hw' f ι
    (powHomRep (Additive.ofMul v) hfixv) N hcyc hcard ?_ h hne ?_
  · rintro ⟨bb, hbb, hsum⟩
    refine hvnorm ⟨bb, hbb, ?_⟩
    rw [hsum, hval]
  · exact ⟨hb, by rw [hinfl]⟩

end DetectHTrivial

end LevelPairTrivial


namespace Work.SSGRoute.E7bFin

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false


-- ===== Y1 wrapper: `RightDetect` for `𝔽_p`, from `detect_h_trivial_K` (proved above) =====
/-- `RightDetect` for the trivial coefficient module `𝔽_p`, from `detect_h_trivial_K`. -/
theorem detect_h_trivial (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w)
    (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K) =
      SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w) ⟶
      NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w')) :
    SSGRoute.PTExt.RightDetect f ι
      (Rep.trivial SSGRoute.PTExt.Coeff (SSGRoute.PTExt.decompK (k := k) w) (ZMod p)) := by
  intro h hne
  exact detect_h_trivial_K p k K w L w' hw' f ι hι h hne


-- ===== copied from rightDetect_quotient_step =====


open SSGRoute.PTExt CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

-- Instance house-keeping for `Coeff = ULift ℤ` (as in `powHomRepDefs`), needed by `powHomRep`.
attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

section Helpers


lemma ext_eq_zero_of_comp_mk₀_iso {G : Type} [Group G] {M M' X : Rep.{0} Coeff G} {n : ℕ}
    (θ : M ≅ M') (u : Abelian.Ext.{0} X M n)
    (h : u.comp (Abelian.Ext.mk₀ θ.hom) (add_zero n) = 0) : u = 0 := by
  have h2 : (u.comp (Abelian.Ext.mk₀ θ.hom) (add_zero n)).comp (Abelian.Ext.mk₀ θ.inv)
      (add_zero n) = 0 := by rw [h]; simp
  simpa only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, θ.hom_inv_id,
    Abelian.Ext.comp_mk₀_id] using h2


lemma levelPair_extClass_comp {G D : Type} [Group G] [Group D] (f : G →* D)
    {A : Rep.{0} Coeff D} {B : Rep.{0} Coeff G} (ι : Rep.res f A ⟶ B)
    (S : ShortComplex (Rep.{0} Coeff D)) (hS : S.ShortExact) {n : ℕ}
    (z : Abelian.Ext.{0} S.X₁ A 1) (x₃ : extH (Rep.res f S.X₃) n) :
    levelPair f ι z (x₃.comp (hS.map_of_exact (Rep.resFunctor f)).extClass rfl) =
      levelPair f ι (hS.extClass.comp z rfl) x₃ := by
  have hβ : (hS.map_of_exact (Rep.resFunctor f)).extClass
      = (hS.extClass).mapExactFunctor (Rep.resFunctor f) :=
    (Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor f) hS).symm
  have hcomp : (hS.extClass.comp z rfl).mapExactFunctor (Rep.resFunctor f)
      = ((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
        (z.mapExactFunctor (Rep.resFunctor f)) rfl :=
    Abelian.Ext.mapExactFunctor_comp (F := Rep.resFunctor f) (α := hS.extClass) (β := z)
      (h := rfl)
  simp only [levelPair, extRes]
  rw [hβ, hcomp]
  have hstep1 : (x₃.comp ((hS.extClass).mapExactFunctor (Rep.resFunctor f)) rfl).comp
        ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1)) rfl
      = x₃.comp (((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
          ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1)) rfl)
        rfl :=
    Abelian.Ext.comp_assoc x₃ ((hS.extClass).mapExactFunctor (Rep.resFunctor f))
      ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1))
      rfl rfl rfl
  have hstep2 : (((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
        (z.mapExactFunctor (Rep.resFunctor f)) rfl).comp (Abelian.Ext.mk₀ ι) (add_zero 2)
      = ((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
          ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1)) rfl :=
    Abelian.Ext.comp_assoc ((hS.extClass).mapExactFunctor (Rep.resFunctor f))
      (z.mapExactFunctor (Rep.resFunctor f)) (Abelian.Ext.mk₀ ι) rfl (add_zero 1) rfl
  rw [hstep1, hstep2]

end Helpers


lemma levelPair_coeff_naturality_map {H G : Type} [Group H] [Group G] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (y : Abelian.Ext.{0} M' A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι ((Abelian.Ext.mk₀ π).comp y (zero_add r)) h =
      levelPair f ι y (h.comp (Abelian.Ext.mk₀ ((Rep.resFunctor f).map π)) (add_zero s)) := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]


theorem rightDetect_quotient_step (p : ℕ) [Fact p.Prime] {G D : Type} [Group G] [Group D]
    [Finite G] [Finite D] (f : G →* D) (hf : Function.Surjective f)
    {A : Rep Coeff D} {B : Rep Coeff G} (ι : Rep.res f A ⟶ B)
    (hT : Nat.card {x : extH B 2 // p • x = 0} = p)
    (hE2 : Finite (Abelian.Ext (Rep.trivial Coeff D (ZMod p)) A 2))
    (hE2card : Nat.card (Abelian.Ext (Rep.trivial Coeff D (ZMod p)) A 2) ≤ p)
    (S : ShortComplex (Rep Coeff D)) (hS : S.ShortExact)
    (e : S.X₃ ≅ Rep.trivial Coeff D (ZMod p))
    [Finite S.X₁] (hp₁ : ∀ m : S.X₁, p • m = 0) (hp₂ : ∀ m : S.X₂, p • m = 0)
    (h₁ : RightDetect f ι S.X₁) (h₃ : RightDetect f ι (Rep.trivial Coeff D (ZMod p))) :
    RightDetect f ι S.X₂ := by
  classical
  intro h hne
  -- `S.X₃` is `p`-torsion: it is a quotient of `S.X₂`
  have hp₃ : ∀ m : S.X₃, p • m = 0 := by
    intro m
    obtain ⟨x, hx⟩ := (Rep.epi_iff_surjective S.g).mp hS.epi_g m
    rw [← hx]
    have h1 : S.g (p • x) = p • S.g x := map_nsmul (Rep.Hom.hom S.g).toLinearMap p x
    rw [← h1, hp₂ x, map_zero]
  -- the target `Ext²_D(S.X₃, A)` of the connecting map
  have hpE : ∀ x : Abelian.Ext S.X₃ A 2, p • x = 0 := fun x => ext_nsmul_p_torsion_left p hp₃ x
  have hcancel : ∀ x : Abelian.Ext S.X₃ A 2,
      (Abelian.Ext.mk₀ e.hom).comp ((Abelian.Ext.mk₀ e.inv).comp x (zero_add 2)) (zero_add 2)
        = x := by
    intro x
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Abelian.Ext.mk₀_id_comp]
  have hinj : Function.Injective
      (fun u : Abelian.Ext S.X₃ A 2 => (Abelian.Ext.mk₀ e.inv).comp u (zero_add 2)) := by
    intro u v huv
    have huv' : (Abelian.Ext.mk₀ e.inv).comp u (zero_add 2)
        = (Abelian.Ext.mk₀ e.inv).comp v (zero_add 2) := huv
    calc u = (Abelian.Ext.mk₀ e.hom).comp ((Abelian.Ext.mk₀ e.inv).comp u (zero_add 2))
          (zero_add 2) := (hcancel u).symm
      _ = (Abelian.Ext.mk₀ e.hom).comp ((Abelian.Ext.mk₀ e.inv).comp v (zero_add 2))
          (zero_add 2) := congrArg
            (fun x => (Abelian.Ext.mk₀ e.hom).comp x (zero_add 2)) huv'
      _ = v := hcancel v
  haveI hEfin : Finite (Abelian.Ext S.X₃ A 2) := Finite.of_injective _ hinj
  have hEcard : Nat.card (Abelian.Ext S.X₃ A 2) ≤ p := by
    have h := Nat.card_le_card_of_injective
      (fun u : Abelian.Ext S.X₃ A 2 => (Abelian.Ext.mk₀ e.inv).comp u (zero_add 2)) hinj
    exact h.trans hE2card
  haveI hfin₁ : Finite (Rep.res f S.X₁) := ‹Finite S.X₁›
  haveI hWfin : Finite (extH (Rep.res f S.X₁) 1) :=
    local_duality_ext_extH_finite (Rep.res f S.X₁) 1
  -- the connecting map `d` of the sequence `S` in the first variable
  let d : Abelian.Ext S.X₁ A 1 →+ Abelian.Ext S.X₃ A 2 :=
    { toFun := fun z => hS.extClass.comp z rfl
      map_zero' := by simp
      map_add' := fun a b => by simp }
  -- push `h` forward along `S.g`
  let hg : extH (Rep.res f S.X₃) 1 :=
    h.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).g)) (add_zero 1)
  by_cases hg0 : hg = 0
  · -- ## the case where `h` is the image of a class in `H¹(G, S.X₁)`
    obtain ⟨hsub, hhsub⟩ := Abelian.Ext.covariant_sequence_exact₂
      (X := unitRep G) (S := S.map (Rep.resFunctor f))
      (hS := hS.map_of_exact (Rep.resFunctor f)) (n := 1) h hg0
    have hsubne : hsub ≠ 0 := by
      intro h0
      apply hne
      rw [← hhsub, h0]
      exact Abelian.Ext.zero_comp (unitRep G) 1
        (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f)) 1 (add_zero 1)
    -- the element of `S.X₃` over `1`
    let u₃ : S.X₃ := (Rep.Hom.hom e.inv) 1
    have hu₃ : (Rep.Hom.hom e.hom) u₃ = 1 := by
      show (Rep.Hom.hom e.hom) ((Rep.Hom.hom e.inv) 1) = 1
      rw [Rep.hom_inv_apply]
    have hcancelE : ∀ x : S.X₃, (Rep.Hom.hom e.inv) ((Rep.Hom.hom e.hom) x) = x :=
      fun x => by rw [Rep.inv_hom_apply]
    have hu₃fixD : ∀ δ : D, S.X₃.ρ δ u₃ = u₃ := by
      intro δ
      have h1 : (Rep.Hom.hom e.hom) (S.X₃.ρ δ u₃) = (Rep.Hom.hom e.hom) u₃ := by
        rw [Rep.hom_comm_apply, hu₃]
        simp
      calc S.X₃.ρ δ u₃
          = (Rep.Hom.hom e.inv) ((Rep.Hom.hom e.hom) (S.X₃.ρ δ u₃)) := (hcancelE _).symm
        _ = (Rep.Hom.hom e.inv) ((Rep.Hom.hom e.hom) u₃) := by rw [h1]
        _ = u₃ := hcancelE u₃
    have hu₃fixG : ∀ γ : G, (Rep.res f S.X₃).ρ γ u₃ = u₃ := fun γ => hu₃fixD (f γ)
    let one₃ : unitRep G ⟶ Rep.res f S.X₃ := powHomRep u₃ hu₃fixG
    have hone₃ : (Rep.Hom.hom one₃) (1 : Coeff) = u₃ := by
      rw [powHomRep_apply, one_smul]
    have hone : e.hom (one₃ 1) = 1 := by
      show (Rep.Hom.hom e.hom) ((Rep.Hom.hom one₃) (1 : Coeff)) = 1
      rw [hone₃, hu₃]
    -- the connecting class
    let eG : extH (Rep.res f S.X₁) 1 :=
      (Abelian.Ext.mk₀ one₃).comp ((hS.map_of_exact (Rep.resFunctor f)).extClass) (zero_add 1)
    by_cases heG : eG = 0
    · -- ### the case where the connecting class vanishes: `S` splits over `D`
      obtain ⟨m, hmD, hm1⟩ :=
        exists_fixed_element_of_connecting_eq_zero p f hf S hS e one₃ hone heG
      obtain ⟨s, hs⟩ := exists_section_of_fixed_generator p S e hp₂ m hmD hm1
      let Sp := ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f
      obtain ⟨z₀, hz₀⟩ := h₁ hsub hsubne
      refine ⟨(Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1), ?_⟩
      have hnat : levelPair f ι ((Abelian.Ext.mk₀ S.f).comp
            ((Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1)) (zero_add 1)) hsub
          = levelPair f ι ((Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1))
            (hsub.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f)) (add_zero 1)) :=
        levelPair_coeff_naturality_map f S.f ι _ hsub
      have hkey : (Abelian.Ext.mk₀ S.f).comp ((Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1))
          (zero_add 1) = z₀ := by
        rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Sp.f_r, Abelian.Ext.mk₀_id_comp]
      rw [← hhsub, ← hnat, hkey]
      exact hz₀
    · -- ### the case where the connecting class is nonzero: the "K"-argument
      have hy : ∃ z : Abelian.Ext S.X₁ A 1,
          hS.extClass.comp z rfl = 0 ∧ levelPair f ι z hsub ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have heGK : ∀ z : Abelian.Ext S.X₁ A 1, hS.extClass.comp z rfl = 0 →
            levelPair f ι z eG = 0 := by
          intro z hz
          rw [show eG = (Abelian.Ext.mk₀ one₃).comp
              ((hS.map_of_exact (Rep.resFunctor f)).extClass) (zero_add 1) from rfl,
            levelPair_extClass_comp f ι S hS z (Abelian.Ext.mk₀ one₃), hz]
          exact levelPair_zero f ι (Abelian.Ext.mk₀ one₃)
        have hWp : ∀ w : extH (Rep.res f S.X₁) 1, p • w = 0 :=
          fun w => ext_nsmul_p_torsion (A := Rep.res f S.X₁) p hp₁ w
        letI : Module (ZMod p) (extH (Rep.res f S.X₁) 1) := AddCommGroup.zmodModule hWp
        obtain ⟨c, hc⟩ := exists_smul_eq_of_annihilator p hpE hEcard hWp hT
          d (fun z w => levelPair f ι z w)
          (fun v₁ v₂ w => levelPair_add f ι v₁ v₂ w)
          (fun v w₁ w₂ => levelPair_add_h f ι v w₁ w₂)
          (fun c z w => by
            have hcw : c • w = c.val • w := by
              rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val w, ZMod.natCast_zmod_val c]
            rw [hcw]
            exact map_nsmul (levelPairFunctional f ι z) c.val w)
          (fun z w => by
            have h1 : levelPair f ι z (p • w) = p • levelPair f ι z w :=
              map_nsmul (levelPairFunctional f ι z) p w
            rw [← h1, hWp w]
            exact levelPair_zero_h f ι z)
          h₁ heG heGK hcon
        exfalso
        have heGker : eG.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f)) (add_zero 1) = 0 := by
          rw [show eG = (Abelian.Ext.mk₀ one₃).comp
              ((hS.map_of_exact (Rep.resFunctor f)).extClass) (zero_add 1) from rfl,
            Abelian.Ext.comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp]
          simp
        have hcv : c • eG = c.val • eG := by
          rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val eG, ZMod.natCast_zmod_val c]
        apply hne
        rw [← hhsub, ← hc, hcv]
        let iStar : extH (Rep.res f S.X₁) 1 →+ extH (Rep.res f S.X₂) 1 :=
          { toFun := fun u => u.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
              (add_zero 1)
            map_zero' := by simp
            map_add' := fun a b => by simp }
        have hsm : (c.val • eG).comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
              (add_zero 1)
            = c.val • (eG.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
                (add_zero 1)) :=
          map_nsmul iStar c.val eG
        rw [hsm, heGker, smul_zero]
      obtain ⟨z, hz0, hz⟩ := hy
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ (S := S) hS A z (by omega) hz0
      refine ⟨y, ?_⟩
      have hnat : levelPair f ι ((Abelian.Ext.mk₀ S.f).comp y (zero_add 1)) hsub
          = levelPair f ι y (hsub.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
              (add_zero 1)) :=
        levelPair_coeff_naturality_map f S.f ι y hsub
      rw [← hhsub, ← hnat, hy]
      exact hz
  · -- ## the case `π_* h ≠ 0`: use the base case for `𝔽_p`
    let hg3 : extH (Rep.res f (Rep.trivial Coeff D (ZMod p))) 1 :=
      hg.comp (Abelian.Ext.mk₀ (Rep.resMap f e.hom)) (add_zero 1)
    have hg3ne : hg3 ≠ 0 := fun h0 =>
      hg0 (ext_eq_zero_of_comp_mk₀_iso ((Rep.resFunctor f).mapIso e) hg h0)
    obtain ⟨y₃, hy₃⟩ := h₃ hg3 hg3ne
    refine ⟨(Abelian.Ext.mk₀ S.g).comp ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1))
      (zero_add 1), ?_⟩
    have hnat1 : levelPair f ι ((Abelian.Ext.mk₀ S.g).comp
          ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1)) (zero_add 1)) h
        = levelPair f ι ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1))
          (h.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).g)) (add_zero 1)) :=
      levelPair_coeff_naturality_map f S.g ι _ h
    have hnat2 : levelPair f ι ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1))
          (h.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).g)) (add_zero 1))
        = levelPair f ι y₃ (hg.comp (Abelian.Ext.mk₀ (Rep.resMap f e.hom)) (add_zero 1)) :=
      levelPair_coeff_naturality_map f e.hom ι y₃ _
    rw [hnat1, hnat2]
    exact hy₃



-- ===== copied from rightDetect_pgroup =====


open SSGRoute.PTExt CategoryTheory


theorem rightDetect_pgroup (p : ℕ) [Fact p.Prime] {G D : Type} [Group G] [Group D]
    [Finite G] [Finite D] (hD : IsPGroup p D) (f : G →* D) (hf : Function.Surjective f)
    {A : Rep Coeff D} {B : Rep Coeff G} (ι : Rep.res f A ⟶ B)
    (hT : Nat.card {x : extH B 2 // p • x = 0} = p)
    (hE2 : Finite (Abelian.Ext (Rep.trivial Coeff D (ZMod p)) A 2))
    (hE2card : Nat.card (Abelian.Ext (Rep.trivial Coeff D (ZMod p)) A 2) ≤ p)
    (hbase : RightDetect f ι (Rep.trivial Coeff D (ZMod p)))
    (M : Rep Coeff D) [Finite M] (hM : ∀ m : M, p • m = 0) :
    RightDetect f ι M := by
  classical
  have key : ∀ n, ∀ (N : Rep Coeff D), Finite N → (∀ m : N, p • m = 0) →
      Nat.card N ≤ n → RightDetect f ι N := by
    intro n
    induction n with
    | zero =>
      intro N hN hNp hcard
      have hpos : 0 < Nat.card N := Nat.card_pos_iff.mpr ⟨Nonempty.intro 0, hN⟩
      exact absurd hcard (by omega)
    | succ n ih =>
      intro N hN hNp hcard
      haveI : Finite ↥N := hN
      by_cases hsmall : Nat.card N ≤ n
      · exact ih N hN hNp hsmall
      · by_cases htriv : Subsingleton ↥N
        · -- `N = 0`: `Ext¹` into a zero object is a point
          haveI : Injective (Rep.res f N) :=
            ((Rep.isZero_res_iff f N).mpr ((Rep.isZero_iff Coeff D N).mpr htriv)).injective
          haveI : Subsingleton (extH (Rep.res f N) 1) :=
            Abelian.Ext.subsingleton_of_injective (unitRep G) (Rep.res f N) 0
          intro h hh
          exact absurd (Subsingleton.elim h 0) hh
        · -- `N ≠ 0`: split off `𝔽_p` as a quotient
          have hNtriv : Nontrivial ↥N := by
            by_contra hcon
            refine htriv ⟨fun a b => ?_⟩
            by_contra hab
            exact hcon ⟨a, b, hab⟩
          obtain ⟨φ, hφsurj⟩ := rightDetect_fixed_functional p hD N hNp hNtriv
          haveI hφepi : Epi φ := (Rep.epi_iff_surjective φ).mpr hφsurj
          have hφne : φ ≠ 0 := by
            intro h0
            obtain ⟨x, hx⟩ := hφsurj 1
            exact one_ne_zero (by rw [← hx, h0]; simp)
          -- the kernel short exact sequence
          let S : ShortComplex (Rep Coeff D) :=
            ShortComplex.mk (Limits.kernel.ι φ) φ (Limits.kernel.condition φ)
          have hS : S.ShortExact :=
            ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (Limits.kernelIsKernel φ))
              inferInstance inferInstance
          have hinj : Function.Injective ⇑(Limits.kernel.ι φ).hom :=
            (Rep.mono_iff_injective (Limits.kernel.ι φ)).mp inferInstance
          haveI hkfin : Finite ↥(Limits.kernel φ) :=
            Finite.of_injective ⇑(Limits.kernel.ι φ).hom hinj
          haveI : Finite S.X₁ := hkfin
          have hp₁ : ∀ x : ↥(Limits.kernel φ), p • x = 0 := by
            intro x
            apply hinj
            simp only [map_nsmul, hNp, map_zero]
          have hker_lt : Nat.card ↥(Limits.kernel φ) < Nat.card ↥N := by
            haveI : Fintype ↥N := Fintype.ofFinite ↥N
            haveI : Fintype ↥(Limits.kernel φ) := Fintype.ofFinite ↥(Limits.kernel φ)
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            refine Fintype.card_lt_of_injective_not_surjective ⇑(Limits.kernel.ι φ).hom hinj ?_
            intro hsurj
            haveI : Epi (Limits.kernel.ι φ) := (Rep.epi_iff_surjective (Limits.kernel.ι φ)).mpr hsurj
            exact hφne ((cancel_epi (Limits.kernel.ι φ)).mp (by simpa using Limits.kernel.condition φ))
          have hIH : RightDetect f ι (Limits.kernel φ) :=
            ih (Limits.kernel φ) hkfin hp₁ (by omega)
          exact rightDetect_quotient_step p f hf ι hT hE2 hE2card S hS (Iso.refl _) hp₁ hNp hIH hbase
  exact key (Nat.card M) M inferInstance hM le_rfl



-- ===== copied from local_detect_h_pgroup =====


set_option linter.style.haveILetI false

open SSGRoute.PTExt CategoryTheory


private theorem ptors_le_of_not_dvd_card (p : ℕ) [Fact p.Prime] {D : Type} [Group D]
    [Fintype D] (A : Rep Coeff D) (hpD : ¬ p ∣ Nat.card D) : PTorsLE p (extH A 2) := by
  have hcop : Nat.Coprime p (Nat.card D) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpD
  have hbez : (p : ℤ) * (Nat.gcdA p (Nat.card D))
      + (Nat.card D : ℤ) * (Nat.gcdB p (Nat.card D)) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p (Nat.card D)
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    linarith [h]
  have hzero : ∀ y : extH A 2, p • y = 0 → y = 0 := by
    intro y hy
    have hDy : Nat.card D • y = 0 := extH_natCard_smul_eq_zero A (n := 2) (by norm_num) y
    have hy' : (p : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ p]; exact hy
    have hDy' : (Nat.card D : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ (Nat.card D)]; exact hDy
    calc y = (1 : ℤ) • y := (one_smul _ _).symm
      _ = ((p : ℤ) * (Nat.gcdA p (Nat.card D))
            + (Nat.card D : ℤ) * (Nat.gcdB p (Nat.card D))) • y := by rw [hbez]
      _ = (Nat.gcdA p (Nat.card D)) • ((p : ℤ) • y)
            + (Nat.gcdB p (Nat.card D)) • ((Nat.card D : ℤ) • y) := by
            rw [add_smul, mul_smul, mul_smul,
              smul_comm (p : ℤ) (Nat.gcdA p (Nat.card D)) y,
              smul_comm (Nat.card D : ℤ) (Nat.gcdB p (Nat.card D)) y]
      _ = 0 := by rw [hy', hDy']; simp
  haveI : Subsingleton {x : extH A 2 // p • x = 0} :=
    ⟨fun a b => Subtype.ext (by rw [hzero a.1 a.2, hzero b.1 b.2])⟩
  refine ⟨Finite.of_subsingleton, ?_⟩
  haveI : Fintype {x : extH A 2 // p • x = 0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact le_trans (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)
    (by have := (Fact.out : p.Prime).two_le; omega)


theorem pTorsLE_extH_two (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) :
    PTorsLE p (extH (localUnitsK (k := k) w) 2) := by
  by_cases hdiv : p ∣ Nat.card (decompK (k := k) w)
  · have hcard := local_pTorsion_card p k K w hdiv
    refine ⟨(Nat.card_ne_zero.mp (by rw [hcard]; exact (Fact.out : p.Prime).ne_zero)).2, ?_⟩
    exact le_of_eq hcard
  · haveI : Fintype (decompK (k := k) w) := Fintype.ofFinite _
    exact ptors_le_of_not_dvd_card p (localUnitsK (k := k) w) hdiv


theorem local_detect_h_pgroup (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (hD : IsPGroup p (decompK (k := k) w))
    (N : Rep Coeff (decompK (k := k) w)) [Finite N] (hN : ∀ n : N, p • n = 0)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w')) :
    RightDetect f ι N := by
  haveI : Finite (MulAction.stabilizer (L ≃ₐ[k] L) w') := inferInstance
  haveI : Finite (decompK (k := k) w) := inferInstance
  have hsurj : Function.Surjective f :=
    decompK_restrict_surjective k K w L w' hw' f hf
  have hH1 : Subsingleton (extH (localUnitsK (k := k) w) 1) :=
    hilbert90_localUnits_extH k K w
  have hT2 : PTorsLE p (extH (localUnitsK (k := k) w) 2) :=
    pTorsLE_extH_two p k K w
  have hE2 := ext_two_trivial_ptors p (localUnitsK (k := k) w) hH1 hT2
  have hT : Nat.card {x : extH (NK.HassePrinciple.localUnitsRep k L w') 2 // p • x = 0} = p :=
    local_pTorsion_card p k L w' hp
  exact rightDetect_pgroup p hD f hsurj ι hT hE2.1 hE2.2
    (detect_h_trivial p k K w L w' hw' f hf ι hι hp) N hN



-- ===== copied from rightDetect_sylowLevelStabIncl =====


open SSGRoute.PTExt CategoryTheory

namespace RDSI

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module


def unitResIso' {H G : Type} [Group H] [Group G] (f : H →* G) :
    Rep.res f (unitRep G) ≅ unitRep H where
  hom := trivResInv f Coeff
  inv := unitRes f
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl


noncomputable def extResEquiv' {G₁ G₂ : Type} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (X Y : Rep.{0} Coeff G₂) (n : ℕ) :
    Abelian.Ext X Y n ≃+ Abelian.Ext (Rep.res e.toMonoidHom X) (Rep.res e.toMonoidHom Y) n := by
  haveI : (Rep.resFunctor (k := Coeff) e.toMonoidHom).IsEquivalence := by
    have h : (e.symm).symm.toMonoidHom = e.toMonoidHom := by rw [MulEquiv.symm_symm]
    rw [← h]
    exact resFunctor_isEquivalence e.symm
  exact AddEquiv.ofBijective ((Rep.resFunctor e.toMonoidHom).mapExtAddHom X Y n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects _ X Y n)

@[simp] lemma extResEquiv'_apply {G₁ G₂ : Type} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (X Y : Rep.{0} Coeff G₂) (n : ℕ) (x : Abelian.Ext X Y n) :
    extResEquiv' e X Y n x = extRes e.toMonoidHom x := rfl


theorem extHMap_self_ne_zero {G H : Type} [Group G] [Group H] (e : H ≃* G)
    {B : Rep.{0} Coeff G} {n : ℕ} (y : extH B n) (hy : y ≠ 0) :
    extHMap e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom B)) y ≠ 0 := by
  intro h0
  have h0u : (Abelian.Ext.mk₀ (unitRes e.toMonoidHom)).comp (extRes e.toMonoidHom y)
      (zero_add n) = 0 := by
    have h := h0
    simp only [SSGRoute.PTExt.extHMap, Abelian.Ext.comp_mk₀_id] at h
    exact h
  have hZ : (Abelian.Ext.mk₀ (unitResIso' e.toMonoidHom).hom).comp
      ((Abelian.Ext.mk₀ (unitRes e.toMonoidHom)).comp (extRes e.toMonoidHom y)
        (zero_add n)) (zero_add n) = extRes e.toMonoidHom y := by
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]
    rw [show Abelian.Ext.mk₀ (unitRes e.toMonoidHom)
        = Abelian.Ext.mk₀ ((unitResIso' e.toMonoidHom).inv) from rfl]
    rw [Abelian.Ext.mk₀_comp_mk₀, (unitResIso' e.toMonoidHom).hom_inv_id,
      Abelian.Ext.mk₀_id_comp]
  have h1 : extRes e.toMonoidHom y = 0 := by
    rw [← hZ, h0u, Abelian.Ext.comp_zero]
  refine hy ?_
  apply (extResEquiv' e (unitRep G) B n).injective
  rw [map_zero, extResEquiv'_apply]
  exact h1


theorem levelPair_eqOfEq {G H' : Type} [Group G] [Group H']
    (φ φ' : H' →* G) (hcomp : φ' = φ)
    {M A : Rep.{0} Coeff G} {B' : Rep.{0} Coeff H'} (ι : Rep.res φ A ⟶ B')
    (ι' : Rep.res φ' A ⟶ B')
    (hι : ι = eqToHom (congrArg (fun t => Rep.res t A) hcomp.symm) ≫ ι')
    {s : ℕ} (x : Abelian.Ext M A 1) (h : extH (Rep.res φ M) s) :
    levelPair φ' ι' x
        (h.comp (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t M) hcomp.symm)))
          (add_zero s))
      = levelPair φ ι x h := by
  cases hcomp
  simp only [CategoryTheory.eqToHom_refl, Category.id_comp, Abelian.Ext.comp_mk₀_id] at hι ⊢
  rw [hι]


theorem coeffMap_eqOfEq {G H' : Type} [Group G] [Group H']
    (φ φ' : H' →* G) (hcomp : φ' = φ)
    {A : Rep.{0} Coeff G} {B' : Rep.{0} Coeff H'} (ι : Rep.res φ A ⟶ B')
    (ι' : Rep.res φ' A ⟶ B')
    (H : ∀ v : A.V, (Rep.Hom.hom ι') v = (Rep.Hom.hom ι) v) :
    ι = eqToHom (congrArg (fun t => Rep.res t A) hcomp.symm) ≫ ι' := by
  cases hcomp
  simp only [CategoryTheory.eqToHom_refl, Category.id_comp]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact (H v).symm


theorem comp_eqToHom_ne_zero {G : Type} [Group G] {X Y : Rep.{0} Coeff G} (h : X = Y)
    {n : ℕ} (a : extH X n) (ha : a ≠ 0) :
    a.comp (Abelian.Ext.mk₀ (eqToHom h)) (add_zero n) ≠ 0 := by
  intro h0
  refine ha ?_
  have hback : (a.comp (Abelian.Ext.mk₀ (eqToHom h)) (add_zero n)).comp
      (Abelian.Ext.mk₀ (eqToHom h.symm)) (add_zero n) = a := by
    rw [Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀]
    have : eqToHom h ≫ eqToHom h.symm = 𝟙 _ := by
      rw [CategoryTheory.eqToHom_trans]
      rw [show h.trans h.symm = rfl from Subsingleton.elim _ _,
        CategoryTheory.eqToHom_refl]
    rw [this, Abelian.Ext.comp_mk₀_id]
    all_goals try omega
  rw [← hback, h0, Abelian.Ext.zero_comp]

end RDSI

theorem rightDetect_sylowLevelStabIncl (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K)) (hP : IsPGroup p P)
    (hPD : P ≤ SSGRoute.PTExt.decompK (k := k) w)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w)
    (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w) ⟶
      NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp' : p ∣ Nat.card (MulAction.stabilizer
      (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w')) :
    SSGRoute.PTExt.RightDetect
      (A := Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
        (SSGRoute.PTExt.localUnitsK (k := k) w))
      (B := Rep.res ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w'))
      (f.subgroupComap (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype))
      (Rep.resMap ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype ι)
      (Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)) := by
  classical
  haveI hgalL : IsGalois ↥(IntermediateField.fixedField P) L :=
    IsGalois.tower_top_of_isGalois k (IntermediateField.fixedField P) L
  -- ## The two group isomorphisms (base change `k → k' = K^P`)
  let eK : SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w ≃*
      P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype :=
    Work.SSGRoute.stabInclEquivK k K w P hPD
  let eL : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' ≃*
      (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f :=
    Work.SSGRoute.stabInclEquivL k K L P w hPD w' hw' f hf
  -- ## The `k'`-world level data
  obtain ⟨f', hf'⟩ := Work.SSGRoute.decompK_restrict_exists
      ↥(IntermediateField.fixedField P) K L w w' hw'
  obtain ⟨ι', hι'⟩ := Work.SSGRoute.localUnitsMap_exists
      ↥(IntermediateField.fixedField P) K L w w' hw' f' hf'
  -- ## The two level maps agree
  have hcomp : eK.toMonoidHom.comp f' =
      (f.subgroupComap (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype)).comp
        eL.toMonoidHom := by
    have hcast2 : ∀ σ : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w',
        ((eL σ : (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f) :
          MulAction.stabilizer (L ≃ₐ[k] L) w')
          = AlgEquiv.restrictScalars k (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L) := fun σ => by
      rw [show ((eL σ : (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f) :
          MulAction.stabilizer (L ≃ₐ[k] L) w') = Work.SSGRoute.stabIncl (k := k)
          (M := ↥(IntermediateField.fixedField P)) (E := L) w' σ from
        Work.SSGRoute.stabInclEquivL_apply k K L P w hPD w' hw' f hf σ]
      rfl
    refine MonoidHom.ext fun σ => Subtype.ext (Subtype.ext (AlgEquiv.ext fun x => ?_))
    simp only [MonoidHom.comp_apply]
    change (AlgEquiv.restrictScalars k ((f' σ :
        SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w) :
        K ≃ₐ[↥(IntermediateField.fixedField P)] K)) x
      = ((f (eL σ) : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K) x
    rw [hf' σ, hf (eL σ), hcast2 σ]
    apply (algebraMap K L).injective
    rw [show (algebraMap K L) ((AlgEquiv.restrictScalars k ((SSGRoute.PTExt.galRes
        ↥(IntermediateField.fixedField P) K L)
        (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L))) x)
        = (algebraMap K L) (((σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)).restrictNormal K x) from rfl,
      show (algebraMap K L) ((SSGRoute.PTExt.galRes k K L
        (AlgEquiv.restrictScalars k (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L))) x)
        = (algebraMap K L) (((AlgEquiv.restrictScalars k
          (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)).restrictNormal K x)) from rfl]
    rw [AlgEquiv.restrictNormal_commutes (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L) K x,
        AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars k
          (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)) K x]
    rfl
  -- ## Right detection in the `k'`-world
  have hD : IsPGroup p (SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w) :=
    (Work.SSGRoute.SylowIn.isPGroup_fixedField (P := P) hP).to_subgroup _
  haveI hfin : Finite (Rep.res (SSGRoute.PTExt.decompK
      (k := ↥(IntermediateField.fixedField P)) w).subtype
      (Rep.res (AlgEquiv.restrictScalarsHom (R := k)
        (S := ↥(IntermediateField.fixedField P)) (A := K)) M)) := inferInstance
  have hM' : ∀ n : Rep.res (SSGRoute.PTExt.decompK
      (k := ↥(IntermediateField.fixedField P)) w).subtype
      (Rep.res (AlgEquiv.restrictScalarsHom (R := k)
        (S := ↥(IntermediateField.fixedField P)) (A := K)) M), p • n = 0 := fun n => hM n
  have hdet : SSGRoute.PTExt.RightDetect f' ι'
      (Rep.res (SSGRoute.PTExt.decompK (k := ↥(IntermediateField.fixedField P)) w).subtype
        (Rep.res (AlgEquiv.restrictScalarsHom (R := k)
          (S := ↥(IntermediateField.fixedField P)) (A := K)) M)) :=
    local_detect_h_pgroup p ↥(IntermediateField.fixedField P) K w hD _
      hM' L w' hw' f' hf' ι' hι' hp'
  -- ## The transport
  intro h hne
  -- abbreviations for the `k`-world at the subgroup `S`
  let M_S := Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
  let A_S := Rep.res (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).subtype
      (SSGRoute.PTExt.localUnitsK (k := k) w)
  let φ₀ := f.subgroupComap (P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype)
  let B := Rep.res ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype
      (NK.HassePrinciple.localUnitsRep k L w')
  let ι_S := Rep.resMap ((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype ι
  let B' := NK.HassePrinciple.localUnitsRep ↥(IntermediateField.fixedField P) L w'
  -- the `H¹`-class at the `eL`-level
  let h₁ := extHMap eL.toMonoidHom (𝟙 (Rep.res eL.toMonoidHom (Rep.res φ₀ M_S))) h
  have h₁ne : h₁ ≠ 0 := RDSI.extHMap_self_ne_zero eL h hne
  -- the transported `H¹`-class at the `eK ∘ f'`-level
  let h₂ := h₁.comp (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t M_S) hcomp.symm)))
    (add_zero 1)
  have h₂ne : h₂ ≠ 0 :=
    RDSI.comp_eqToHom_ne_zero (congrArg (fun t => Rep.res t M_S) hcomp.symm) h₁ h₁ne
  obtain ⟨y', hy'⟩ := hdet h₂ h₂ne
  -- the class at the `k`-world `S`-level
  set y : Abelian.Ext M_S A_S 1 := (RDSI.extResEquiv' eK M_S A_S 1).symm y' with hydef
  have hy : extRes eK.toMonoidHom y = y' := by
    rw [hydef, ← RDSI.extResEquiv'_apply]
    exact AddEquiv.apply_symm_apply _ _
  refine ⟨y, ?_⟩
  -- ## The identification of the coefficient maps
  have hιM : (Rep.resMap eL.toMonoidHom ι_S)
      = eqToHom (congrArg (fun t => Rep.res t A_S) hcomp.symm) ≫ ι' := by
    refine RDSI.coeffMap_eqOfEq (A := A_S) (B' := B') (φ := φ₀.comp eL.toMonoidHom)
      (φ' := eK.toMonoidHom.comp f') hcomp (ι := Rep.resMap eL.toMonoidHom ι_S) (ι' := ι') ?_
    intro v
    change (Rep.Hom.hom ι') v = (Rep.Hom.hom ι) v
    calc (Rep.Hom.hom ι') v
        = (Rep.Hom.hom ι') (Additive.ofMul (Additive.toMul v)) := rfl
      _ = Additive.ofMul ((NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw') (Additive.toMul v)) :=
            hι' (Additive.toMul v)
      _ = (Rep.Hom.hom ι) (Additive.ofMul (Additive.toMul v)) := (hι (Additive.toMul v)).symm
      _ = (Rep.Hom.hom ι) v := rfl
  -- ## The final chain of pairings
  have hchain : levelPair f' ι' y' h₂
      = extHMap eL.toMonoidHom (𝟙 (Rep.res eL.toMonoidHom B))
          (levelPair φ₀ ι_S y h) := by
    calc levelPair f' ι' y' h₂
        = levelPair f' ι' (extRes eK.toMonoidHom y) h₂ := by rw [hy]
      _ = levelPair (eK.toMonoidHom.comp f') ι' y h₂ := by
            simp only [SSGRoute.PTExt.levelPair]
            rw [← Work.SSGRoute.SylowDesc.extRes_comp_aux]
      _ = levelPair (φ₀.comp eL.toMonoidHom) (Rep.resMap eL.toMonoidHom ι_S) y h₁ :=
            RDSI.levelPair_eqOfEq (M := M_S) (A := A_S) (B' := B')
              (φ₀.comp eL.toMonoidHom) (eK.toMonoidHom.comp f') hcomp
              (Rep.resMap eL.toMonoidHom ι_S) ι' hιM y h₁
      _ = extHMap eL.toMonoidHom (𝟙 (Rep.res eL.toMonoidHom B)) (levelPair φ₀ ι_S y h) :=
            (Work.SSGRoute.SylowIn.levelPair_restrict (M := M_S) (A := A_S) (B := B)
              (B' := Rep.res eL.toMonoidHom B) φ₀ eL.toMonoidHom ι_S
              (𝟙 (Rep.res eL.toMonoidHom B)) (Rep.resMap eL.toMonoidHom ι_S) y h rfl).symm
  rw [hchain] at hy'
  exact fun h0 => hy' (by rw [h0, E6Util.extHMap_zero])



-- ===== copied from local_duality_ext_detect_h =====


open SSGRoute.PTExt CategoryTheory




theorem levelPair_coeff_naturality {H G : Type} [Group H] [Group G] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (y : Abelian.Ext.{0} M' A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι ((Abelian.Ext.mk₀ π).comp y (zero_add r)) h =
      levelPair f ι y (h.comp (Abelian.Ext.mk₀ (Rep.resMap f π)) (add_zero s)) := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]


theorem detect_of_quotient {G H : Type} [Group G] [Group H] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B)
    (y : Abelian.Ext.{0} M' A 1) (h : extH (Rep.res f M) 1)
    (hy : levelPair f ι y (h.comp (Abelian.Ext.mk₀ (Rep.resMap f π)) (add_zero 1)) ≠ 0) :
    ∃ y' : Abelian.Ext.{0} M A 1, levelPair f ι y' h ≠ 0 :=
  ⟨(Abelian.Ext.mk₀ π).comp y (zero_add 1),
    by rw [levelPair_coeff_naturality]; exact hy⟩



section BaseCase

variable (p : ℕ) [Fact p.Prime] (k K : Type)
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
  [IsGalois k K] (w : NK.GlobalCFT.Place K)


theorem detect_trivial_cyclic_of_norm_notMem
    (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w')]
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (φ : unitRep (decompK (k := k) w) ⟶ localUnitsK (k := k) w)
    (hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') = p)
    (hnot : (Rep.Hom.hom (((Rep.resFunctor f).map φ) ≫ ι) 1) ∉
      Set.range (Rep.Hom.hom (NK.HassePrinciple.localUnitsRep k L w').norm))
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1) (hne : h ≠ 0) :
    ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1,
      levelPair f ι y h ≠ 0 := by
  refine ⟨pushClass_lde p (localUnitsK (k := k) w) φ, fun hzero => hnot ?_⟩
  exact (levelPair_trivial_eq_zero_iff_norm b p k K w L w' hw' f ι φ hcyc hcard h hne).mp hzero

end BaseCase








theorem exists_sylow_fixedField_setup (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) :
    ∃ S : Subgroup (decompK (k := k) w),
      IsPGroup p S ∧ ¬ p ∣ S.index ∧
      (IntermediateField.fixedField (S.map (decompK (k := k) w).subtype)).fixingSubgroup =
        S.map (decompK (k := k) w).subtype := by
  classical
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := decompK (k := k) w)
  refine ⟨(P : Subgroup (decompK (k := k) w)), P.isPGroup', Sylow.not_dvd_index P, ?_⟩
  exact IntermediateField.fixingSubgroup_fixedField _



theorem fixedField_world_instances (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (P : Subgroup (K ≃ₐ[k] K)) (hP : IsPGroup p P) :
    IsGalois ↥(IntermediateField.fixedField P) K ∧
      IsPGroup p (K ≃ₐ[↥(IntermediateField.fixedField P)] K) ∧
      NumberField ↥(IntermediateField.fixedField P) :=
  ⟨inferInstance, SylowIn.isPGroup_fixedField (P := P) hP, inferInstance⟩



theorem place_smul_restrictScalarsHom (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k k'] [Algebra k' K] [Algebra k K]
    [IsScalarTower k k' K] (σ : K ≃ₐ[k'] K) (w : NK.GlobalCFT.Place K) :
    (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K) σ) • w = σ • w := by
  cases w <;> rfl


theorem map_restrictScalarsHom_decompK_fixedField (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K)) (hPD : P ≤ decompK (k := k) w) :
    (decompK (k := ↥(IntermediateField.fixedField P)) w).map
      (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P)) (A := K)) = P := by
  classical
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, -, rfl⟩
    have hmem : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
        (A := K) σ) ∈ (IntermediateField.fixedField P).fixingSubgroup :=
      ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)).symm σ).2
    rwa [IntermediateField.fixingSubgroup_fixedField P] at hmem
  · intro hx
    have hx' : x ∈ (IntermediateField.fixedField P).fixingSubgroup := by
      rwa [IntermediateField.fixingSubgroup_fixedField P]
    refine ⟨(IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)) ⟨x, hx'⟩, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      rw [← place_smul_restrictScalarsHom k ↥(IntermediateField.fixedField P) K]
      have hrst : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
          (A := K) ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P))
            ⟨x, hx'⟩)) = x :=
        AlgEquiv.ext fun y => rfl
      rw [hrst]
      exact MulAction.mem_stabilizer_iff.mp (hPD hx)
    · exact AlgEquiv.ext fun y => rfl



theorem exists_restrictionMap_fixedField (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (P : Subgroup (K ≃ₐ[k] K)) :
    ∃ f' : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' →*
        decompK (k := ↥(IntermediateField.fixedField P)) w,
      ∀ σ, ((f' σ : decompK (k := ↥(IntermediateField.fixedField P)) w) :
          K ≃ₐ[↥(IntermediateField.fixedField P)] K)
        = galRes ↥(IntermediateField.fixedField P) K L
            (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L) := by
  haveI : IsGalois ↥(IntermediateField.fixedField P) L :=
    IsGalois.tower_top_of_isGalois k (IntermediateField.fixedField P) L
  exact decompK_restrict_exists ↥(IntermediateField.fixedField P) K L w w' hw'



theorem exists_localUnitsMap_fixedField (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (P : Subgroup (K ≃ₐ[k] K))
    [IsGalois ↥(IntermediateField.fixedField P) L]
    (f' : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' →*
        decompK (k := ↥(IntermediateField.fixedField P)) w)
    (hf' : ∀ σ, ((f' σ : decompK (k := ↥(IntermediateField.fixedField P)) w) :
        K ≃ₐ[↥(IntermediateField.fixedField P)] K)
      = galRes ↥(IntermediateField.fixedField P) K L
          (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)) :
    ∃ ι' : Rep.res f' (localUnitsK (k := ↥(IntermediateField.fixedField P)) w) ⟶
        NK.HassePrinciple.localUnitsRep ↥(IntermediateField.fixedField P) L w',
      ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι'.hom (Additive.ofMul u)
          = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) :=
  localUnitsMap_exists ↥(IntermediateField.fixedField P) K L w w' hw' f' hf'



instance instIsGalois_fixedField_of_isGalois (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (P : Subgroup (K ≃ₐ[k] K)) : IsGalois ↥(IntermediateField.fixedField P) L :=
  IsGalois.tower_top_of_isGalois k (IntermediateField.fixedField P) L


theorem fixedField_levelData (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (P : Subgroup (K ≃ₐ[k] K)) :
    ∃ (f' : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' →*
          decompK (k := ↥(IntermediateField.fixedField P)) w)
      (hf' : ∀ σ, ((f' σ : decompK (k := ↥(IntermediateField.fixedField P)) w) :
          K ≃ₐ[↥(IntermediateField.fixedField P)] K)
        = galRes ↥(IntermediateField.fixedField P) K L
            (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L))
      (ι' : Rep.res f' (localUnitsK (k := ↥(IntermediateField.fixedField P)) w) ⟶
          NK.HassePrinciple.localUnitsRep ↥(IntermediateField.fixedField P) L w')
      (hι' : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι'.hom (Additive.ofMul u)
          = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u)),
      True := by
  obtain ⟨f', hf'⟩ := exists_restrictionMap_fixedField k K L w w' hw' P
  obtain ⟨ι', hι'⟩ := exists_localUnitsMap_fixedField k K L w w' hw' P f' hf'
  exact ⟨f', hf', ι', hι', trivial⟩


theorem local_duality_ext_detect_h (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1) (hne : h ≠ 0) :
    ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
      levelPair f ι y h ≠ 0 := by
  classical
  -- ## Step 1: the Sylow `p`-subgroup `S₀ ≤ D_w` and the subgroup `S = P.comap subtype`
  obtain ⟨S₀, hS₀group, hidxS₀, _hfixS₀⟩ := exists_sylow_fixedField_setup (p := p) k K w
  let P : Subgroup (K ≃ₐ[k] K) := S₀.map (decompK (k := k) w).subtype
  let S : Subgroup (decompK (k := k) w) := P.comap (decompK (k := k) w).subtype
  have hPgroup : IsPGroup p P := hS₀group.map (decompK (k := k) w).subtype
  have hPD : P ≤ decompK (k := k) w := by
    rintro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hSeq : S = S₀ := by
    show (S₀.map (decompK (k := k) w).subtype).comap (decompK (k := k) w).subtype = S₀
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext (by simpa using hyx)
      rwa [← hxy]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hSindex : ¬ p ∣ S.index := by rw [hSeq]; exact hidxS₀
  -- ## Step 2: the source group is `S.comap f` and `p` divides its order
  have hfsurj : Function.Surjective f := decompK_restrict_surjective k K w L w' hw' f hf
  have hpS : p ∣ Nat.card (S.comap f) := by
    have h1 : Nat.card (S.comap f) * (S.comap f).index
        = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') := Subgroup.card_mul_index _
    have h2 : (S.comap f).index = S.index := Subgroup.index_comap_of_surjective S hfsurj
    have h3 : p ∣ Nat.card (S.comap f) * (S.comap f).index := by rw [h1]; exact hp
    rcases ((Fact.out : p.Prime).dvd_mul (m := Nat.card (S.comap f))
      (n := (S.comap f).index)).mp h3 with hh | hh
    · exact hh
    · exact absurd (h2 ▸ hh) hSindex
  -- ## Step 3: the same divisibility in the `k'`-world (Y4's hypothesis `hp`)
  have hp' : p ∣ Nat.card (MulAction.stabilizer
      (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w') :=
    Nat.card_congr (stabInclEquivL k K L P w hPD w' hw' f hf).toEquiv ▸ hpS
  -- ## Step 4: the two Sylow-level inputs of X5
  have hTS : Nat.card {x : extH (Rep.res (S.comap f).subtype
      (NK.HassePrinciple.localUnitsRep k L w')) 2 // p • x = 0} = p :=
    pTorsion_card_sylowLevel p k K w P hPD L w' hw' f hf hpS
  have hdet := rightDetect_sylowLevelStabIncl p k K w P hPgroup hPD M hM L w' hw' f hf ι hι hp'
  -- ## Step 5 (X5, Sylow descent) and the unpacking of `RightDetect` at `(h, hne)`
  exact rightDetect_of_sylow p f hfsurj S hSindex ι
    (local_pTorsion_card p k L w' hp) hTS (Rep.res (decompK (k := k) w).subtype M) hM hdet h hne



-- ===== copied from detectAbove_trivial =====


open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero




section FiniteCase


theorem detectAbove_localFixedUnits_eq_localAlgebraMapUnits
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (v : NK.GlobalCFT.Place k) (hv : NK.GlobalCFT.Place.LiesOver w v)
    (a : (NK.GlobalCFT.Place.localField K w)ˣ)
    (hafix : ∀ σ : decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a) :
    ∃ a₀ : (NK.GlobalCFT.Place.localField k v)ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits w v hv a₀ = a :=
  NK.GlobalCFT.Inclusion.globalCFT_localFixed_mem_range (K := k) (L := K) hv a
    ((localUnitsEquiv_fixed_iff_ringEquiv_fixed_general (k := k) (K := K) w a).mp hafix)


theorem detectAbove_localUnitsEquiv_localAlgebraMapUnits_eq_self
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (v : NK.GlobalCFT.Place k) (hv : NK.GlobalCFT.Place.LiesOver w v)
    (u : (NK.GlobalCFT.Place.localField k v)ˣ) (σ : decompK (k := k) w) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w σ
        (NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u)
      = NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u := by
  have h := NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower
    (F := k) (L := k) (M := K) hv σ u
  rw [← h]
  congr 1
  have hτ : (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := k) (L := k) (M := K) hv σ) = 1 :=
    Subsingleton.elim _ _
  rw [hτ, NK.HassePrinciple.localUnitsEquiv_one]
  rfl


theorem detectAbove_finite_quotientNorm_avoids
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (qw : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite qw))ˣ)
    (hafix : ∀ σ : decompK (k := k) (NK.GlobalCFT.Place.ofFinite qw),
      NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofFinite qw) σ a = a)
    (ha : ¬ ∃ b : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite qw))ˣ,
      (∀ σ : decompK (k := k) (NK.GlobalCFT.Place.ofFinite qw),
        NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofFinite qw) σ b = b) ∧
        b ^ p = a)
    (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra k L₀] [Algebra K L₀] [IsScalarTower k K L₀]
    [FiniteDimensional k L₀] [IsGalois k L₀]
    (w₀ : NK.GlobalCFT.Place L₀)
    (hw₀ : NK.GlobalCFT.Place.LiesOver w₀ (NK.GlobalCFT.Place.ofFinite qw)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra L₀ L)
      (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w₀)
      (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
      (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
      IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
          (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
            (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ (NK.GlobalCFT.Place.ofFinite qw) hw₀ a))) := by
  classical
  rcases w₀ with w₀K | q₀
  · exact absurd ((NK.GlobalCFT.Place.isFinite_of_liesOver hw₀).mpr
      (NK.GlobalCFT.Place.isFinite_ofFinite qw)) (by simp)
  · -- the base place of `k` below `q₀`
    let Qk : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
      ⟨q₀.asIdeal.under (NumberField.RingOfIntegers k), inferInstance, Ideal.under_ne_bot _ q₀.ne_bot⟩
    have hq₀Q : q₀.asIdeal.LiesOver Qk.asIdeal := Ideal.over_under q₀.asIdeal
    have hq₀qw : q₀.asIdeal.LiesOver qw.asIdeal := by
      rcases (NK.GlobalCFT.Place.liesOver_iff _ _).mp hw₀ with h | ⟨q', Q', e1, e2, hL⟩
      · obtain ⟨w', v', e1, e2, hL⟩ := h
        exact absurd e1 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q₀).symm
      · rw [NK.GlobalCFT.Place.ofFinite_inj] at e1 e2
        rw [← e1, ← e2] at hL; exact hL
    have hqwQ : qw.asIdeal.LiesOver Qk.asIdeal := by
      haveI := hq₀qw
      have hQeq : Qk.asIdeal = qw.asIdeal.under (NumberField.RingOfIntegers k) := by
        change q₀.asIdeal.under (NumberField.RingOfIntegers k) = _
        rw [Ideal.LiesOver.over (A := NumberField.RingOfIntegers K) (P := q₀.asIdeal)
              (p := qw.asIdeal),
          Ideal.under_under (A := NumberField.RingOfIntegers k) q₀.asIdeal]
      rw [hQeq]
      exact Ideal.over_under qw.asIdeal
    obtain ⟨a₀, ha₀⟩ := detectAbove_localFixedUnits_eq_localAlgebraMapUnits k K
      (NK.GlobalCFT.Place.ofFinite qw) (NK.GlobalCFT.Place.ofFinite Qk)
      (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) a hafix
    have hnotpow : ∀ b : (Qk.adicCompletion k)ˣ, b ^ p ≠ a₀ := by
      intro b hb
      apply ha
      refine ⟨NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite qw)
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) b, ?_, ?_⟩
      · intro σ
        exact detectAbove_localUnitsEquiv_localAlgebraMapUnits_eq_self k K
          (NK.GlobalCFT.Place.ofFinite qw) (NK.GlobalCFT.Place.ofFinite Qk)
          (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) b σ
      · rw [← map_pow, hb, ha₀]
    obtain ⟨E, hEf, hEA, hEfd, hEgal, hEcard, hEnorm⟩ :=
      exists_level_normGroup_not_mem_of_not_pthPower Qk p a₀ hnotpow
    obtain ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, q', hq', hq'Q, hne⟩ :=
      exists_level_local_embedding_fix k L₀ q₀ Qk hq₀Q E
    letI : Field L := hLf
    letI : NumberField L := hLn
    letI : Algebra k L := hLk
    letI : Algebra L₀ L := hLL₀
    letI : IsScalarTower k L₀ L := hST
    letI : FiniteDimensional k L := hLfd
    letI : IsGalois k L := hLgal
    obtain ⟨N, hNnorm, hNfin, hcyc, hcard, hfail⟩ :=
      norm_fail_of_local_embedding p k L Qk q' hq'Q E hEcard hne a₀ hEnorm
    letI : N.Normal := hNnorm
    letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q') ⧸ N) := hNfin
    have hstep1 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
          (NK.GlobalCFT.Place.ofFinite qw) hw₀)
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite qw)
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) a₀)
        = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q) a₀ := by
      rw [← MonoidHom.comp_apply, localAlgebraMapUnits_comp (K := k) (L := K) (M := L₀)
          hw₀ (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ)
          (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q)]
    have hstep2 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite q₀) (NK.GlobalCFT.Place.liesOver_ofFinite hq'))
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q) a₀)
        = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q) a₀ := by
      rw [← MonoidHom.comp_apply, localAlgebraMapUnits_comp (K := k) (L := L₀) (M := L)
          (NK.GlobalCFT.Place.liesOver_ofFinite hq')
          (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q)
          (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q)]
    have hkey : NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite q₀) (NK.GlobalCFT.Place.liesOver_ofFinite hq')
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
            (NK.GlobalCFT.Place.ofFinite qw) hw₀ a)
        = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q) a₀ := by
      rw [← ha₀, hstep1, hstep2]
    exact ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, NK.GlobalCFT.Place.ofFinite q',
      NK.GlobalCFT.Place.liesOver_ofFinite hq', N, hNnorm, hNfin, hcyc, hcard, by
        rw [hkey]
        exact hfail⟩

end FiniteCase


theorem detectAbove_trivial (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) :
    DetectAbove k K w (Rep.trivial Coeff (decompK (k := k) w) (ZMod p)) := by
  classical
  unfold DetectAbove
  intro L₀ hL₀f hL₀n hkL₀ hKL₀ hST₀ hfd₀ hgal₀ w₀ hw₀ f₀ hf₀ ι₀ hι₀ y hy
  by_contra hyne
  obtain ⟨φ, hφ⟩ := localUnits_pushClass_surjective p k K w y
  rw [hφ] at hyne
  let av : Additive (NK.GlobalCFT.Place.localField K w)ˣ := Rep.Hom.hom φ (1 : Coeff)
  let a : (NK.GlobalCFT.Place.localField K w)ˣ := Additive.toMul av
  have hof : (Rep.Hom.hom φ (1 : Coeff) : localUnitsK (k := k) w) = Additive.ofMul a := rfl
  have hafix : ∀ σ : decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a := by
    intro σ
    have h2 : Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) w σ a) =
        Additive.ofMul a := rep_hom_apply_one_fixed φ σ
    exact Additive.ofMul.injective h2
  have ha : ¬ ∃ bb : (NK.GlobalCFT.Place.localField K w)ˣ,
      (∀ σ : decompK (k := k) w,
        NK.HassePrinciple.localUnitsEquiv (K := k) w σ bb = bb) ∧ bb ^ p = a := by
    rintro ⟨bb, hbb, hbbp⟩
    refine not_pow_of_pushClass_lde_ne_zero_local p k K w φ hyne ⟨bb, hbb, ?_⟩
    rw [hbbp]
    exact hof
  obtain ⟨L, hLf, hLn, hAL, hAL₀, hSTL, hfdL, hgalL, w', hw', N, hN, hF, hcyc, hcard, hfail⟩ :=
    (show ∃ (L : Type 0) (_ : Field L) (_ : NumberField L) (_ : Algebra k L)
        (_ : Algebra L₀ L) (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L)
        (_ : IsGalois k L) (w' : NK.GlobalCFT.Place L)
        (hw' : NK.GlobalCFT.Place.LiesOver w' w₀)
        (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
        (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
        IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
        Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
        ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
          (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
            (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
          (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
            (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
              (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a))) from by
      rcases w with u | qw
      · exact arch_quotientNorm_avoids p k K u a hafix ha L₀ w₀ hw₀
      · exact detectAbove_finite_quotientNorm_avoids p k K qw a hafix ha L₀ w₀ hw₀)
  letI : Field L := hLf
  letI : NumberField L := hLn
  letI : Algebra k L := hAL
  letI : Algebra L₀ L := hAL₀
  letI : IsScalarTower k L₀ L := hSTL
  letI : FiniteDimensional k L := hfdL
  letI : IsGalois k L := hgalL
  letI : N.Normal := hN
  letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) := hF
  letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w') := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := decompK_restrict_exists k L₀ L w₀ w' hw'
  obtain ⟨ι₁, hι₁⟩ := localUnitsMap_exists k L₀ L w₀ w' hw' g hg
  obtain ⟨χ₀, hχ₀ne, hχ₀infl⟩ := exists_H1_inflated_ne_zero N p hcyc hcard
  obtain ⟨b⟩ := nonempty_extGroupCohomologyBridge
  set hb : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (groupCohomology.map (QuotientGroup.mk' N)
      (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom χ₀ with hbdef
  set h : extH (Rep.res (f₀.comp g) (Rep.trivial Coeff (decompK (k := k) w) (ZMod p))) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))) hb with hh
  have hne : h ≠ 0 := by
    rw [hh]
    intro h0
    exact hχ₀infl ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).injective
      (by rw [h0]; exact (map_zero _).symm))
  have hlift : ∃ hb' : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) (ZMod p)) 1,
      (groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb' =
        (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h := by
    refine ⟨χ₀, ?_⟩
    rw [hh, hbdef]
    exact ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm_apply_apply
      ((groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom χ₀)).symm
  -- The value of the level coefficient map on `1` is the image of `a` in `L_{w'}ˣ`.
  let u : (Rep.res g (Rep.res f₀ (localUnitsK (k := k) w))).V := Additive.ofMul a
  have h₁ : Rep.Hom.hom (Rep.resMap g ι₀) u
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a) :=
    hι₀ a
  have h₂ : Rep.Hom.hom (Rep.resMap g ι₀ ≫ ι₁) u
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
          (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a)) := by
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_apply]
    rw [h₁]
    exact hι₁ (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a)
  have hcomp : Rep.Hom.hom (((Rep.resFunctor (f₀.comp g)).map φ) ≫ (Rep.resMap g ι₀ ≫ ι₁))
      (1 : Coeff)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
          (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a)) := by
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_apply]
    exact h₂
  -- `y` vanishes at the level `(L, w')` with the level data `(g, ι₁)`.
  have hzero : levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁)
      (pushClass_lde p (localUnitsK (k := k) w) φ) h = 0 := by
    rw [← hφ]
    exact hy L w' hw' g hg ι₁ hι₁ h
  -- the group-cohomology class corresponding to `h` at the level `(L, w')`
  set χ : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h with hχ
  have hχne : χ ≠ 0 := by
    rw [hχ]
    intro h0
    have h1 : (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)))
        ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h) = h :=
      (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).apply_symm_apply h
    rw [h0, map_zero] at h1
    exact hne h1.symm
  have hbridge : groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[k] L) w'))
      (((Rep.resFunctor (f₀.comp g)).map φ) ≫ (Rep.resMap g ι₀ ≫ ι₁)) 2
      ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact
        (MulAction.stabilizer (L ≃ₐ[k] L) w') p) 1 2 rfl).hom χ) = 0 :=
    (levelPair_pushClass_bridge b p (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) φ h).mp hzero
  have hcrit := (normCriterion_quotient_apply_one'
      (((Rep.resFunctor (f₀.comp g)).map φ) ≫ (Rep.resMap g ι₀ ≫ ι₁))
      (fun σ => rep_hom_apply_one_fixed _ σ) N p hcyc hcard
      (hilbert90_localUnitsRep (k := k) (L := L) w' N) χ hlift hχne).mp hbridge
  rw [hcomp] at hcrit
  exact hfail hcrit




-- ===== copied from detectAbove_pgroup =====


open SSGRoute.PTExt CategoryTheory


theorem detectAbove_pgroup (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (hD : IsPGroup p (decompK (k := k) w))
    (z : Rep.trivial Coeff (decompK (k := k) w) (ZMod p) ⟶ localUnitsK (k := k) w) (hz : z ≠ 0)
    (N : Rep Coeff (decompK (k := k) w)) [Finite N] (hN : ∀ n : N, p • n = 0) :
    DetectAbove k K w N := by
  classical
  -- Strong induction on `|M|` along the dévissage `0 → 𝔽_p → M → M₂ → 0`.
  have aux : ∀ (n : ℕ) (M : Rep.{0} Coeff (decompK (k := k) w)) [Finite M],
      Nat.card M = n → (∀ m : M, p • m = 0) → DetectAbove k K w M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro M _ hcard hM
      by_cases hsub : Subsingleton M
      · -- `M` is a zero object, so `Ext¹(M, K_wˣ)` is a subsingleton.
        have hz0 : CategoryTheory.Limits.IsZero M :=
          (Rep.isZero_iff Coeff (decompK (k := k) w) M).mpr hsub
        have hid : (𝟙 M : M ⟶ M) = 0 :=
          (CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp hz0
        intro L₀ _ _ _ _ _ _ _ w₀ _hw₀ f₀ _hf₀ ι₀ _hι₀ y _hy
        have heq : y = (Abelian.Ext.mk₀ (𝟙 M)).comp y (zero_add 1) :=
          (Abelian.Ext.mk₀_id_comp y).symm
        rw [heq, hid, Abelian.Ext.mk₀_zero]
        exact Abelian.Ext.zero_comp M 0 y 1 (zero_add 1)
      · -- `p`-group, nonzero `p`-torsion module: a nonzero fixed vector spans a copy of `𝔽_p`.
        haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨M₂, i, π, hcond, hS, hFin₂, hp₂⟩ :=
          exists_trivial_sub_shortExact (G := decompK (k := k) w) p hD M hM ‹Nontrivial M›
        have hcard₁ : Nat.card (Rep.trivial Coeff (decompK (k := k) w) (ZMod p)) = p := by
          rw [Nat.card_eq_fintype_card, ZMod.card]
        have hlt : Nat.card (ShortComplex.mk i π hcond).X₃ <
            Nat.card (ShortComplex.mk i π hcond).X₂ := natCard_cokernel_lt hS hcard₁
        haveI : Finite (ShortComplex.mk i π hcond).X₃ := hFin₂
        have hIH : DetectAbove k K w (ShortComplex.mk i π hcond).X₃ := by
          refine ih (Nat.card (ShortComplex.mk i π hcond).X₃) ?_
            (ShortComplex.mk i π hcond).X₃ rfl hp₂
          rw [← hcard]
          exact hlt
        exact detectAbove_sub_step p k K w z hz (ShortComplex.mk i π hcond) hS (Iso.refl _)
          hM (detectAbove_trivial p k K w) hIH
  exact aux (Nat.card N) N rfl hN



-- ===== copied from local_duality_ext_realization_of_detection =====


open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000




theorem zmod_prime_linearEquiv_of_card_eq (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod p) A] [Finite A] (hcard : Nat.card A = p) :
    Nonempty (A ≃ₗ[ZMod p] ZMod p) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    omega
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  have hinj : Function.Injective (LinearMap.toSpanSingleton (ZMod p) A x) := by
    intro c d hcd
    simp only [LinearMap.toSpanSingleton_apply] at hcd
    have h : (c - d) • x = 0 := by rw [sub_smul, hcd, sub_self]
    rcases smul_eq_zero.mp h with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hx
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (ZMod p) A x) := by
    have hcu : (Finset.univ.image (LinearMap.toSpanSingleton (ZMod p) A x)).card
        = Fintype.card A := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod, hcard]
    have huniv : Finset.univ.image (LinearMap.toSpanSingleton (ZMod p) A x) = Finset.univ :=
      Finset.eq_univ_of_card _ hcu
    intro a
    have hmem : a ∈ Finset.univ.image (LinearMap.toSpanSingleton (ZMod p) A x) := by
      rw [huniv]; exact Finset.mem_univ a
    rw [Finset.mem_image] at hmem
    obtain ⟨b, _, hb⟩ := hmem
    exact ⟨b, hb⟩
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm⟩


theorem realization_of_detection_pairing
    (p : ℕ) [Fact p.Prime]
    (V W T : Type) [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Module (ZMod p) V] [Module (ZMod p) W] [Finite W]
    [Module (ZMod p) ↥(AddSubgroup.torsionBy (A := T) p)]
    (e : ↥(AddSubgroup.torsionBy (A := T) p) ≃ₗ[ZMod p] ZMod p)
    (pair : V → W → T)
    (hadd_v : ∀ v₁ v₂ w, pair (v₁ + v₂) w = pair v₁ w + pair v₂ w)
    (hsmul_v : ∀ (c : ZMod p) v w, pair (c • v) w = c.val • pair v w)
    (hadd_w : ∀ v w₁ w₂, pair v (w₁ + w₂) = pair v w₁ + pair v w₂)
    (hsmul_w : ∀ (c : ZMod p) v w, pair v (c • w) = c.val • pair v w)
    (htors : ∀ v w, (p : ℕ) • pair v w = 0)
    (hdet : ∀ w, w ≠ 0 → ∃ v, pair v w ≠ 0)
    (lam : W →+ T) (hlam : ∀ w, (p : ℕ) • lam w = 0) :
    ∃ v, ∀ w, pair v w = lam w := by
  classical
  haveI : FiniteDimensional (ZMod p) W := Module.Finite.of_finite
  have memTors : ∀ v w, pair v w ∈ AddSubgroup.torsionBy (A := T) p :=
    fun v w => AddSubgroup.torsionBy.nsmul_iff.mpr (htors v w)
  have hcoe : ∀ (c : ZMod p) (x : ↥(AddSubgroup.torsionBy (A := T) p)),
      ((c • x : ↥(AddSubgroup.torsionBy (A := T) p)) : T) = c.val • (x : T) := by
    intro c x
    have h1 : c • x = c.val • x := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val x, ZMod.natCast_zmod_val c]
    rw [h1]
    exact AddSubgroup.coe_nsmul _ x c.val
  let B : V →ₗ[ZMod p] W →ₗ[ZMod p] ZMod p :=
    LinearMap.mk₂ (ZMod p) (fun v w => e ⟨pair v w, memTors v w⟩)
      (fun v₁ v₂ w => by
        have h : (⟨pair (v₁+v₂) w, memTors (v₁+v₂) w⟩ :
              ↥(AddSubgroup.torsionBy (A := T) p))
            = ⟨pair v₁ w, memTors v₁ w⟩ + ⟨pair v₂ w, memTors v₂ w⟩ :=
          Subtype.ext (hadd_v v₁ v₂ w)
        rw [h, map_add])
      (fun c v w => by
        have h : (⟨pair (c • v) w, memTors (c • v) w⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = c • ⟨pair v w, memTors v w⟩ := by
          apply Subtype.ext
          rw [hcoe c ⟨pair v w, memTors v w⟩]
          exact hsmul_v c v w
        rw [h, map_smul])
      (fun v w₁ w₂ => by
        have h : (⟨pair v (w₁+w₂), memTors v (w₁+w₂)⟩ :
              ↥(AddSubgroup.torsionBy (A := T) p))
            = ⟨pair v w₁, memTors v w₁⟩ + ⟨pair v w₂, memTors v w₂⟩ :=
          Subtype.ext (hadd_w v w₁ w₂)
        rw [h, map_add])
      (fun c v w => by
        have h : (⟨pair v (c • w), memTors v (c • w)⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = c • ⟨pair v w, memTors v w⟩ := by
          apply Subtype.ext
          rw [hcoe c ⟨pair v w, memTors v w⟩]
          exact hsmul_w c v w
        rw [h, map_smul])
  have hdetB : ∀ w : W, w ≠ 0 → ∃ v, B v w ≠ 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hdet w hw
    refine ⟨v, fun h0 => hv ?_⟩
    have h1 : (⟨pair v w, memTors v w⟩ : ↥(AddSubgroup.torsionBy (A := T) p)) = 0 := by
      refine e.injective ?_
      rw [map_zero]
      exact h0
    exact congrArg Subtype.val h1
  have hflip : Function.Injective B.flip := by
    intro w w' hww'
    by_contra hne
    obtain ⟨v, hv⟩ := hdetB (w - w') (sub_ne_zero.mpr hne)
    exact hv (by
      have h0 : B.flip (w - w') = 0 := by rw [map_sub, hww', sub_self]
      have := congrArg (fun g : V →ₗ[ZMod p] ZMod p => g v) h0
      simpa [LinearMap.flip_apply] using this)
  have hsurj : Function.Surjective B := LinearMap.flip_injective_iff₂.mp hflip
  have memTorsL : ∀ w, lam w ∈ AddSubgroup.torsionBy (A := T) p :=
    fun w => AddSubgroup.torsionBy.nsmul_iff.mpr (hlam w)
  let ψ : W →ₗ[ZMod p] ZMod p :=
    { toFun := fun w => e ⟨lam w, memTorsL w⟩
      map_add' := fun w₁ w₂ => by
        have h : (⟨lam (w₁+w₂), memTorsL (w₁+w₂)⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = ⟨lam w₁, memTorsL w₁⟩ + ⟨lam w₂, memTorsL w₂⟩ :=
          Subtype.ext (map_add lam w₁ w₂)
        rw [h, map_add]
      map_smul' := fun c w => by
        have h1 : c • w = c.val • w := by
          rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val w, ZMod.natCast_zmod_val c]
        have h : (⟨lam (c • w), memTorsL (c • w)⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = c • ⟨lam w, memTorsL w⟩ := by
          apply Subtype.ext
          rw [hcoe c ⟨lam w, memTorsL w⟩]
          change lam (c • w) = c.val • lam w
          rw [h1, map_nsmul lam c.val w]
        rw [h, map_smul]
        simp }
  obtain ⟨v, hv⟩ := hsurj ψ
  refine ⟨v, fun w => ?_⟩
  have h2 : B v w = ψ w := by rw [hv]
  exact congrArg Subtype.val (e.injective h2)


theorem local_duality_ext_realization_of_detection
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (hdet : ∀ h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1, h ≠ 0 →
      ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
        levelPair f ι y h ≠ 0) :
    ∀ lam : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1 →+
        extH (NK.HassePrinciple.localUnitsRep k L w') 2,
      (∀ h, p • lam h = 0) →
      ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
        ∀ h, levelPair f ι y h = lam h := by
  classical
  intro lam hlam
  -- abbreviations for the three groups appearing
  -- `V = Ext¹_{D_w}(M, K_wˣ)`, `W = H¹(D_{w'}, M)`, `T = H²(D_{w'}, L_{w'}ˣ)`
  -- `p`-torsion of the coefficient module `M`, transported through restriction
  have hMres : ∀ x : Rep.res (decompK (k := k) w).subtype M, p • x = 0 := fun x => hM x
  have hMres' : ∀ x : Rep.res f (Rep.res (decompK (k := k) w).subtype M), p • x = 0 :=
    fun x => hM x
  -- the source `V` is a `ZMod p`-module
  have hVp : ∀ v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
      (localUnitsK (k := k) w) 1, p • v = 0 :=
    fun v => ext_nsmul_p_torsion_left p hMres v
  letI : Module (ZMod p) (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
      (localUnitsK (k := k) w) 1) := AddCommGroup.zmodModule (n := p) hVp
  -- the target `W` is a `ZMod p`-module, and finite
  have hWp : ∀ h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1, p • h = 0 :=
    fun h => ext_nsmul_p_torsion p hMres' h
  letI : Module (ZMod p) (extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1) :=
    AddCommGroup.zmodModule (n := p) hWp
  haveI : Finite (MulAction.stabilizer (L ≃ₐ[k] L) w') := inferInstance
  haveI : Finite (extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1) :=
    local_duality_ext_extH_finite _ 1
  -- the `p`-torsion of `T = H²(D_{w'}, L_{w'}ˣ)` is `ZMod p`
  haveI : Module (ZMod p)
      ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) :=
    AddSubgroup.torsionBy.zmodModule
  have hcardT : Nat.card
      ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) = p :=
    (Nat.card_congr (Equiv.subtypeEquivRight
        (fun x => AddSubgroup.torsionBy.nsmul_iff (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) (n := p)))).trans
      (local_pTorsion_card p k L w' hp)
  haveI : Finite ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) :=
    (Nat.card_ne_zero.mp (by rw [hcardT]; exact (Fact.out : p.Prime).ne_zero)).2
  obtain ⟨e⟩ := zmod_prime_linearEquiv_of_card_eq p
    ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) hcardT
  have hv_add : ∀ (v₁ v₂ : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι (v₁ + v₂) h = levelPair f ι v₁ h + levelPair f ι v₂ h :=
    fun v₁ v₂ h => levelPair_add f ι v₁ v₂ h
  have hv_smul : ∀ (c : ZMod p)
      (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι (c • v) h = c.val • levelPair f ι v h := by
    intro c v h
    have hcv : c • v = c.val • v := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val v, ZMod.natCast_zmod_val c]
    let hvadd : (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
          (localUnitsK (k := k) w) 1) →+ extH (NK.HassePrinciple.localUnitsRep k L w') 2 :=
      { toFun := fun x => levelPair f ι x h
        map_zero' := levelPair_zero f ι h
        map_add' := fun a b => levelPair_add f ι a b h }
    rw [hcv]
    simpa [hvadd] using map_nsmul hvadd c.val v
  have hw_add : ∀ (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w) 1)
      (h₁ h₂ : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι v (h₁ + h₂) = levelPair f ι v h₁ + levelPair f ι v h₂ :=
    fun v h₁ h₂ => levelPair_add_h f ι v h₁ h₂
  have hw_smul : ∀ (c : ZMod p)
      (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι v (c • h) = c.val • levelPair f ι v h := by
    intro c v h
    have hcw : c • h = c.val • h := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val h, ZMod.natCast_zmod_val c]
    rw [hcw]
    exact map_nsmul (levelPairFunctional (f := f) (ι := ι) (r := 1) (s := 1) v) c.val h
  have htors : ∀ (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      p • levelPair f ι v h = 0 := by
    intro v h
    let hvadd : (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
          (localUnitsK (k := k) w) 1) →+ extH (NK.HassePrinciple.localUnitsRep k L w') 2 :=
      { toFun := fun x => levelPair f ι x h
        map_zero' := levelPair_zero f ι h
        map_add' := fun a b => levelPair_add f ι a b h }
    have h1 := map_nsmul hvadd p v
    rw [hVp v, map_zero] at h1
    simpa [hvadd] using h1.symm
  -- assemble: the pairing is bilinear and detects, so finite duality realises `lam`
  exact realization_of_detection_pairing p
    (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
    (extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1)
    (extH (NK.HassePrinciple.localUnitsRep k L w') 2)
    e (fun v h => levelPair f ι v h) hv_add hv_smul hw_add hw_smul htors hdet lam hlam




end Work.SSGRoute.E7bFin

/-! ## Copied from `Submission/Work/SSGRoute/E7bZ8/detect_levels.lean` (Z8, clause (i))

The lane module is in the import closure of this file, so its content cannot be imported here;
this is a faithful copy in the fresh namespace `Work.SSGRoute.E7bZ8In`, with the one reference
to `Work.SSGRoute.detectAbove_pgroup` redirected to the local copy `Work.SSGRoute.E7bFin.detectAbove_pgroup`.
-/

namespace Work.SSGRoute.E7bZ8In

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Auxiliary `Ext`-algebra for the level change -/

/-- **The two descriptions of the restriction of a class to the preimage subgroup**: restricting a
class first to a subgroup `S` and then to the preimage `S.comap f` agrees with restricting first
along `f` and then to the preimage. -/
theorem extRes_subgroupComap_eq {G D : Type} [Group G] [Group D] (f : G →* D) (S : Subgroup D)
    {M A : Rep Coeff D} (y : Abelian.Ext M A 1) :
    extRes (f.subgroupComap S) (extRes S.subtype y) = extRes (S.comap f).subtype (extRes f y) := by
  rw [← Work.SSGRoute.SylowDesc.extRes_comp_aux S.subtype (f.subgroupComap S) y,
    ← Work.SSGRoute.SylowDesc.extRes_comp_aux f (S.comap f).subtype y]
  congr 1

/-- **The level pairing only depends on the restriction of the class**: computing the level pairing
of the `S`-restricted class with the level map `f.subgroupComap S` is the same as computing the
level pairing of the `f`-restricted class along the subgroup inclusion. -/
theorem levelPair_subgroupComap_restrict {G D : Type} [Group G] [Group D] (f : G →* D)
    (S : Subgroup D) {M A : Rep Coeff D} {B : Rep Coeff G} (ι : Rep.res f A ⟶ B)
    (y : Abelian.Ext M A 1)
    (h : extH (Rep.res (f.subgroupComap S) (Rep.res S.subtype M)) 1) :
    levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι) (extRes S.subtype y) h =
      levelPair (S.comap f).subtype (Rep.resMap (S.comap f).subtype ι) (extRes f y) h := by
  simp only [SSGRoute.PTExt.levelPair]
  rw [extRes_subgroupComap_eq f S y]
  rfl

/-- The reassociation of the Yoneda product occurring in the projection formula: the composite
`(t ∘ x) ∘ (mk₀ ι)` is the level pairing `levelPair f ι x t`. -/
theorem comp_comp_mk0_eq_levelPair {G D : Type} [Group G] [Group D] (f : G →* D)
    {M A : Rep Coeff D} {B : Rep Coeff G} (ι : Rep.res f A ⟶ B)
    (y : Abelian.Ext M A 1) (t : extH (Rep.res f M) 1) :
    (t.comp (extRes f y) rfl).comp (Abelian.Ext.mk₀ ι) (add_zero (1 + 1)) = levelPair f ι y t := by
  simp only [SSGRoute.PTExt.levelPair]
  exact Abelian.Ext.comp_assoc t (extRes f y) (Abelian.Ext.mk₀ ι) rfl (add_zero 1)
    (add_zero (1 + 1))

/-! ## Projection formula for the Sylow-restricted level pairing -/

/-- **The Sylow-restricted level pairing is detected by the level-`D` pairing.**  If `y` pairs to
zero with everything at the level `G`, then the pairing of its `S`-restriction at the level
`S' = S.comap f` is zero, provided corestriction is injective on the `p`-torsion of `H²(S', B)`
(this injectivity is the arithmetic input supplied by the caller). -/
theorem levelPair_subgroup_vanish {G D : Type} [Group G] [Group D] [Fintype G] [Fintype D]
    (S : Subgroup D) [DecidableRel (QuotientGroup.rightRel S)] [Fintype (D ⧸ S)]
    (f : G →* D) [DecidableRel (QuotientGroup.rightRel (S.comap f))]
    [Fintype (G ⧸ S.comap f)]
    (p : ℕ) {M A : Rep Coeff D} {B : Rep Coeff G} (ι : Rep.res f A ⟶ B)
    (hM : ∀ m : M, p • m = 0)
    (y : Abelian.Ext M A 1)
    (hy : ∀ t : extH (Rep.res f M) 1, levelPair f ι y t = 0)
    (hker : ∀ t : extH (Rep.res (S.comap f).subtype B) (1 + 1), p • t = 0 →
      Work.SSGRoute.extCor (S.comap f) (unitRep G) B (1 + 1) t = 0 → t = 0)
    (h : extH (Rep.res (S.comap f).subtype (Rep.res f M)) 1) :
    levelPair (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι) (extRes S.subtype y) h = 0 := by
  rw [levelPair_subgroupComap_restrict f S ι y h]
  refine hker _ ?_ ?_
  · -- the value is `p`-torsion because `h` is
    have hh : p • h = 0 :=
      Work.SSGRoute.E6Util.ext_nsmul_p_torsion p
        (A := Rep.res (S.comap f).subtype (Rep.res f M)) (fun m => hM m) h
    simp only [SSGRoute.PTExt.levelPair]
    rw [← Work.SSGRoute.nsmul_comp_aux p h ((extRes (S.comap f).subtype (extRes f y)).comp
      (Abelian.Ext.mk₀ (Rep.resMap (S.comap f).subtype ι)) rfl) rfl]
    rw [hh, Abelian.Ext.zero_comp]
  · -- the corestriction is the level-`G` pairing with `cor h`, which vanishes by hypothesis
    rw [Work.SSGRoute.E6Calc.extCor_levelPair (S := S.comap f) (x := extRes f y) (b := h)
      (c := ι)]
    exact (comp_comp_mk0_eq_levelPair f ι y (Work.SSGRoute.extCor (S.comap f)
      (unitRep G) (Rep.res f M) 1 h)).trans (hy _)

/-! ## Corestriction is injective on the `p`-torsion of `H²` -/

/-- **Corestriction is injective on the `p`-torsion of `H²(S, res_S B)`** when the index `[G : S]`
is prime to `p` and both `p`-torsion groups have `Nat.gcd p |·|` elements.  This is the dichotomy
`|T_S| ∈ {1, p}` of the Sylow descent, using `extCor_two_injective_pTorsion`. -/
theorem extCor_injective_pTorsion_of_card (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (S : Subgroup G) [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]
    (hS : ¬ p ∣ S.index) (B : Rep Coeff G)
    (hcardG : Nat.card {x : extH B 2 // p • x = 0} = Nat.gcd p (Nat.card G))
    (hcardS : Nat.card {x : extH (Rep.res S.subtype B) 2 // p • x = 0} = Nat.gcd p (Nat.card S)) :
    ∀ t : extH (Rep.res S.subtype B) (1 + 1), p • t = 0 →
      extCor S (unitRep G) B (1 + 1) t = 0 → t = 0 := by
  intro t ht h0
  by_cases hpS : p ∣ Nat.card S
  · have hpG : p ∣ Nat.card G := hpS.trans (Subgroup.card_subgroup_dvd_card S)
    have hTG : Nat.card {x : extH B 2 // p • x = 0} = p := by
      rw [hcardG, Nat.gcd_eq_left hpG]
    have hTS : Nat.card {x : extH (Rep.res S.subtype B) 2 // p • x = 0} = p := by
      rw [hcardS, Nat.gcd_eq_left hpS]
    exact Work.SSGRoute.extCor_two_injective_pTorsion p S hS B hTG hTS t ht h0
  · have hg : Nat.gcd p (Nat.card S) = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hpS
    have h1 : Nat.card {x : extH (Rep.res S.subtype B) 2 // p • x = 0} = 1 := by
      rw [hcardS, hg]
    have h1' : Nat.card {x : extH (Rep.res S.subtype B) (1 + 1) // p • x = 0} = 1 := h1
    haveI : Subsingleton {x : extH (Rep.res S.subtype B) (1 + 1) // p • x = 0} :=
      (Nat.card_eq_one_iff_unique.mp h1').1
    exact Subtype.ext_iff.mp (Subsingleton.elim
      (⟨t, ht⟩ : {x : extH (Rep.res S.subtype B) (1 + 1) // p • x = 0})
      ⟨0, by simp⟩)




/-! ## The fixed field of a subgroup of the decomposition group -/

/-- **The action on places only sees the underlying function.** -/
theorem place_smul_rst (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k k'] [Algebra k' K] [Algebra k K]
    [IsScalarTower k k' K] (σ : K ≃ₐ[k'] K) (w : NK.GlobalCFT.Place K) :
    (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K) σ) • w = σ • w := by
  cases w <;> rfl

/-- **The image of the decomposition group of `w` over the fixed field `K^P` is `P`.** -/
theorem map_rst_decompK_fixedField (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K)) (hPD : P ≤ decompK (k := k) w) :
    (decompK (k := ↥(IntermediateField.fixedField P)) w).map
      (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
        (A := K)) = P := by
  classical
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, -, rfl⟩
    have hmem : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
        (A := K) σ) ∈ (IntermediateField.fixedField P).fixingSubgroup :=
      ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)).symm σ).2
    rwa [IntermediateField.fixingSubgroup_fixedField P] at hmem
  · intro hx
    have hx' : x ∈ (IntermediateField.fixedField P).fixingSubgroup := by
      rwa [IntermediateField.fixingSubgroup_fixedField P]
    refine ⟨(IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)) ⟨x, hx'⟩,
      ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      rw [← place_smul_rst k ↥(IntermediateField.fixedField P) K]
      have hrst : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
          (A := K) ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P))
            ⟨x, hx'⟩)) = x :=
        AlgEquiv.ext fun y => rfl
      rw [hrst]
      exact MulAction.mem_stabilizer_iff.mp (hPD hx)
    · exact AlgEquiv.ext fun y => rfl

/-! ## Places and the fixed field of a Sylow subgroup -/

/-- The place `w` lies over itself, for the trivial extension `K / K`. -/
theorem place_liesOver_self (K : Type) [Field K] [NumberField K] (w : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Place.LiesOver w w := by
  rcases w with w | q
  · refine NK.GlobalCFT.Place.liesOver_ofInfinite ?_
    exact (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w w).mpr (NumberField.InfinitePlace.comap_id w)
  · refine NK.GlobalCFT.Place.liesOver_ofFinite ?_
    exact (NK.GlobalCFT.Norm.liesOver_iff_under_eq q.asIdeal q.asIdeal).mpr (by
      rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id])

/-- The base-change subgroup attached to a subgroup `S ≤ D_w` is, for the fixed field `k' = K^S`,
the subgroup `S` itself. -/
theorem sylowBaseChangeSubgroup_eq (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (S : Subgroup (decompK (k := k) w)) :
    (((decompK (k := ↥(IntermediateField.fixedField (galSub (k := k) w S))) w).map
        (AlgEquiv.restrictScalarsHom (R := k)
          (S := ↥(IntermediateField.fixedField (galSub (k := k) w S))) (A := K))).comap
      (decompK (k := k) w).subtype) = S := by
  have hPD : galSub (k := k) w S ≤ decompK (k := k) w := galSub_le (k := k) w S
  have hmr := map_rst_decompK_fixedField k K w (galSub (k := k) w S) hPD
  rw [hmr]
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : y = x := Subtype.ext (by simpa using hyx)
    rwa [← hxy]
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A primitive `p`-th root of unity in `K` is fixed by the decomposition group of `w` over the
fixed field `K^S` of a `p`-subgroup `S ≤ D_w`. -/
theorem fixedBase_zeta_fixed (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (w : NK.GlobalCFT.Place K)
    (S : Subgroup (decompK (k := k) w)) (hS : IsPGroup p ↥S) :
    ∀ σ : decompK (k := fixedBase (k := k) w S) w,
      (σ : K ≃ₐ[fixedBase (k := k) w S] K) ζ = ζ := by
  have hPD : galSub (k := k) w S ≤ decompK (k := k) w := galSub_le (k := k) w S
  have hmr := map_rst_decompK_fixedField k K w (galSub (k := k) w S) hPD
  have hfixP : ∀ σ ∈ galSub (k := k) w S, σ ζ = ζ :=
    pgroup_fixes_primitiveRoot p k K ζ hζ (galSub (k := k) w S)
      (isPGroup_galSub (k := k) w S hS)
  intro σ
  refine hfixP (AlgEquiv.restrictScalarsHom (R := k) (S := fixedBase (k := k) w S) (A := K) σ) ?_
  have hmem : AlgEquiv.restrictScalarsHom (R := k) (S := fixedBase (k := k) w S) (A := K) σ
      ∈ (decompK (k := ↥(IntermediateField.fixedField (galSub (k := k) w S))) w).map
          (AlgEquiv.restrictScalarsHom (R := k)
            (S := ↥(IntermediateField.fixedField (galSub (k := k) w S))) (A := K)) :=
    Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩
  rw [hmr] at hmem
  exact hmem

/-! ## The target -/

/-- **E7b clause (i)**: the local pairing at the base level `K` has trivial left radical over all
levels. -/
theorem detect_levels (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (ζ : K) (hζ : IsPrimitiveRoot ζ p) (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0) (w : NK.GlobalCFT.Place K) : ∀ y : CategoryTheory.Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M) (SSGRoute.PTExt.localUnitsK (k := k) w) 1, (∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L] (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w) (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w) (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K) = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L)) (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w') (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ, ι.hom (Additive.ofMul u) = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u)) (h : SSGRoute.PTExt.extH (Rep.res f (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)) 1), SSGRoute.PTExt.levelPair f ι y h = 0) → y = 0 := by
  classical
  intro y hy
  -- Step 1: the hypothesis is the base-level cone hypothesis over `k`.
  have hyV : VanishesAbove k K y K w (MonoidHom.id _) (𝟙 _) :=
    vanishesAbove_base p k K w M y hy
  -- Step 2: a Sylow `p`-subgroup `S₀ ≤ D_w` and the fixed field `k' = K^S₀`.
  obtain ⟨S₀, hS₀grp, hS₀idx⟩ := Work.SSGRoute.exists_isPGroup_sylow_decompK p k K w
  let k' : Type := ↥(IntermediateField.fixedField (galSub (k := k) w S₀))
  let Mr : Rep Coeff (K ≃ₐ[k'] K) :=
    Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M
  let Sbc : Subgroup (decompK (k := k) w) :=
    ((decompK (k := k') w).map (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))).comap
      (decompK (k := k) w).subtype
  have hidx : ¬ p ∣ Sbc.index := by
    rw [show Sbc = S₀ from sylowBaseChangeSubgroup_eq k K w S₀]
    exact hS₀idx
  -- Step 3: the base change `k → k'`.
  obtain ⟨-, eE, hY3⟩ := levelPair_baseChange_fullC p k k' K w M
  let N' : Rep Coeff (decompK (k := k') w) := Rep.res (decompK (k := k') w).subtype Mr
  -- Step 4: the cone hypothesis at the base `k'` (the Sylow descent).
  have hV' : VanishesAbove k' K (eE (extRes Sbc.subtype y)) K w (MonoidHom.id _) (𝟙 _) := by
    intro L hFL hNFL hA1L hA2L hSTL hFinL hGalL w' hw' g hg ι₁ hι₁ h
    letI := hFL
    letI := hNFL
    letI := hA1L
    letI := hA2L
    letI := hSTL
    letI := hFinL
    letI := hGalL
    -- a `k`-algebra structure on `L` exhibiting the tower `k ⊆ k' ⊆ L`
    letI : Algebra k L := RingHom.toAlgebra ((algebraMap k' L).comp (algebraMap k k'))
    letI : SMul k' L := Algebra.toSMul
    haveI : IsScalarTower k k' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    -- the Galois closure of the `k'`-level `L` over `k`, and a place `wc` above `w'` above `w`
    obtain ⟨Lc, hLcF, hLcNF, hLcA1, hLcA2, hLcA3, hLcA4, hLcF5, hLcF6, hLcF7, hLcF8, hLcF9,
      hLcF10, hLcF11, hLcF12, hLcF13, hLcF14, hLcF15, wc, hwcw', hwcw⟩ :=
      Work.SSGRoute.exists_galoisClosure_level k k' K L w w' hw'
    letI := hLcF
    letI := hLcNF
    letI := hLcA1
    letI := hLcA2
    letI := hLcA3
    letI := hLcA4
    letI := hLcF5
    letI := hLcF6
    letI := hLcF7
    letI := hLcF8
    letI := hLcF9
    letI := hLcF10
    letI := hLcF11
    letI := hLcF12
    letI := hLcF13
    letI := hLcF14
    letI := hLcF15
    -- the closure-level vanishing, for every choice of `k'`-level data
    have htop : ∀ (fc : MulAction.stabilizer (Lc ≃ₐ[k'] Lc) wc →* decompK (k := k') w)
        (hfc : ∀ σ, ((fc σ : decompK (k := k') w) : K ≃ₐ[k'] K) =
          galRes k' K Lc (σ : Lc ≃ₐ[k'] Lc))
        (ιc : Rep.res fc (localUnitsK (k := k') w) ⟶ NK.HassePrinciple.localUnitsRep k' Lc wc)
        (hιc : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ, ιc.hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits wc w hwcw u))
        (hc : extH (Rep.res fc (Rep.res (decompK (k := k') w).subtype Mr)) 1),
        levelPair fc ιc (eE (extRes Sbc.subtype y)) hc = 0 := by
      intro fc hfc ιc hιc hc
      -- the `k`-level data at `Lc`
      obtain ⟨f, hf⟩ := Work.SSGRoute.decompK_restrict_exists k K Lc w wc hwcw
      obtain ⟨ι, hι⟩ := Work.SSGRoute.localUnitsMap_exists k K Lc w wc hwcw f hf
      -- the base change at `Lc`
      obtain ⟨hY3a, hY3b, eH, eB, hY3eq⟩ := hY3 Lc wc hwcw f hf ι hι fc hfc ιc hιc
      -- the two `p`-torsion cardinalities of the dichotomy
      have hcardG : Nat.card {x : SSGRoute.PTExt.extH
            (NK.HassePrinciple.localUnitsRep k Lc wc) 2 // p • x = 0}
          = Nat.gcd p (Nat.card (MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc)) :=
        Work.SSGRoute.Z8.localUnits_extH_pTorsion_card_gcd p k Lc wc
      have hcardS : Nat.card {x : SSGRoute.PTExt.extH (Rep.res (Sbc.comap f).subtype
            (NK.HassePrinciple.localUnitsRep k Lc wc)) 2 // p • x = 0}
          = Nat.gcd p (Nat.card (Sbc.comap f)) := by
        have h1 : Nat.card (decompK (k := k') wc) = Nat.card (Sbc.comap f) := hY3a
        rw [hY3b, Work.SSGRoute.Z8.localUnits_extH_pTorsion_card_gcd p k' Lc wc, h1]
      haveI : Fintype (MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc) := Fintype.ofFinite _
      haveI : Fintype ((MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc) ⧸ Sbc.comap f) :=
        Fintype.ofFinite _
      have hidxS : ¬ p ∣ (Sbc.comap f).index := by
        rw [Subgroup.index_comap_of_surjective Sbc
          (Work.SSGRoute.decompK_restrict_surjective k K w Lc wc hwcw f hf)]
        exact hidx
      -- corestriction is injective on the `p`-torsion at the level `Sbc.comap f`
      have hkerf := extCor_injective_pTorsion_of_card p (Sbc.comap f) hidxS
        (NK.HassePrinciple.localUnitsRep k Lc wc) hcardG hcardS
      -- the level-`Sbc.comap f` pairing vanishes
      have hP2 := levelPair_subgroup_vanish (G := MulAction.stabilizer (Lc ≃ₐ[k] Lc) wc) Sbc f p ι
        (fun m => hM m) y (fun t => hy Lc wc hwcw f hf ι hι t) hkerf (eH.symm hc)
      -- the interlacing identity of the base change
      have key := hY3eq (extRes Sbc.subtype y) (eH.symm hc)
      rw [AddEquiv.apply_symm_apply, hP2, map_zero] at key
      exact key
    -- descend from the closure to `L`
    have hP4 := Work.SSGRoute.Z8.levelPair_vanish_of_vanish_closure (k' := k') (K := K) w Mr
      (eE (extRes Sbc.subtype y)) L w' hw' Lc wc hwcw' hwcw htop
    have hA : (MonoidHom.id (decompK (k := k') w)).comp g = g := MonoidHom.id_comp g
    have hB : Rep.resMap g (𝟙 (Rep.res (MonoidHom.id (decompK (k := k') w))
        (localUnitsK (k := k') w))) ≫ ι₁ = ι₁ := by
      rw [Work.SSGRoute.resMap_id]
      exact Category.id_comp ι₁
    try rw [hA]
    rw [hB]
    exact hP4 g hg ι₁ hι₁ h
  -- Step 5: detection at the base `k'`, where `D_w` is a `p`-group.
  have hD' : IsPGroup p (decompK (k := k') w) :=
    isPGroup_decompK_fixedBase (k := k) w S₀ hS₀grp
  obtain ⟨u, z, hu, hz, hzm⟩ :=
    Work.SSGRoute.exists_localZetaCoeff p k' K w ζ hζ
      (fixedBase_zeta_fixed p k K ζ hζ w S₀ hS₀grp)
  haveI hfinN' : Finite N' := ‹Finite M›
  have hN' : ∀ n : N', p • n = 0 := fun n => hM n
  have hdet : DetectAbove k' K w N' :=
    Work.SSGRoute.E7bFin.detectAbove_pgroup p k' K w hD' z hz N' hN'
  have hy'0 : eE (extRes Sbc.subtype y) = 0 :=
    hdet K w (place_liesOver_self K w) (MonoidHom.id _)
      (fun σ => by
        have h : galRes k' K K = MonoidHom.id (K ≃ₐ[k'] K) := AlgEquiv.restrictNormalHom_id k' K
        rw [h]
        rfl)
      (𝟙 _)
      (fun u => by
        rw [localAlgebraMapUnits_self K w (place_liesOver_self K w) u]
        rfl)
      _ hV'
  -- Step 6: injectivity of `eE` and of `extRes`.
  have h1 : extRes Sbc.subtype y = 0 := by
    refine eE.injective ?_
    rw [map_zero]
    exact hy'0
  have h2 : extRes S₀.subtype y = 0 := by
    rw [← sylowBaseChangeSubgroup_eq k K w S₀]
    exact h1
  haveI : Fintype (decompK (k := k) w) := Fintype.ofFinite _
  haveI : Fintype ((decompK (k := k) w) ⧸ S₀) := Fintype.ofFinite _
  haveI : Finite (Rep.res (decompK (k := k) w).subtype M) := ‹Finite M›
  refine Work.SSGRoute.extRes_injective_of_index (p := p) (S := S₀) hS₀idx
    (Rep.res (decompK (k := k) w).subtype M) hM (localUnitsK (k := k) w) ?_
  change extRes S₀.subtype y = extRes S₀.subtype 0
  rw [h2]
  exact (map_zero ((Rep.resFunctor S₀.subtype).mapExtAddHom
    (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)).symm

end Work.SSGRoute.E7bZ8In


/-- **E7b.** Canonical local duality in `Ext` form at a place `w` of `K` (`μ_p ⊆ K`, `M` finite
`p`-torsion): the Yoneda pairing of `Ext¹_{D_w}(M, K_wˣ)` with `H¹(D_{w'}, M)` into
`H²(D_{w'}, L_{w'}ˣ) = Br(L_{w'}/k_v)`, over the levels `L ⊇ K` and places `w' ∣ w`, (i) has no
left kernel, and (ii) at a level with `p ∣ [L_{w'} : k_v]` realises every `p`-torsion functional. -/
theorem local_duality_ext (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K) :
    (∀ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
      (∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
        [FiniteDimensional k L] [IsGalois k L]
        (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
        (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
        (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
        (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
        (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
          ι.hom (Additive.ofMul u) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
        (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
        levelPair f ι y h = 0) → y = 0) ∧
    ∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
      (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
      (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
      (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
      (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι.hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u)),
      p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') →
      ∀ lam : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1 →+
          extH (NK.HassePrinciple.localUnitsRep k L w') 2,
        (∀ h, p • lam h = 0) →
        ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
          ∀ h, levelPair f ι y h = lam h := by
  refine ⟨Work.SSGRoute.E7bZ8In.detect_levels p k K ζ hζ M hM w, ?_⟩
  intro L _ _ _ _ _ _ _ w' hw' f hf ι hι hp lam hlam
  exact Work.SSGRoute.E7bFin.local_duality_ext_realization_of_detection p k K M hM w
    L w' hw' f hf ι hι hp
    (fun h hne => Work.SSGRoute.E7bFin.local_duality_ext_detect_h p k K ζ hζ M hM w
      L w' hw' f hf ι hι hp h hne)
    lam hlam

end Work.SSGRoute
