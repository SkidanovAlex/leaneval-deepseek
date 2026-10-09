/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.IdeleNorm
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.Norm
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.Reciprocity
import Submission.NK.GlobalCFT.ClassFormation
import Submission.NK.GlobalCFT.LocalField.Topology
import Submission.NK.GlobalCFT.Ideles.globalCFT_unityIdeles_isCompact
import Submission.NK.GlobalCFT.Ideles.globalCFT_totallyDisconnectedSpace_unityIdeles
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalIdele_injective
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalIdele_isDiscrete
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed
import Submission.NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_mul
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_one
import Submission.NK.GlobalCFT.Norm.globalCFT_localNorm_mem_localUnits
import Submission.NK.GlobalCFT.Norm.globalCFT_eventually_normIdeleFun_mem
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFT.GaloisAction
import Submission.NK.GlobalCFT.GaloisIdeles
import Submission.NK.GlobalCFT.Galois.globalCFT_exists_localRingEquiv_smul
import Submission.NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_place_smul
import Submission.NK.GlobalCFT.Galois.globalCFT_one_smul_place
import Submission.NK.GlobalCFT.H0Computation
import Submission.NK.GlobalCFT.ClassFormation
import Submission.NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_smul
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits
import Submission.NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.Cohomology.globalCFT_H0Computation_of_invariants
import Submission.NK.GlobalCFT.Cohomology.globalCFT_H0Computation_of_invariants_and_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Global class field theory for number fields

Aggregator module: `import Submission.NK.GlobalCFT.GlobalCFT` brings in the whole chapter.

## The idèles

* `NK.GlobalCFT.Place K`: the places of `K`; `NK.GlobalCFT.Place.localField K v = K_v`;
  `NK.GlobalCFT.Place.localUnits K v = 𝒪_vˣ` (all of `K_vˣ` at an archimedean place).
* `NK.GlobalCFT.Idele K` (notation `𝕀[K]`): the idèle group as the restricted product of the
  local unit groups, with its restricted-product topology; it is a topological group
  (`IsTopologicalGroup`) and locally compact (`LocallyCompactSpace`).
* `NK.GlobalCFT.Idele.principalIdele K : Kˣ →* 𝕀 K`: the diagonal embedding; its range is
  `NK.GlobalCFT.Idele.principalSubgroup K`, which is closed and discrete
  (`globalCFT_principalSubgroup_isClosed`, `globalCFT_principalIdele_isDiscrete`) and injective
  (`globalCFT_principalIdele_injective`).
* `NK.GlobalCFT.Idele.unityIdeles K = ∏_{v finite} 𝒪_vˣ`, compact
  (`globalCFT_unityIdeles_isCompact`).
* `NK.GlobalCFT.Idele.abs K : 𝕀 K →* ℝˣ`: the content; `NK.GlobalCFT.Idele.normOne K = 𝕀¹ K`
  its kernel; the product formula `globalCFT_abs_principalIdele`.

## The idèle class group

* `NK.GlobalCFT.IdeleClassGroup K` (notation `C[K]`): `C_K = 𝕀 K ⧸ Kˣ`, with
  `NK.GlobalCFT.IdeleClassGroup.mk K` the quotient map and `abs K : C_K →* ℝˣ` the content.
* `NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U = 𝕀 K ⧸ (Kˣ · U)`: ray class groups as
  quotients of `C_K` (`rayClassGroupMk`, `rayClassGroupMk_surjective`, `ker_rayClassGroupMk`).
* `NK.GlobalCFT.IdeleClassGroup.normOneClassGroup K = C¹_K = 𝕀¹ K ⧸ Kˣ`; it is compact
  (`globalCFT_compactSpace_normOneClassGroup`: finiteness of the class group and Dirichlet's unit
  theorem).
* The local–global exact sequence `1 → 𝒪_Kˣ → ∏_v 𝒪_vˣ → C_K → Cl(K) → 1`:
  `NK.GlobalCFT.IdeleClassGroup.idealClassMap` (the divisor-class map),
  `idealClassMap_eq_one_iff` and `local_global_exact_sequence`.

## Norms and functoriality

* `NK.GlobalCFT.Place.localNormInfinite/Finite`: the local norms.
* `NK.GlobalCFT.Idele.normIdeleFun K L`: the componentwise idèlic norm.
* `NK.GlobalCFT.Idele.normIdeleHom K L : 𝕀 L →* 𝕀 K`: the idèlic norm.
* `NK.GlobalCFT.IdeleClassGroup.normClassHom K L : C_L →* C_K`: the norm on idèle class
  groups, well defined because the norm of a principal idèle is principal
  (`NK.GlobalCFT.Idele.normIdeleHom_principalIdele`).
* `NK.GlobalCFT.Idele.normImage K L`, `NK.GlobalCFT.Idele.normClassSubgroup K L`: the norm
  subgroups `N_{L/K} 𝕀 L ≤ 𝕀 K` and `N_{L/K} C_L ≤ C_K`.
* Transitivity over a tower: `NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans`.

## The action of the Galois group

* `NK.GlobalCFT.Place.mulActionGalois`: `Gal(L/K) = (L ≃ₐ[K] L)` acts on the places of `L`
  (an archimedean place is composed with the automorphism, a nonarchimedean place is the image
  prime), and `Place.liesOver_smul_iff`: it preserves the places above a given place of `K`
  (`NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver`, `...globalCFT_smul_place_smul`,
  `...globalCFT_one_smul_place`), and `NK.GlobalCFT.Place.localRingEquiv` is the canonical
  local field isomorphism `L_v ≃+* L_{σ v}`
  (`NK.GlobalCFT.Galois.globalCFT_exists_localRingEquiv_smul`, with
  `Place.localRingEquiv_algebraMap`, `Place.localRingEquiv_mem_localUnits`).  The induced action
  on `𝕀 L` and `C L` is `NK.GlobalCFT.Idele.smul_apply` (`SMul`/`MulDistribMulAction` instances
  on `𝕀 L` and `C L`), and `NK.GlobalCFT.galoisClassGroup`.  `NK.GlobalCFT.Inclusion`
  provides the canonical local embeddings `Place.localAlgebraMapUnits : K_vˣ →* L_wˣ` used for the
  inclusion `𝕀 K → 𝕀 L` of idèles.

## Reciprocity, the existence theorem and Čebotarev

* `NK.GlobalCFT.ArtinReciprocity K L`: the reciprocity isomorphism `C_K ⧸ N_{L/K} C_L ≃* Gal(L/K)`
  for abelian `L/K` (hypothesis), and its general-Galois form
  `NK.GlobalCFT.GaloisReciprocity K L` (`≃* Gal(L/K)ᵃᵇ`, with
  `GaloisReciprocity.artinMap`, `..._ker`, `..._surjective`, `..._index_eq_card_abelianization`
  and `..._toArtinReciprocity`);
  `NK.GlobalCFT.ArtinReciprocity.artinMap`, `..._ker`, `..._surjective`.
* `NK.GlobalCFT.ExistenceTheorem K`: the existence theorem (hypothesis).
* `NK.GlobalCFT.ChebotarevDensity K L`: Čebotarev's density theorem (hypothesis), with the
  qualitative consequences `exists_prime_frobeniusClass`, `infinite_setOf_frobeniusClass`.

## Class formations and the inequalities

* `NK.GlobalCFT.ExtensionAxiom`, `NK.GlobalCFT.FieldAxiom`, `NK.GlobalCFT.TwoInequalities`;
  the extension property is *proved* (`NK.GlobalCFT.extensionAxiom_holds`).
* From the reciprocity isomorphism: `NK.GlobalCFT.index_normClassSubgroup_eq_finrank`,
  `NK.GlobalCFT.first_inequality_of_artinReciprocity`,
  `NK.GlobalCFT.second_inequality_of_artinReciprocity`.

## The cohomological layer (`NK.GlobalCFT.Cohomology`)

* `NK.GlobalCFT.IdeleClassGroup.rep`: `C_L` as a `ℤ[Gal(L/K)]`-module.
* `NK.GlobalCFT.CohomologicalFieldAxiom`: `H¹ = 0` on all subgroups, `|H²(H)| = |H|`, and a
  *fundamental class* `u ∈ H²(Gal(L/K), C_L)` of order `[L : K]`.
* `NK.GlobalCFT.natCard_tateCohomology_zero_eq_abelianization` (Tate's theorem):
  `|Ĥ⁰(Gal(L/K), C_L)| = |Gal(L/K)ᵃᵇ|`, and the abelian case
  `NK.GlobalCFT.natCard_tateCohomology_zero_eq_finrank`: `= [L : K]`.
* `NK.GlobalCFT.H0Computation`: the `H⁰`-computation `C_K ⧸ N_{L/K} C_L ≅ Ĥ⁰(Gal(L/K), C_L)`.
* `NK.GlobalCFT.HerbrandQuotient`: the Herbrand quotient computation `h(G, C_L) = [L : K]`
  (Milne, *CFT*, Theorem 4.3), the classical non-circular input.
* `NK.GlobalCFT.first_inequality_of_herbrandQuotient`,
  `NK.GlobalCFT.second_inequality_of_herbrandQuotient_of_subsingleton`,
  `NK.GlobalCFT.index_eq_card_abelianization`,
  `NK.GlobalCFT.fieldAxiom_of_cohomologicalFieldAxiom`.

⚠ For a general finite Galois `L/K` the norm index is `|Gal(L/K)ᵃᵇ|`, not `[L : K]`: the two
inequalities (and the index form of the field axiom) are statements about **abelian** extensions.
-/
