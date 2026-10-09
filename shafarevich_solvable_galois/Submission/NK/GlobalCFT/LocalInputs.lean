/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.GaloisIdeles
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Galois.globalCFT_exists_localRingEquiv_smul
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pointer module: the local inputs for the idèle fixed-point computation

This module is a pure aggregator (no declarations of its own).  It collects the imports which are
useful for the lemmas `NK.GlobalCFT.Galois.globalCFT_localFixed_finite`,
`...globalCFT_localFixed_infinite`, `NK.GlobalCFT.Inclusion.globalCFT_exists_placeOver`,
`...globalCFT_exists_smul_eq_of_liesOver` and
`...globalCFT_mem_localUnits_of_localAlgebraMapUnits`, together with a map of the relevant API.

## Finite (`p`-adic) places: `q | Q`

* `Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (q)` — the decomposition group
  `D_q = {σ : Gal(L/K) | placeSmul σ q = q}`; note `placeSmul σ q` is the *same* action on
  `HeightOneSpectrum` as `NK.GlobalCFT.Place.smulHeightOneSpectrum σ q` (both are
  `HeightOneSpectrum.mapRingEquiv` of the automorphism of `𝓞 L` induced by `σ`; the two ring
  equivalences are `RingOfIntegers.mapRingEquiv σ` and `galRestrict (𝓞 K) K L (𝓞 L) σ`, which
  agree after coercing to `L`, see `RingOfIntegers.mapRingEquiv_apply`,
  `IsIntegralClosure.galRestrict_apply` and injectivity of `𝓞 L → L`).
* `...decompositionToAdicCompletion q : D_q →* (q.adicCompletion L ≃+* q.adicCompletion L)` —
  the action of `D_q` on the completion, with `...decompositionToAdicCompletion_coe` giving its
  value on the image of `L`.
* `...decompositionSubgroupMulEquivLocalGalois Q q h : D_q ≃* Gal(L_q/K_Q)` — **the decomposition
  group *is* the local Galois group** (this is the hard degree-theoretic input, already proved in
  the commons); `...decompositionSubgroupMulEquivLocalGalois_coe` says that on underlying maps it
  is `...decompositionToLocalGalois`.
* `...isGalois_adicCompletion Q q h : IsGalois (Q.adicCompletion K) (q.adicCompletion L)`.
* Hence, for `y : L_q` fixed by all of `D_q`, `IsGalois.fixedField_top` (Mathlib) says that `y`
  lies in `⊥ : IntermediateField K_Q L_q`, i.e. in the range of the algebra map, which is
  `Commons.RingTheory.Henselian.adicCompletionMap Q q h`.

## Infinite (archimedean) places: `w | v`

* `NumberField.InfinitePlace.exists_smul_eq_of_comap_eq` — transitivity of `Gal(L/K)` on the
  infinite places above a given one.
* `NumberField.InfinitePlace.LiesOver.comap_eq` — `w.LiesOver v` is `w.comap (algebraMap K L) = v`.
* `NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`,
  `...ringEquivComplexOfIsComplex` — the canonical isomorphisms `v.Completion ≃+* ℝ`, `≃+* ℂ`,
  with `..._apply` computing them as `extensionEmbeddingOfIsReal` / `extensionEmbedding`.
* `Complex.uniformContinuous_ringHom_eq_id_or_conj` — a continuous unital ring hom `ℂ → ℂ` is the
  identity or complex conjugation, hence bijective; this handles the cases where the local algebra
  map `K_v → L_w` is surjective.
* `NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq` and
  `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq` — used to produce `σ : Gal(L/K)` which fixes a
  complex place `w` over a *real* `v` and acts as complex conjugation on `L_w` (so that the fixed
  units are the units of the image of `K_v = ℝ`).

## Local units

* `NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mapsTo_localUnits` — the forward
  inclusion `𝒪_vˣ → 𝒪_wˣ`.
* `Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff` — the converse
  (integrality reflects along `Q ↪ q`), which gives
  `localAlgebraMapUnits w v h a ∈ localUnits L w → a ∈ localUnits K v` at finite places.
-/
