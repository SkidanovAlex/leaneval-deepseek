/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.NormIndex.Defs
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_finite

/-!
# The local norm data attached to a choice of a place above each place of `K`

For a finite **Galois** extension `L / K` of number fields, a finite set `S` of places of `K`
containing all archimedean places, and a choice `g` of a place `g v` of `L` above each place `v`
of `K`, this file assembles the local data used by the elementary proof of the finiteness of the
norm index:

* at every place `v`, a homomorphism `Φ v : L_{g v}ˣ →* K_vˣ` which computes the idèlic norm of
  the idèle of `L` concentrated at `g v` (`exists_normAt_data`, first conjunct);
* `Φ v` has finite index image (`FiniteIndex`), i.e. `K_vˣ ⧸ N L_{g v}ˣ` is finite;
* outside `S` (where the extension is unramified by hypothesis) `Φ v` maps the local units of
  `L_{g v}` *onto* the local units of `K_v`.

The archimedean places are handled by `localNorm_finiteIndex_archimedean`, the nonarchimedean
places by `localNorm_finiteIndex_finite`, and the unit surjectivity at an unramified place is
`Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.NormIndex

open NK.GlobalCFT

/-- Every place of `K` has a place of `L` above it (for a finite extension `L / K`). -/
theorem exists_place_liesOver {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : Place K) : ∃ w : Place L, Place.LiesOver w v := by
  rcases v with v' | Q
  · obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v'
    exact ⟨Place.ofInfinite w,
      Place.liesOver_ofInfinite ((Norm.liesOver_iff_comap_eq w v').mpr hw)⟩
  · obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    exact ⟨Place.ofFinite q, Place.liesOver_ofFinite hq⟩

/-- **The local norm data.**  For `L / K` finite Galois, `S` a finite set of places of `K`
containing the archimedean places, `g` a choice of a place of `L` above each place of `K`, and
`S` containing the places below all ramified primes, every place `v` of `K` carries a norm
homomorphism `Φ v : L_{g v}ˣ →* K_vˣ` with the three properties listed in the module docstring. -/
theorem exists_normAt_data {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (Place K)) (g : Place K → Place L) (hg : ∀ v, Place.LiesOver (g v) v)
    (hSinf : ∀ v : InfinitePlace K, Place.ofInfinite v ∈ S)
    (hunr : ∀ (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K)),
      q.asIdeal.LiesOver Q.asIdeal → Place.ofFinite Q ∉ S →
        q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∀ v : Place K, ∃ Φ : (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ,
      (∀ u, Idele.normIdeleFun K L
        (SecondInequality.KummerCase.singleIdele (g v) u) v = Φ u) ∧
      (Φ.range).FiniteIndex ∧
      (v ∉ S → ∀ a ∈ Place.localUnits K v,
        ∃ u ∈ Place.localUnits L (g v), Φ u = a) := by
  intro v
  rcases hg v with ⟨w, v', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
  · obtain rfl := h2
    haveI : w.LiesOver v' := h3
    rw [h1]
    refine ⟨Place.localNormInfinite w v', fun u => ?_, ?_, ?_⟩
    · exact SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite v' w u
    · exact localNorm_finiteIndex_archimedean w v'
    · intro hvS _ _
      exact absurd (hSinf v') hvS
  · obtain rfl := h2
    rw [h1]
    refine ⟨Place.localNormFinite q Q h3, fun u => ?_, ?_, ?_⟩
    · exact SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q h3 u
    · exact localNorm_finiteIndex_finite q Q h3
    · intro hQS a ha
      obtain ⟨u, hu, hu'⟩ :=
        SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q q h3 (hunr q Q h3 hQS) a ha
      exact ⟨u, hu, hu'⟩

end NK.GlobalCFTdeep.NormIndex
