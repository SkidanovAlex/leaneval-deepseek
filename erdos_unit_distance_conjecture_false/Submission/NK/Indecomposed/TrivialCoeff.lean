/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The same criterion in the trivial-coefficient vocabulary, at `p = 2`

The chapter `Submission/Work/LocalDecomposition/` states Neukirch's "if" direction in the
**trivial**-coefficient vocabulary (`NK.BrauerHasse.H2Profinite p U = H²(U, Z/p)`) and reduces it
to the input `NK.LocalDecomposition.IndecomposedPrime p K K' κ κ'`.  For `p = 2` the two
coefficient modules agree — `μ_2 = {±1} = Z/2` carries the trivial action — so the twisted assembly
of `NK.Indecomposed.Main` applies, and this file delivers the reduction in that vocabulary:

```lean
NK.Indecomposed.indecomposedPrime_of_rankDataTrivial
    (hrank : NK.Indecomposed.RankDataTrivial p K K' κ κ')
    (hrec  : NK.Indecomposed.LocalReconstruction p K K' κ κ') :
    NK.LocalDecomposition.IndecomposedPrime p K K' κ κ'
```

together with its specialisation to `p = 2`.  The proof is the *same* four steps as in the twisted
case; only the rank count and the triviality of the cohomology of the trivial group change
vocabulary:

* the rank count in the trivial-coefficient vocabulary:
  `NK.Indecomposed.subsingleton_of_ne_bot_of_surjective_trivial`;
* `H²(⊥, Z/p)` is a point: `NK.Indecomposed.subsingleton_h2Profinite_of_subsingleton` together
  with `NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero_trivial`;
* the group-theoretic core is *coefficient-free* and is shared:
  `NK.Indecomposed.le_stabSubgroup_of_unique_localGroup`.

Since `IndecomposedPrime`'s conclusion is a purely group-theoretic statement about the subgroup `H`
(cf. `README.md` §5), no comparison of the two cohomology theories is needed: the input is the
trivial-coefficient rank data `NK.Indecomposed.RankDataTrivial`, and the output is the sibling
chapter's input, now *proved* from it.  (The conclusion is a statement about `H`, so the local
reconstruction is used only through its coefficient-free part, exactly as before.)
-/

import Submission.NK.Indecomposed.Defs
import Submission.NK.Indecomposed.subsingleton_of_ne_bot_of_surjective_trivial
import Submission.NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero_trivial
import Submission.NK.Indecomposed.le_stabSubgroup_of_unique_localGroup

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace NK.Indecomposed

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Neukirch's "the prime is indecomposed", in the trivial-coefficient vocabulary**: from the rank
data `NK.Indecomposed.RankDataTrivial` (the cardinality computations `|H²(U, Z/p)| = p`,
`p ≤ |H²(V, Z/p)|` at the non-trivial local groups, and Neukirch's surjectivity) and the local
reconstruction, every closed subgroup `H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` which has a class of
`H²(H, Z/p)` with a non-zero local component at a place over a finite prime contains an open
subgroup lying in the decomposition group of a place over a finite prime.

Note that the subgroup produced is `H` itself: the assembly proves the *sharp* containment
`H ≤ D_{A'}` (see `NK.Indecomposed.le_stabSubgroup_of_unique_localGroup`), and the openness
hypothesis `0 < H.relIndex H = 1` is then trivially satisfied.  This is the input
`NK.LocalDecomposition.IndecomposedPrime` of the sibling chapter, *proved* here. -/
theorem indecomposedPrime_of_rankDataTrivial
    (hrank : RankDataTrivial p K K' κ κ') (hrec : LocalReconstruction p K K' κ κ') :
    NK.LocalDecomposition.IndecomposedPrime p K K' κ κ' := by
  intro H hHcl hκ A x hx
  -- the finite prime below `A`, and `A` as a place over it
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) := primeUnder A
  have h𝔭 : A.val.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := primeUnder_spec A
  let A₀ : PlacesOverPrime K K' 𝔭 := ⟨A.val, h𝔭⟩
  have hA₀ : A₀.toOverFinitePrime = A := Subtype.ext rfl
  have hguard : ∃ (A' : PlacesOverPrime K K' 𝔭) (y : NK.BrauerHasse.H2Profinite p H),
      NK.BrauerHasse.H2Profinite.loc p H y A'.toOverFinitePrime ≠ 0 :=
    ⟨A₀, x, hx⟩
  have hsurj : Function.Surjective (localisationToTrivial (K := K) (K' := K') p H 𝔭) :=
    hrank.surj H hHcl hκ 𝔭 hguard
  have hcard : Nat.card (NK.BrauerHasse.H2Profinite p H) = p := hrank.card_global H hHcl hκ
  have hloc : ∀ V, V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      V ≠ ⊥ → p ≤ Nat.card (NK.BrauerHasse.H2Profinite p V) :=
    fun V hV hne => hrank.card_local H hHcl hκ 𝔭 V hV hne
  have huniq := subsingleton_of_ne_bot_of_surjective_trivial (K := K) (K' := K')
    p hrank.hp H 𝔭 hcard hloc hsurj
  have hVne : H ⊓ stabSubgroup A₀.1 ≠ ⊥ :=
    inf_stabSubgroup_ne_bot_of_loc_ne_zero_trivial (K := K) (K' := K') p H A (x := x) hx
  have hHle : H ≤ stabSubgroup A₀.1 := by
    refine le_stabSubgroup_of_unique_localGroup (K := K) (K' := K') 𝔭 A₀ H hVne ?_
    intro A' A'' h1 h2
    exact huniq (H ⊓ stabSubgroup A'.1) (H ⊓ stabSubgroup A''.1) ⟨A', rfl⟩ ⟨A'', rfl⟩ h1 h2
  refine ⟨H, A₀.1, le_rfl, ?_, ?_, hHle⟩
  · rw [Subgroup.relIndex_self]
    exact Nat.one_pos
  · rw [h𝔭]
    exact isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭

/-- **The same, at `p = 2`**, which is the prime at which the twisted and the trivial coefficient
modules agree (`μ_2 = Z/2` for every field of characteristic `≠ 2`).  This is the form requested by
the consumer: `NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ'`, *proved* from the rank data
and the local reconstruction. -/
theorem indecomposedPrime_two_of_rankData
    (hrank : RankDataTrivial 2 K K' κ κ') (hrec : LocalReconstruction 2 K K' κ κ') :
    NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ' :=
  indecomposedPrime_of_rankDataTrivial (K := K) (K' := K') (κ := κ) (κ' := κ') hrank hrec

/-- **The `(a)`-chain at `p = 2` with Neukirch's "the prime is indecomposed" step *proved*.**

This is `NK.LocalDecomposition.preservesDecompositionGroups_of_localData_two` with two of its
per-prime inputs discharged:

* the input `NK.LocalDecomposition.IndecomposedPrime 2` is *proved* from the trivial-coefficient
  rank data (`NK.Indecomposed.indecomposedPrime_two_of_rankData`);
* the input `NK.LocalDecomposition.IndexOneOfSelfNormalizing 2` is *derived* from the local
  reconstruction `NK.Indecomposed.LocalReconstruction 2` through
  `NK.LocalDecomposition.localFinishingStep_iff_indexOne`.

What remains as a per-prime hypothesis is the local Brauer input
`NK.BrauerHasse.LocalH2Input 2`, the Hasse principle `NK.BrauerHasse.Sha2Vanishing 2`, Neukirch's
Korollar 1 in the global form used by that chain (`NK.LocalDecomposition.InjectionFiniteIndex`),
the infinitude of the local Galois group and the trivial-coefficient rank data
`NK.Indecomposed.RankDataTrivial 2` — for the completions of both number fields. -/
theorem preservesDecompositionGroups_of_localData_two_of_rankData
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hLoc₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      NK.BrauerHasse.LocalH2Input 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hHasse₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      NK.BrauerHasse.Sha2Vanishing 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hRank₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      RankDataTrivial 2 K₂ K₂' (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hRec₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      LocalReconstruction 2 K₂ K₂' (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hFin₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      NK.LocalDecomposition.InjectionFiniteIndex 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hInf₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      NK.LocalDecomposition.LocalGaloisInfinite
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hLoc₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      NK.BrauerHasse.LocalH2Input 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hHasse₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      NK.BrauerHasse.Sha2Vanishing 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hRank₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      RankDataTrivial 2 K₁ K₁' (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hRec₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      LocalReconstruction 2 K₁ K₁' (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hFin₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      NK.LocalDecomposition.InjectionFiniteIndex 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hInf₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      NK.LocalDecomposition.LocalGaloisInfinite
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ :=
  NK.LocalDecomposition.preservesDecompositionGroups_of_localData_two (K₁ := K₁) (K₂ := K₂)
    (K₁' := K₁') (K₂' := K₂') ϕ he hLoc₁ hHasse₁
    (fun 𝔭 => indecomposedPrime_two_of_rankData (K := K₂) (K' := K₂') (hRank₁ 𝔭) (hRec₁ 𝔭))
    hFin₁ hInf₁
    (fun 𝔭 => (NK.LocalDecomposition.localFinishingStep_iff_indexOne (p := 2) (K := K₂)
      (K' := K₂')).mp (hRec₁ 𝔭).finishingStep)
    hLoc₂ hHasse₂
    (fun 𝔮 => indecomposedPrime_two_of_rankData (K := K₁) (K' := K₁') (hRank₂ 𝔮) (hRec₂ 𝔮))
    hFin₂ hInf₂
    (fun 𝔮 => (NK.LocalDecomposition.localFinishingStep_iff_indexOne (p := 2) (K := K₁)
      (K' := K₁')).mp (hRec₂ 𝔮).finishingStep)

end NK.Indecomposed
