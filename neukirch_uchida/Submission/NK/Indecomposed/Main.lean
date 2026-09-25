/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.Indecomposed.Main`: Neukirch's criterion assembled

This file assembles Neukirch's local characterisation of decomposition groups — Theorem 1 of
J. Neukirch, *Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*, Invent.
Math. **6** (1969); Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (12.1.9) "if" — in its
coefficient-correct (`μ_p`-twisted) form,

`NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ'`,

from

* the **rank data** `NK.Indecomposed.RankData p K K' κ κ'` (the twisted cardinality computations of
  local class field theory together with Neukirch's surjectivity `eq:NeukirchH2modifiedsurj`, i.e.
  NSW (9.2.1), in the guarded form delivered by `Submission/Work/HasseTwist/`), and
* Neukirch's **local reconstruction** `NK.Indecomposed.LocalReconstruction p K K' κ κ'`
  (Korollar 1 and the finishing step).

## The argument

The proof has exactly the four steps of Neukirch's Theorem 1 (and of the sibling chapter
`Submission/Work/LocalDecomposition/`, whose group-theoretic lemmas it reuses):

1. **the rank count** (`NK.Indecomposed.subsingleton_of_ne_bot_of_surjective`): from Neukirch's
   surjectivity, `Nat.card (H²(H, μ_p)) = p` and `p ≤ Nat.card (H²(H ⊓ D_A, μ_p))` for every
   *non-trivial* local group, at most one non-trivial local group of `H` over the prime `𝔭` can
   occur.  (The cardinality hypothesis cannot be imposed at `V = ⊥` — there `H²(⊥, μ_p)` is a point,
   `NK.Indecomposed.subsingleton_h2Twist_bot` — and `⊥` occurs precisely when the prime is
   decomposed.)
2. **the local group at the place carrying the class is non-trivial**
   (`NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero`): a non-zero local component at `A`
   forces `H ⊓ D_A ≠ ⊥`.
3. **Neukirch's "the prime is indecomposed" step**
   (`NK.Indecomposed.le_stabSubgroup_of_unique_localGroup`, the FKS normalizer property): the
   uniqueness of the non-trivial local group says that `H` normalises `H ⊓ D_A`, and since
   `H ⊓ D_A ≤ D_A` is non-trivial the normalizer property of the FKS theorem
   (CoNF XII (12.1.3)–(12.1.4)) gives `H ≤ D_A`.
4. **Korollar 1 and the finishing step**: `H ≤ D_A` with `H ≅ Gal(κ'/κ)` gives
   `0 < H.relIndex D_A` by Neukirch's Korollar 1
   (`NK.Indecomposed.relIndex_pos_of_localKorollar1`), and the finishing step
   (`NK.LocalStructure.LocalFinishingStep`) produces a place `A'` with `D_{A'} = H`.

The Hasse principle `NK.BrauerTwist.Sha2Vanishing` is *not* used in the criterion itself (its
hypothesis is the local non-vanishing of the class, not the existence of a place where it does not
vanish); it is consumed by the corollaries that *produce* the non-vanishing
(`NK.Indecomposed.exists_decompositionGroup_of_twistedHasse`), which is how the criterion is used
in the `(a)`-chain of the Neukirch–Uchida development.
-/

import Submission.NK.Indecomposed.Defs
import Submission.NK.HassePrinciple.LocalCharacterisation
import Submission.NK.Indecomposed.subsingleton_of_ne_bot_of_surjective
import Submission.NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero
import Submission.NK.Indecomposed.le_stabSubgroup_of_unique_localGroup
import Submission.NK.Indecomposed.relIndex_pos_of_localKorollar1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace NK.Indecomposed

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## Neukirch's "the prime is indecomposed" step, from the rank data -/

/-- **The rank count and the FKS normalizer property.**

A closed labelled subgroup `H ≤ Gal(K'/K)` that has a class of `H²(H, μ_p)` with a non-zero local
component at a place `A` over a finite prime of `K` is *contained* in the decomposition group of a
place over a finite prime of `K`.

This is the group-theoretic content of the sibling chapter's input
`NK.LocalDecomposition.IndecomposedPrime` (in the `μ_p`-twisted vocabulary), and the assembly below
therefore does *not* assume it: it is proved here, from the rank data alone, in the sharp form in
which no openness of the local group is needed.  The three steps are

1. the rank count (`NK.Indecomposed.subsingleton_of_ne_bot_of_surjective`): at most one non-trivial
   local group of `H` over the prime `𝔭` below `A`;
2. the local group `H ⊓ D_A` is non-trivial, because the local component at `A` does not vanish
   (`NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero`);
3. hence `H` normalizes `H ⊓ D_A` (its conjugates are again non-trivial local groups, so they
   coincide with it), and since `H ⊓ D_A` is a non-trivial subgroup of `D_A` the FKS normalizer
   property (`NK.LocalDecomposition.normalizer_le_of_ne_bot`, CoNF XII (12.1.3)–(12.1.4),
   `NK.Indecomposed.le_stabSubgroup_of_unique_localGroup`) gives `N(H ⊓ D_A) ≤ D_A`, so
   `H ≤ D_A`. -/
theorem le_stabSubgroup_of_rankData (hrank : RankData p K K' κ κ')
    (H : Subgroup Gal(K'/K)) (hHcl : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (A : NK.BrauerTwist.OverFinitePrime K K') (x : H2Twist p H)
    (hx : H2Twist.loc p H x A ≠ 0) :
    ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
      H ≤ NK.BrauerTwist.stabSubgroup A' := by
  -- the finite prime below `A`, and `A` as a place over it
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) := primeUnder A
  have h𝔭 : A.1.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := primeUnder_spec A
  let A₀ : PlacesOverPrime K K' 𝔭 := ⟨A.1, h𝔭⟩
  have hA₀ : A₀.toOverFinitePrime = A := Subtype.ext rfl
  -- the guard of the guarded surjectivity: the class has a non-zero component at `A₀`
  have hguard : ∃ (A' : PlacesOverPrime K K' 𝔭) (y : H2Twist p H),
      H2Twist.loc p H y A'.toOverFinitePrime ≠ 0 :=
    ⟨A₀, x, by rw [hA₀]; exact hx⟩
  -- the rank data at this subgroup and prime
  have hsurj : Function.Surjective (localisationTo (K := K) (K' := K') p H 𝔭) :=
    hrank.surj H hHcl hκ 𝔭 hguard
  have hcard : Nat.card (H2Twist p H) = p := hrank.card_global H hHcl hκ
  have hloc : ∀ V, V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      V ≠ ⊥ → p ≤ Nat.card (H2Twist p V) :=
    fun V hV hne => hrank.card_local H hHcl hκ 𝔭 V hV hne
  -- the rank count: at most one non-trivial local group of `H` over `𝔭`
  have huniq := subsingleton_of_ne_bot_of_surjective (K := K) (K' := K')
    p hrank.hp H 𝔭 hcard hloc hsurj
  -- the local group at `A₀` is non-trivial, because the local component at `A` is non-zero
  have hVne : H ⊓ stabSubgroup A₀.1 ≠ ⊥ :=
    inf_stabSubgroup_ne_bot_of_loc_ne_zero (K := K) (K' := K') p H A (x := x) hx
  -- FKS turns the unique non-trivial local group into the containment `H ≤ D_{A₀}`
  have hHle : H ≤ stabSubgroup A₀.1 := by
    refine le_stabSubgroup_of_unique_localGroup (K := K) (K' := K') 𝔭 A₀ H hVne ?_
    intro A' A'' h1 h2
    exact huniq (H ⊓ stabSubgroup A'.1) (H ⊓ stabSubgroup A''.1) ⟨A', rfl⟩ ⟨A'', rfl⟩ h1 h2
  exact ⟨A.1, A.2, hHle⟩

/-! ## The criterion from the rank data and the local reconstruction -/

/-- **Neukirch's criterion from the rank data and the local reconstruction.**

Let `K` be a number field with separable closure `K'`, `κ` a `p`-adic field with separable closure
`κ'`.  Suppose

* `RankData p K K' κ κ'` — the local Brauer cardinalities `|H²(U, μ_p)| = p` (`U ≅ Gal(κ'/κ)`
  closed), `p ≤ |H²(H ⊓ D_A, μ_p)|` for the non-trivial local groups, and Neukirch's surjectivity
  (NSW (9.2.1)) in the guarded form of `Submission/Work/HasseTwist/`;
* `LocalReconstruction p K K' κ κ'` — Neukirch's Korollar 1 and the finishing step.

Then a closed self-normalising subgroup `H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` whose `H²(H, μ_p)`
class has a non-zero local component at a place over a finite prime of `K` *is* the decomposition
group of a place over a finite prime of `K`.  This is Theorem 1 of Neukirch, Invent. Math. **6**
(1969), i.e. the "if" direction of CoNF (12.1.9), with `μ_p`-coefficients.

The proof is `NK.Indecomposed.le_stabSubgroup_of_rankData` (the "prime is indecomposed" step,
proved from the rank data), Neukirch's Korollar 1 for the finiteness of the relative index
(`NK.Indecomposed.relIndex_pos_of_localKorollar1`) and the finishing step. -/
theorem localDecompositionCriterion_of_rankData
    (hrank : RankData p K K' κ κ') (hrec : LocalReconstruction p K K' κ κ') :
    NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ' := by
  intro H hHcl hN hκ A x hx
  obtain ⟨A', hA'ne, hHle⟩ := le_stabSubgroup_of_rankData (K := K) (K' := K') hrank H hHcl hκ A x hx
  -- Neukirch's Korollar 1: the relative index of `H` in `D_{A'}` is finite
  have hfin : 0 < H.relIndex (stabSubgroup A') :=
    relIndex_pos_of_localKorollar1 (K := K) (K' := K') hrec.korollar1 A' hA'ne H hHle hκ
  -- the finishing step: `H` is *equal* to the decomposition group of a place
  exact hrec.finishingStep H hHcl hN hκ A' hA'ne hHle hfin

/-! ## The local Brauer non-vanishing from the rank data -/

/-- **The local Brauer non-vanishing input from the rank data.**  The cardinality input
`Nat.card (H2Twist p H) = p` (with `p` prime) already contains the existence of a non-zero class
`NK.BrauerTwist.LocalH2Input` (which is its non-vanishing half), so no separate input is needed
for the `(a)`-chain. -/
theorem localH2Input_of_rankData (hrank : RankData p K K' κ κ') :
    NK.BrauerTwist.LocalH2Input p K K' κ κ' := by
  intro H hHcl hκ
  by_contra h
  push_neg at h
  have hsub : Subsingleton (H2Twist p H) := ⟨fun a b => by rw [h a, h b]⟩
  have h1 : Nat.card (H2Twist p H) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
  have hcard := hrank.card_global H hHcl hκ
  rw [hcard] at h1
  have := hrank.hp.two_le
  omega

/-! ## The requested form: the criterion from the Hasse chapter's rank-count input -/

/-- **Neukirch's criterion, assembled from the `μ_p`-twisted Hasse chapter.**

This is the form requested by the consumer: from

* `hH : Sha2Input p K K' κ κ'` — the Hasse principle with cyclotomic coefficients
  (`NK.HasseTwist.sha2Vanishing`), the chapter of `Submission/Work/HasseTwist/`
  (`Sha2Input` carries `hp : p.Prime`);
* `hSurj : NeukirchH2modifiedsurjAt p K K' κ κ'` — Neukirch's surjectivity (NSW (9.2.1)) in the
  guarded form delivered by that chapter;
* `hcard` — the twisted local Brauer cardinality `Nat.card (H2Twist p U) = p` for every closed
  `U ≅ Gal(κ'/κ)` (classically `H²(G_κ, μ_p) = Br(κ)[p] ≅ Z/p`; the named forms
  `NK.BrauerTwist.LocalH2Input` and `NK.BrauerTwist.LocalFieldBrauerCyclic` are the
  non-vanishing and the cyclic form of this computation);
* `hloc` — the same computation at the local groups `V = H ⊓ D_A`, **restricted to the non-trivial
  local groups** (`V ≠ ⊥`; at `V = ⊥` the group `H2Twist p ⊥` is a point, so the hypothesis
  correctly fails there — see `NK.Indecomposed.subsingleton_h2Twist_bot` and `README.md` §4);
* `hkor : LocalReconstruction p K K' κ κ'` — Neukirch's local reconstruction (Korollar 1 and the
  finishing step),

we conclude `NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ'`.

The hypothesis `hH` is not used by the criterion itself: the criterion's hypothesis is that some
class has a non-zero local component, whereas the Hasse principle produces such a place.  It is
consumed by the corollaries that produce the class and its place, in particular
`NK.Indecomposed.exists_decompositionGroup_of_twistedHasse`, which is what the `(a)`-chain uses;
it is kept in the signature because the caller has it available and it is the shape requested. -/
theorem localDecompositionCriterion_of_twistedHasse
    (hH : Sha2Input p K K' κ κ')
    (hSurj : NeukirchH2modifiedsurjAt p K K' κ κ')
    (hcard : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → Nat.card (H2Twist p U) = p)
    (hloc : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
      Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
          V ≠ ⊥ → p ≤ Nat.card (H2Twist p V))
    (hkor : LocalReconstruction p K K' κ κ') :
    NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ' :=
  localDecompositionCriterion_of_rankData (K := K) (K' := K') (κ := κ) (κ' := κ')
    { hp := hH.hp, card_global := hcard, card_local := hloc, surj := hSurj } hkor

/-- **The same criterion with the literal form of the local cardinality hypothesis**, i.e. with
`p ≤ Nat.card (H2Twist p V)` imposed on *all* local groups over `𝔭`, including `⊥`.

The hypothesis is stronger than the one of
`NK.Indecomposed.localDecompositionCriterion_of_twistedHasse` (which requires it only for
`V ≠ ⊥`), so the theorem follows from it.  It is recorded because it is the literal shape of the
request; see `README.md` §4 for why the unrestricted form is unsatisfiable in the intended
situation (at `V = ⊥` the group `H2Twist p ⊥` is a point, and `⊥` occurs as a local group exactly
when the prime is decomposed in `K'/K`). -/
theorem localDecompositionCriterion_of_twistedHasse_allLocals
    (hp : p.Prime)
    (hSurj : NeukirchH2modifiedsurjAt p K K' κ κ')
    (hcard : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → Nat.card (H2Twist p U) = p)
    (hloc : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
      Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
          p ≤ Nat.card (H2Twist p V))
    (hkor : LocalReconstruction p K K' κ κ') :
    NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ' :=
  localDecompositionCriterion_of_rankData (K := K) (K' := K') (κ := κ) (κ' := κ')
    { hp := hp, card_global := hcard
      card_local := fun H hHcl hκ 𝔭 V hV _ => hloc H hHcl hκ 𝔭 V hV
      surj := hSurj } hkor

/-! ## The criterion in the existential form used by the `(a)`-chain -/

/-- **Neukirch's Theorem 1 with the Hasse principle consumed.**  Every closed self-normalising
subgroup `H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` — where `κ` is a `p`-adic field — *is* the
decomposition group of a place of `K'` over a finite prime of `K`.

Here the non-vanishing of the local component is *produced* (rather than assumed, as in the
criterion): the local Brauer input `NK.BrauerTwist.LocalH2Input` supplies a non-zero class, and
the Hasse principle `NK.HasseTwist.Sha2Input` (through
`NK.HasseTwist.sha2Vanishing`) produces a place at which its localisation does not vanish. -/
theorem exists_decompositionGroup_of_twistedHasse
    (hH : Sha2Input p K K' κ κ')
    (hLoc : NK.BrauerTwist.LocalH2Input p K K' κ κ')
    (hSurj : NeukirchH2modifiedsurjAt p K K' κ κ')
    (hcard : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → Nat.card (H2Twist p U) = p)
    (hloc : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
      Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
          V ≠ ⊥ → p ≤ Nat.card (H2Twist p V))
    (hkor : LocalReconstruction p K K' κ κ') :
    NK.HassePrinciple.LocalCharacterisationSN p K K' κ κ' := by
  have hStep := localDecompositionCriterion_of_twistedHasse (K := K) (K' := K') (κ := κ) (κ' := κ')
    hH hSurj hcard hloc hkor
  intro H hHcl hN hκ
  obtain ⟨x, hx⟩ := hLoc H hHcl hκ
  obtain ⟨A, hA⟩ := NK.BrauerTwist.exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ')
    p (NK.HasseTwist.sha2Vanishing (K := K) (K' := K') (κ := κ) (κ' := κ') p hH) H hHcl hκ hx
  obtain ⟨A', hA'ne, hA'⟩ := hStep H hHcl hN hκ A x hA
  exact ⟨⟨A', hA'ne⟩, le_of_eq hA'.symm⟩

/-! ## The pointwise form, for the per-finite-prime assembly -/

/-- **The criterion at a single subgroup and place.**  This is the working form of the assembly: the
rank data and the local reconstruction at one labelled subgroup and one prime yield, for every class
with non-zero local component at a place over that prime, a place whose decomposition group is the
subgroup. -/
theorem exists_stabSubgroup_eq_of_rankData
    (hrank : RankData p K K' κ κ') (hrec : LocalReconstruction p K K' κ κ')
    (H : Subgroup Gal(K'/K)) (hHcl : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (A : NK.BrauerTwist.OverFinitePrime K K') (x : H2Twist p H)
    (hx : H2Twist.loc p H x A ≠ 0) :
    ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
      NK.BrauerTwist.stabSubgroup A' = H :=
  localDecompositionCriterion_of_rankData (K := K) (K' := K') (κ := κ) (κ' := κ')
    hrank hrec H hHcl hN hκ A x hx

end NK.Indecomposed
