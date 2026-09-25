/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Submission/Work/Indecomposed/` — the assembly of Neukirch's local characterisation of
decomposition groups

**Namespace** `NK.Indecomposed`.
**Import everything with** `import Submission.NK.Indecomposed.All`.

This chapter *assembles* Neukirch's local characterisation of decomposition groups — Theorem 1 of
J. Neukirch, *Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*, Invent.
Math. **6** (1969); Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (12.1.9) "if" — in
its **coefficient-correct (`μ_p`-twisted) form**

```lean
NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ'
```

from the inputs that the sibling chapters already deliver:

* the **rank count** of `Submission/Work/HasseTwist/` — Neukirch's surjectivity
  `NK.HasseTwist.NeukirchH2modifiedsurjAt` together with the two twisted cardinality
  computations `Nat.card (H2Twist p U) = p` / `p ≤ Nat.card (H2Twist p V)`;
* **Neukirch's local reconstruction** — Korollar 1 (`NK.Indecomposed.LocalKorollar1`, the local
  form of `NK.LocalDecomposition.LocalInjectionFiniteIndexSubgroup`) and the finishing step
  (`NK.LocalStructure.LocalFinishingStep`, the maximality of decomposition groups, equivalent by
  `NK.LocalDecomposition.localFinishingStep_iff_indexOne` to the index-one statement
  `NK.LocalDecomposition.IndexOneOfSelfNormalizing`).

Everything between the inputs and the criterion is *proved* in this directory.  The two
group-theoretic ingredients are the FKS normalizer property
(`NK.LocalDecomposition.normalizer_le_of_ne_bot`, delivered) and the passage from a non-zero
local component to the containment `H ≤ D_A` (`NK.Indecomposed.le_stabSubgroup_of_rankData`),
which is Neukirch's "the prime is indecomposed" step in its sharp form.

## The shape of the cardinality hypotheses

The rank count of `Submission/Work/HasseTwist/` is the cardinality squeeze
`NK.HasseTwist.subsingleton_of_surjective_prod`: a surjection from a `p`-element set onto a
product of sets of cardinality `≥ p` forces the index set to be a singleton.  The hypothesis
`p ≤ Nat.card (H2Twist p V)` on the local groups can only be imposed on the **non-trivial** local
groups `V = H ⊓ D_A`: for `V = ⊥` the twisted cohomology `H2Twist p ⊥` is a point
(`NK.Indecomposed.subsingleton_h2Twist_bot`), so the hypothesis fails there and *must* fail —
the local group `⊥` occurs exactly when the prime is decomposed in `K'/K`.  The chapter therefore
uses the hypothesis in the form

`hloc : ∀ V ∈ localGroupsOver H 𝔭, V ≠ ⊥ → p ≤ Nat.card (H2Twist p V)`,

and *also* provides the literal form `∀ V ∈ localGroupsOver H 𝔭, p ≤ Nat.card (H2Twist p V)` of the
request (it is the stronger hypothesis, so the same theorem applies verbatim); see
`NK.Indecomposed.localDecompositionCriterion_of_twistedHasse_allLocals` and `README.md` §4.

## Contents

* `Defs.lean` (this file) — `LocalKorollar1`, `RankData`, `RankDataTrivial`, `LocalReconstruction`,
  `localisationToTrivial`;
* `RankCount.lean` — the cardinality squeeze in the form used here, and the group-theoretic core
  `le_stabSubgroup_of_unique_localGroup` (FKS);
* `Trivial.lean` — the twisted cohomology of the trivial group, and `loc ≠ 0 ⟹ H ⊓ D_A ≠ ⊥`;
* `Main.lean` — the assembly of `NK.BrauerTwist.LocalDecompositionCriterion`;
* `TrivialCoeff.lean` — the same assembly in the trivial-coefficient (`H2Profinite`) vocabulary at
  `p = 2`, i.e. a proof of `NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ'`;
* `Preserves.lean` — the per-finite-prime form consumed by
  `NK.BrauerTwist.preservesDecompositionGroups_of_localGalois`;
* `All.lean` — umbrella import.
-/

import Submission.NK.HasseTwist.All
import Submission.NK.LocalDecomposition.All
import Submission.NK.LocalStructure.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace NK.Indecomposed

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## Neukirch's Korollar 1 -/

/-- **Neukirch's Korollar 1**, in the form in which the criterion consumes it.

Let `L` be a `p`-adic field (presented as a completion `𝔮.adicCompletion L` of a number field at a
finite prime), `L'` a separable closure, and `H ≤ Gal(L'/L)` an *arbitrary* subgroup isomorphic to
the absolute Galois group `Gal(κ'/κ)` of a `p`-adic field `κ`.  Then `H` has **finite index** in
`Gal(L'/L)`.

This is A. Ivanov, arXiv:1309.2801, Lemma `lm:locfinindex`, attributed to Neukirch, Invent. Math.
**6** (1969), Korollar 1 (proved at the end of the proof of CoNF (12.1.9)): an injection
`Gal_L ⊆ Gal_M` of absolute Galois groups of local fields, with `L` `p`-adic, forces `M` to be
`p`-adic and `Gal_L` to have finite index in `Gal_M`.

**A word of warning about the general form.**  The sibling chapter states the same statement with
an extra parameter `κ₀ : IntermediateField κ κ'` ranging over *all* intermediate fields
(`NK.LocalDecomposition.LocalInjectionFiniteIndexSubgroup`), with `H ≅ Gal(κ'/↥κ₀)`.  That
general form is *unsatisfiable*: at `κ₀ = ⊤` the group `Gal(κ'/↥⊤)` is trivial, so `H = ⊥` is
admissible for the subgroup, and the conclusion becomes `0 < Nat.card (Gal(L'/L_𝔮))`, which fails
for a `p`-adic `L` (`Gal(L'/L_𝔮)` is infinite).  See
`NK.Indecomposed.not_localInjectionFiniteIndexSubgroup`, which proves this refutation.  The
correct reading of Neukirch's Korollar 1 — the one used by the criterion, where the subgroup
`H ≅ Gal(κ'/κ)` is a *full* local absolute Galois group — is the form below, in which no
`IntermediateField` parameter occurs. -/
def LocalKorollar1 (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
    Nonempty (H ≃* Gal(κ'/κ)) → 0 < H.relIndex ⊤

/-! ## The rank data of Neukirch's argument, with `μ_p`-coefficients -/

/-- **The rank data of Neukirch's argument, with `μ_p`-coefficients.**

This bundles the two inputs of the rank count of `Submission/Work/HasseTwist/Localisation.lean` for
the *labelled* situation `U ≅ Gal(κ'/κ)` (`κ` a `p`-adic field):

* `card_global` — `Nat.card (H2Twist p U) = p` for every closed `U ≅ Gal(κ'/κ)`.  Classically this
  is the local computation `H²(G_κ, μ_p) = Br(κ)[p] ≅ Z/p` of local class field theory
  (Kummer sequence + Hilbert 90; Serre, *Local Fields* XII–XIV; CoNF (7.2.6)), transported along
  the labelling.  This is the form `NK.BrauerTwist.LocalFieldBrauerCyclic` in the consumer's
  vocabulary.
* `card_local` — `p ≤ Nat.card (H2Twist p V)` for every **non-trivial local group** `V = H ⊓ D_A` of
  a labelled `H` over a finite prime `𝔭`.  Classically this is the same computation at the local
  fields of `H`, i.e. `H²(H ⊓ D_A, μ_p) ≅ Z/p` (CoNF (7.1.7), (7.1.8) as used by Ivanov).  The
  restriction `V ≠ ⊥` is necessary: for `V = ⊥` the group `H2Twist p ⊥` is a point
  (`NK.Indecomposed.subsingleton_h2Twist_bot`), so the hypothesis is false there, and `⊥` occurs as
  a local group exactly when the prime is decomposed in `K'/K`.
* `surj` — Neukirch's surjectivity `eq:NeukirchH2modifiedsurj` (NSW (9.2.1)), in the guarded form
  `NK.HasseTwist.NeukirchH2modifiedsurjAt` delivered by the Hasse chapter: the product of the
  restrictions to the local groups over the prime carrying a non-zero local component is
  surjective.

The **rank count** of the Hasse chapter
(`NK.HasseTwist.indecomposedAt_of_surjective`, and its refinement used here) turns this data into:
at most one *non-trivial* local group of `H` over the prime `𝔭`. -/
structure RankData (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime -/
  hp : p.Prime
  /-- **the local computation of local class field theory at `κ`**: `|H²(U, μ_p)| = p` for every
  closed `U ≅ Gal(κ'/κ)` -/
  card_global : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → Nat.card (H2Twist p U) = p
  /-- **the local computation at the non-trivial local groups**: `p ≤ |H²(H ⊓ D_A, μ_p)|` -/
  card_local : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
        V ≠ ⊥ → p ≤ Nat.card (H2Twist p V)
  /-- **Neukirch's (9.2.1)** in the guarded form: the localisation to the local groups over the prime
  carrying a non-zero local component is surjective -/
  surj : NeukirchH2modifiedsurjAt p K K' κ κ'

/-! ## Neukirch's local reconstruction -/

/-- **Neukirch's local reconstruction**: the two classical statements of Neukirch's Theorem 1 that
the assembly consumes.

* `korollar1` — the finiteness of the index `[D_A : H]` for a closed `H ≤ D_A ≅ Gal(κ'/κ)`
  (Neukirch's Korollar 1; Ivanov's `lm:locfinindex`).  In the workspace this is the local
  reconstruction of the `p`-adic field: it is derived from `NK.LocalStructure.LocalNUExistence`
  (Neukirch's Kennzeichnung), see `NK.LocalDecomposition.korollar1Local_iff_localNUExistence`.
* `finishingStep` — the maximality of decomposition groups: a closed self-normalising `H ≤ D_A`
  isomorphic to `Gal(κ'/κ)`, of finite relative index in `D_A`, is *equal* to `D_A` (Neukirch,
  Invent. Math. **6** (1969), Theorem 1; CoNF (12.1.9)–(12.1.10); A. Ivanov, arXiv:1309.2801, the
  Corollary following Proposition `cycloDecChar`).  In the workspace this is the named input
  `NK.LocalStructure.LocalFinishingStep`, *equivalent* by
  `NK.LocalDecomposition.localFinishingStep_iff_indexOne` to the index-one statement
  `NK.LocalDecomposition.IndexOneOfSelfNormalizing`.

Neither field is derivable from the rank data: by
`NK.LocalDecomposition.indexOne_of_localDecompositionCriterion` the criterion together with the
local Brauer nonvanishing *implies* the finishing step, so the pair (rank data, local
reconstruction) is exactly a splitting of the content of Neukirch's Theorem 1 into a
local-global-arithmetic half and a local half. -/
structure LocalReconstruction (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- Neukirch's Korollar 1 (Ivanov's `lm:locfinindex`) -/
  korollar1 : LocalKorollar1 κ κ'
  /-- the finishing step: decomposition groups are maximal (CoNF (12.1.9)–(12.1.10)) -/
  finishingStep : NK.LocalStructure.LocalFinishingStep p K K' κ κ'

/-! ## The trivial-coefficient vocabulary at `p = 2` -/

/-- The restriction map on the trivial-coefficient cohomology, to a local group of `H` over `𝔭`
(given by the family `NK.HasseTwist.localGroupSubgroupsOver`; this is the same set of subgroups as
`NK.HassePrinciple.localGroupsOver`, since both are the range of `A ↦ H ⊓ D_A`). -/
noncomputable def localisationToTrivial (p : ℕ) (H : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.BrauerHasse.H2Profinite p H →
      ∀ V : ↥(localGroupSubgroupsOver (K := K) (K' := K') H 𝔭),
        NK.BrauerHasse.H2Profinite p V.1 :=
  fun x V => NK.LocalDecomposition.H2Profinite.res p
    (le_of_mem_localGroupSubgroupsOver (K := K) (K' := K') V.2) x

/-- **The rank data of Neukirch's argument in the trivial-coefficient vocabulary `H²(·, Z/p)`.**

This is `NK.Indecomposed.RankData` with `NK.BrauerTwist.H2Twist p` replaced by
`NK.BrauerHasse.H2Profinite p`; the two agree at `p = 2`, where the coefficient module
`μ_2 = {±1} = Z/2` carries the trivial action.  It feeds
`NK.Indecomposed.indecomposedPrime_two_of_rankData`, whose conclusion is the sibling chapter's
input `NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ'`. -/
structure RankDataTrivial (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime -/
  hp : p.Prime
  /-- `|H²(U, Z/p)| = p` for every closed `U ≅ Gal(κ'/κ)` -/
  card_global : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → Nat.card (NK.BrauerHasse.H2Profinite p U) = p
  /-- `p ≤ |H²(H ⊓ D_A, Z/p)|` for every non-trivial local group -/
  card_local : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
        V ≠ ⊥ → p ≤ Nat.card (NK.BrauerHasse.H2Profinite p V)
  /-- the guarded surjectivity of the localisation over the prime carrying a non-zero local
  component -/
  surj : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (∃ (A : PlacesOverPrime K K' 𝔭) (x : NK.BrauerHasse.H2Profinite p H),
        NK.BrauerHasse.H2Profinite.loc p H x A.toOverFinitePrime ≠ 0) →
      Function.Surjective (localisationToTrivial (K := K) (K' := K') p H 𝔭)

end NK.Indecomposed
