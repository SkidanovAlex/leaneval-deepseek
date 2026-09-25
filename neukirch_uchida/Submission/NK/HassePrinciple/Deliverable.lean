/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# THE DELIVERABLE — the Hasse principle in the shape the Neukirch–Uchida development calls

Umbrella development: `Submission/Work/HassePrinciple/` (README §16, §22, and the headline at the
top of the README).

This module is written **for the requester** (`fundmath3-neukirch_uchida`).  It contains the
chapter's consumer interface in one place and names, for each entry point, exactly what the caller
supplies and what it obtains.

## What to import

```lean
import Submission.NK.HassePrinciple.Deliverable
```

(namespace `NK.HassePrinciple`; this re-exports the whole chapter through `All.lean`'s modules —
a caller who wants everything should import `Submission.NK.HassePrinciple.All`).

## The theorem to call

```lean
NK.HassePrinciple.hassePrinciple_of_localH2Input
    (hLoc : NK.BrauerHasse.LocalH2Input p K K' κ κ')   -- owed by NK.LocalCFT
    (h    : NK.HassePrinciple.RankInput p K K' κ κ')   -- the chapter's one arithmetic input
    (H : Subgroup Gal(K'/K)) (hH : IsClosed H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0
```

i.e. **under the local Brauer input and one arithmetic input, every non-zero class of
`H²(H, Z/p)` (for `H ≤ Gal(K'/K)` closed and isomorphic to `Gal(κ'/κ)`) has a non-zero local
component at some place of `K'` over a finite prime of `K`.**  This is
`NK.BrauerHasse.exists_loc_ne_zero` with its `Sha2Vanishing` hypothesis discharged
(`NK.HassePrinciple.sha2Vanishing_of_rankInput`).

The same statement with the two inputs bundled is
`NK.HassePrinciple.exists_loc_ne_zero_of_consumerHypotheses` (bundle
`NK.HassePrinciple.ConsumerHypotheses`), and with Neukirch's (9.2.1) instead of its rank-count
form it is `NK.HassePrinciple.hassePrinciple_of_localH2Input_of_nswsInput` (bundle
`NK.HassePrinciple.ConsumerInputNSW`).

## Why `LocalH2Input` alone is not a possible hypothesis, and why there is a second input

The deliverable asks for a corollary "so that a caller only has to supply `LocalH2Input`".  That is
not possible, and the reason is a *theorem* of this chapter, not a limitation of effort:

1. **The literal target is false.**  `NK.HassePrinciple.ArchimedeanDefect E E'` is the datum of a
   non-zero `x : H2Profinite 2 ⊤` whose localisation at every `A : OverFinitePrime E E'` vanishes,
   and `NK.HassePrinciple.not_sha2Vanishing_of_archimedeanDefect` /
   `NK.HassePrinciple.not_archimedeanDefect_of_sha2Vanishing` prove
   `ArchimedeanDefect E E' ↔ ¬ Sha2Vanishing 2 E E' E E'`.
   Classically such an `x` exists for every formally real `E` (the quaternion class `(-1,-1)`:
   invariants `1/2` at the two real places of `ℚ(√2)`, `0` at every finite place), so
   `NK.BrauerHasse.Sha2Vanishing 2 E E' E E'` is *false* — a statement with no hypotheses cannot
   be proved.  The κ-labelling is exactly what removes the defect: the labelled `U` are
   `2`-torsion-free (`NK.HassePrinciple.NoTwoTorsion`,
   `NK.HassePrinciple.noTwoTorsion_of_mulEquiv`) for a `p`-adic `κ`; see README §13.1, §19.
2. **Modulo the local inputs, the target is *equivalent* to Neukirch's Theorem 1.**
   `NK.HassePrinciple.sha2Vanishing_iff_localCharacterisation` proves

   > `Sha2Vanishing p K K' κ κ' ↔ LocalCharacterisation p K K' κ κ'`

   where `NK.HassePrinciple.LocalCharacterisation` is "every closed `U ≤ Gal(K'/K)` isomorphic to
   `Gal(κ'/κ)` is contained in the decomposition group of a place over a finite prime" — the "if"
   direction of Neukirch, *Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*,
   Invent. Math. **6** (1969), Theorem 1 = Neukirch–Schmidt–Wingberg (12.1.9), i.e. the core
   theorem of the paper whose Hasse-principle input this chapter was asked to discharge.  It
   follows that no statement *about cyclic extensions of number fields and their norm groups* can
   imply the target (README §16.3, §17.3): in particular the licensed cyclic input
   (`NK.HassePrinciple.CyclicHasseInput`) cannot, and the chapter proves *why* its finite-level
   localisation misses the target's local groups
   (`NK.HassePrinciple.le_stabSubgroup_iff_localInclHom_surjective`,
   `NK.HassePrinciple.iInf_sup_fixingSubgroup_eq_stabSubgroup`: `⋂_L D_A·Gal(K'/L) = D_A`).

So the smallest faithful input is an arithmetic statement of the same depth as the target, and the
chapter's form of it is `NK.HassePrinciple.RankInput` (Neukirch's *surjectivity* of the
localisation at a place — Neukirch (1969) Thm 1, NSW (9.2.1), the input the sibling chapters carry
as `NK.HasseTwist.NeukirchH2modifiedsurj` and `NK.LocalDecomposition.IndecomposedPrime` —
together with the local computations of local class field theory).  It is available in the
interchangeable forms below, each with a *proved* reduction to the target:

| input | reduction | what it assumes |
|---|---|---|
| `NK.HassePrinciple.RankInput` | `sha2Vanishing_of_rankInput` | finiteness of `H²(U,Z/p)` + surjectivity at one place + order comparison |
| `NK.HassePrinciple.SurjInput` | `rankInput_of_surjInput`, `sha2Vanishing_of_rankInput` | the same in product form over a prime (NSW (9.2.1)) |
| `NK.HassePrinciple.NSWSInput` | `sha2Vanishing_of_nswsInput` | the surjectivity at a prime + the local computations at `κ` and at the local groups |
| `NK.HassePrinciple.IndexInput` | `sha2Vanishing_of_indexInput` | a place whose local degree inside `U` is prime to `p` (no cohomology) |
| `NK.HassePrinciple.LimitPassage` | `sha2Vanishing_of_limitPassage` | the Hasse principle itself, κ-labelled (the old route) |

and, if the caller's own development can deliver Neukirch's local characterisation of the
decomposition groups, the chapter needs **no cohomological input at all**:
`NK.HassePrinciple.sha2Vanishing_of_localCharacterisation` (with
`exists_loc_ne_zero_of_localH2Input_and_localCharacterisation` below as the consumer form).

**The composition with the consumer's own chapter.**  `NK.LocalDecomposition` delivers
`NK.BrauerHasse.LocalDecompositionCriterion`, whose hypothesis is `Subgroup.normalizer H = H`
(a decomposition group is self-normalising, CoNF (12.1.4)).  The theorem
`NK.HassePrinciple.sha2Vanishing_of_localDecomposition` composes it with this chapter's
reduction: from the criterion, the local Brauer input, Neukirch's (9.2.1) in the local-groups form
(`NSWSInput`) and the hypothesis `NK.HassePrinciple.SelfNormalisingLabeled` (closed subgroups
isomorphic to `Gal(κ'/κ)` are self-normalising — exactly the hypothesis the criterion carries),
the target `NK.BrauerHasse.Sha2Vanishing` follows.  The consumer corollary is
`NK.HassePrinciple.hassePrinciple_of_localDecomposition`, and the same with Neukirch's input in
the rank-count form is `NK.HassePrinciple.sha2Vanishing_of_localDecomposition_of_rankInput`.

## What the chapter also delivers (finite case, from the licensed input)

`NK.HassePrinciple.hbnUnits_from_cyclicInput` — the relative Hasse–Brauer–Noether theorem
`H²(Gal(L/K), Lˣ) ↪ ∏_w H²(Γ_w, L_wˣ)` for **every** finite Galois extension of number fields,
from the licensed cyclic input alone (Milne, *CFT*, VII.7.1); and
`NK.HassePrinciple.fieldAxiom_of_cyclicHasseInput` (the field axiom of the on-disk global class
field theory from the licensed Hasse norm theorem).  See README §13.4 for the chain and §21 for the
one point (the Kummer correction) at which the finite case does *not* transport to the `Z/p`
coefficient statement.
-/

import Submission.NK.HassePrinciple.Main
import Submission.NK.HassePrinciple.Spec
import Submission.NK.HassePrinciple.NSWSConsumer
import Submission.NK.HassePrinciple.IndexInput
import Submission.NK.HassePrinciple.LocalCharacterisation
import Submission.NK.BrauerHasse.Main

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
variable {p : ℕ}

/-- **THE THEOREM TO CALL.**  Under the local Brauer input
`NK.BrauerHasse.LocalH2Input p K K' κ κ'` (owed by `NK.LocalCFT`) and the chapter's single
arithmetic input `NK.HassePrinciple.RankInput p K K' κ κ'` (Neukirch's (9.2.1) — the surjectivity
of the localisation at a place — together with the local computations of local class field theory),
every non-zero class of `H²(H, Z/p)`, for `H ≤ Gal(K'/K)` closed with
`Nonempty (H ≃* Gal(κ'/κ))`, has a non-zero local component at some place of `K'` over a finite
prime of `K`.

This is `NK.BrauerHasse.exists_loc_ne_zero` with the Hasse-principle hypothesis discharged by
`NK.HassePrinciple.sha2Vanishing_of_rankInput`.  **No Hasse-principle statement is among the
hypotheses.**  See the module docstring for why the second hypothesis cannot be removed (the target
is equivalent to Neukirch's Theorem 1) and for the alternatives
(`NSWSInput`, `SurjInput`, `IndexInput`, `LocalCharacterisation`). -/
theorem hassePrinciple_of_localH2Input
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_localH2Input (K := K) (K' := K') (κ := κ) (κ' := κ')
    hLoc h H hH hκ hx

/-- **The same theorem with Neukirch's (9.2.1) in its product/`NSWSInput` form** (the form in
which the input is classical: the surjectivity of the localisation to the local groups over a
prime, NSW (9.2.1), plus the local computations of local class field theory at `κ` and at the local
groups). -/
theorem hassePrinciple_of_localH2Input_of_nswsInput
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_nswsInput_and_localH2Input (K := K) (K' := K') (κ := κ) (κ' := κ')
    p hLoc h H hH hκ hx

/-- **The same theorem with the underlying product form** (`NK.HassePrinciple.SurjInput`), which
is Neukirch's `eq:NeukirchH2modifiedsurj` (NSW (9.2.1)) together with the order comparison at the
local group. -/
theorem hassePrinciple_of_localH2Input_of_surjInput
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : SurjInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_rankInput_and_localH2Input (K := K) (K' := K') (κ := κ) (κ' := κ')
    (rankInput_of_surjInput h) hLoc H hH hκ hx

/-- **The cohomology-free form**: if some place of `K'` has local degree inside `U` prime to `p`
at every finite level (`NK.HassePrinciple.IndexInput`), then the conclusion holds — with no
cohomological input beyond the local Brauer input. -/
theorem hassePrinciple_of_localH2Input_of_indexInput
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : IndexInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_indexInput_and_localH2Input (K := K) (K' := K') (κ := κ) (κ' := κ')
    h hLoc H hH hκ hx

/-- **The form to use if the caller's own development can deliver Neukirch's local
characterisation of the decomposition groups** — i.e.
`NK.HassePrinciple.LocalCharacterisation p K K' κ κ'`, which *is* the condition
`∀ U closed labelled, ∃ A, U ≤ stabSubgroup A.1`, the "inert place" hypothesis of
`NK.HassePrinciple.sha2Vanishing_of_inert` (in the sibling chapters this is the conclusion of
`NK.LocalDecomposition`, from `NeukirchH2modifiedsurj`/`IndecomposedPrime`).  Then the chapter needs **no cohomological input**:
the localisation at the place found is injective (`NK.HassePrinciple.loc_injective_of_le_stabSubgroup`),
so every non-zero class has a non-zero local component.

The hypotheses are only the local Brauer input and `NK.HassePrinciple.LocalCharacterisation`. -/
theorem exists_loc_ne_zero_of_localH2Input_and_localCharacterisation
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : LocalCharacterisation (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Vanishing_of_localCharacterisation (K := K) (K' := K') (κ := κ) (κ' := κ') p h)
    H hH hκ hx

/-! ## The composition with the consumer's own chapter (`NK.LocalDecomposition`)

The consumer's `NK.BrauerHasse.LocalDecompositionCriterion` — delivered by
`NK.LocalDecomposition` from its four inputs (`IndecomposedPrime`, `InjectionFiniteIndex`,
`LocalGaloisInfinite`, `IndexOneOfSelfNormalizing`) — carries the *self-normalising* hypothesis
`Subgroup.normalizer H = H` (CoNF (12.1.4): a decomposition group is self-normalising;
`NK.LocalDecomposition.normalizer_stabSubgroup_eq`).  It produces, for a self-normalising
`H ≅ Gal(κ'/κ)`, a place with `D_{A'} = H`.

The theorems below compose it with the chapter's reduction: given the criterion, the local Brauer
input, Neukirch's (9.2.1) in the `NSWSInput` form, and the hypothesis that the closed subgroups
isomorphic to `Gal(κ'/κ)` are self-normalising
(`NK.HassePrinciple.SelfNormalisingLabeled`), the target `NK.BrauerHasse.Sha2Vanishing` holds —
so the consumer's own criterion is all the extra license their endgame needs. -/

/-- **The Hasse principle from the consumer's own local-decomposition criterion.**  The hypotheses
are: the local Brauer input, Neukirch's (9.2.1) in the local-groups form (`NSWSInput`), the
criterion `NK.BrauerHasse.LocalDecompositionCriterion` (the output of `NK.LocalDecomposition`),
and the statement that closed subgroups isomorphic to `Gal(κ'/κ)` are self-normalising
(`NK.HassePrinciple.SelfNormalisingLabeled`), which is exactly the hypothesis under which the
criterion is stated. -/
theorem sha2Vanishing_of_localDecomposition
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hSN : SelfNormalisingLabeled (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_localCharacterisationSN (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (fun U hU hN hκ => localCharacterisation_of_nswsInput (K := K) (K' := K') (κ := κ) (κ' := κ')
      h hLoc hStep U hU hN hκ)
    hSN

/-- **The consumer corollary of the composition with their own criterion**: under the local Brauer
input, Neukirch's (9.2.1), the local-decomposition criterion and the self-normalising hypothesis,
every non-zero class of `H²(H, Z/p)` has a non-zero local component at some place of `K'` over a
finite prime of `K`. -/
theorem hassePrinciple_of_localDecomposition
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hSN : SelfNormalisingLabeled (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Vanishing_of_localDecomposition (K := K) (K' := K') (κ := κ) (κ' := κ')
      hLoc h hStep hSN) H hH hκ hx

/-- **The same composition with Neukirch's input in the rank-count form** (`RankInput`, the weakest
of the chapter's inputs). -/
theorem sha2Vanishing_of_localDecomposition_of_rankInput
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hin : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hSN : SelfNormalisingLabeled (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_localCharacterisationSN (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (fun U hU hN hκ => localCharacterisation_of_rankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p
      hin hLoc hStep U hU hN hκ)
    hSN

/-- **THE THEOREM TO CALL FOR THE ENDGAME** — Neukirch's characterisation of the decomposition
groups (the "if" direction of CoNF (12.1.9)), with the Hasse-principle hypothesis discharged by the
chapter: a closed, self-normalising subgroup `H ≤ Gal(K'/K)` isomorphic to the absolute Galois
group of a `p`-adic field is the decomposition group of a place of `K'` over a finite prime of `K`.

The caller supplies the local Brauer input, the chapter's input (`RankInput`, here in the form
derived from the `LocalH2Input`-first interface) and the local finishing step
`NK.BrauerHasse.LocalDecompositionCriterion`. -/
theorem neukirchCriterion_of_localH2Input
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  exists_decompositionGroup_of_localGalois (K := K) (K' := K') (κ := κ) (κ' := κ')
    H hH hN hκ hLoc h hStep

/-- **The endgame from Neukirch's (9.2.1) in the `NSWSInput` form.** -/
theorem neukirchCriterion_of_nswsInput
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  exists_decompositionGroup_of_nswsInput (K := K) (K' := K') (κ := κ) (κ' := κ')
    p hLoc hStep h H hH hN hκ

/-- **The single-hypothesis form of the headline theorem**: the two inputs bundled as
`NK.HassePrinciple.ConsumerHypotheses`. -/
theorem hassePrinciple_of_consumerHypotheses
    (h : ConsumerHypotheses (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_consumerHypotheses (K := K) (K' := K') (κ := κ) (κ' := κ')
    h H hH hκ hx

end NK.HassePrinciple
