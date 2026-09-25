/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The consumer corollaries from Neukirch's (9.2.1)

Umbrella development: `Submission/Work/HassePrinciple/` (README §18).

This module states the chapter's target and its consumer corollaries in the vocabulary of the
Neukirch–Uchida development, with `NK.HassePrinciple.NSWSInput` (Neukirch's (9.2.1) plus the local
computations of local class field theory) as the only arithmetic input added to the local Brauer
input `NK.BrauerHasse.LocalH2Input`:

* `NK.HassePrinciple.sha2Vanishing_of_nswsInput` — the Hasse principle
  `NK.BrauerHasse.Sha2Vanishing`;
* `NK.HassePrinciple.exists_loc_ne_zero_of_nswsInput_and_localH2Input` — **the corollary requested
  by the Neukirch–Uchida development**: under `LocalH2Input p K K' κ κ'` and Neukirch's (9.2.1),
  every non-zero class of `H²(H, Z/p)` has a non-zero local component at a place of `K'` over a
  finite prime of `K`;
* `NK.HassePrinciple.exists_decompositionGroup_of_nswsInput` — Neukirch's characterisation of the
  decomposition groups (CoNF (12.1.9), "if" direction) with the Hasse-principle hypothesis
  discharged by `sha2Vanishing_of_nswsInput`;
* `NK.HassePrinciple.ConsumerInputNSW` — the two inputs bundled, with
  `exists_loc_ne_zero_of_consumerInputNSW` as the single-hypothesis form.

The point of the module is that the caller supplies **no Hasse-principle hypothesis**: the
surjectivity (9.2.1) together with the local computations of local class field theory is enough,
because Neukirch's rank count
(`NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective`) turns it into the statement that
the prime is indecomposed, and the localisation at an inert place is injective
(`NK.HassePrinciple.loc_injective_of_le_stabSubgroup`).
-/

import Submission.NK.HassePrinciple.LocalGroupInput
import Submission.NK.BrauerHasse.Main

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The corollary in the vocabulary of the consumer.**  Under the local Brauer input
`NK.BrauerHasse.LocalH2Input p K K' κ κ'` (`Br(κ)[p] ≅ Z/p`) and Neukirch's (9.2.1) plus the local
computations (bundled as `NK.HassePrinciple.NSWSInput`), every non-zero class of `H²(H, Z/p)` for
a closed `H ≤ Gal(K'/K)` with `Nonempty (H ≃* Gal(κ'/κ))` has a non-zero local component at some
place of `K'` over a finite prime of `K`.

This is `NK.BrauerHasse.exists_loc_ne_zero` instantiated with `NK.HassePrinciple.sha2Vanishing_of_nswsInput`;
the only hypotheses are the two inputs, and **no Hasse-principle statement** is among them. -/
theorem exists_loc_ne_zero_of_nswsInput_and_localH2Input (p : ℕ)
    (hLoc : LocalH2Input p K K' κ κ')
    (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero (K := K) (K' := K') p (sha2Vanishing_of_nswsInput h)
    H hH hκ hx

/-- **Neukirch's characterisation of the decomposition groups from the chapter's input**
(the "if" direction of CoNF (12.1.9)): a closed self-normalising `H ≤ Gal(K'/K)` isomorphic to
`Gal(κ'/κ)` is the decomposition group of a place of `K'` over a finite prime of `K`.

The Hasse-principle hypothesis of `NK.BrauerHasse.exists_decompositionGroup_of_localGalois` is
discharged by `NK.HassePrinciple.sha2Vanishing_of_nswsInput`; the remaining inputs are the local
Brauer input and the local finishing step of the Neukirch argument. -/
theorem exists_decompositionGroup_of_nswsInput (p : ℕ)
    (hLoc : LocalH2Input p K K' κ κ') (hStep : LocalDecompositionCriterion p K K' κ κ')
    (h : NSWSInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A' = H :=
  NK.BrauerHasse.exists_decompositionGroup_of_localGalois (K := K) (K' := K') p h.hp
    H hH hN hκ hLoc (sha2Vanishing_of_nswsInput h) hStep

/-- **The two inputs of the chapter, bundled**: the local Brauer computation
(`NK.BrauerHasse.LocalH2Input`, owed by the local side `NK.LocalCFT`) and Neukirch's (9.2.1)
together with the local computations at the local groups (`NK.HassePrinciple.NSWSInput`).  No
Hasse-principle hypothesis occurs in either field. -/
structure ConsumerInputNSW (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the local Brauer computation `Br(κ)[p] ≅ Z/p`, transported along the labelling. -/
  local_brauer : LocalH2Input p K K' κ κ'
  /-- Neukirch's (9.2.1) with the local computations of local class field theory. -/
  nsws : NSWSInput p K K' κ κ'

/-- **The single-hypothesis form of the consumer corollary.** -/
theorem exists_loc_ne_zero_of_consumerInputNSW (p : ℕ)
    (h : ConsumerInputNSW (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_nswsInput_and_localH2Input p h.local_brauer h.nsws H hH hκ hx

end NK.HassePrinciple
