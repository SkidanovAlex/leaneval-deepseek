/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The twisted Hasse principle: the corollaries in the consumer's vocabulary

The main theorem of the chapter is `NK.HasseTwist.sha2Vanishing`, the Hasse principle
`NK.BrauerTwist.Sha2Vanishing` proved from the inputs bundled in `NK.HasseTwist.Sha2Input`.
This module records the corollaries that the Neukirch–Uchida development consumes, i.e. the
statements of `Submission/Work/BrauerTwist/Hasse.lean` and `.../Main.lean` with their
`Sha2Vanishing` hypothesis discharged:

* `NK.HasseTwist.exists_loc_ne_zero` — every non-zero class of `H²(H, μ_p)` has a non-zero local
  component at some place of `K'` over a finite prime of `K` (the cohomological core of Neukirch's
  argument);
* `NK.HasseTwist.exists_nonzero_class_with_loc_ne_zero` and
  `NK.HasseTwist.exists_loc_ne_zero_of_localH2Input` — the same, in the vocabulary of
  `NK.BrauerTwist.LocalH2Input`;
* `NK.HasseTwist.exists_decompositionGroup_of_localGalois` — Neukirch's characterisation of
  decomposition groups, with `μ_p`-coefficients and with the Hasse-principle hypothesis discharged;
* `NK.HasseTwist.fieldAxiom_of_sha2Input` — the number-theoretic input `Sha2Input.hasse_norm`
  consumed: it yields the field axiom of the on-disk global class field theory for every cyclic
  extension of number fields.
-/

import Submission.NK.HasseTwist.Inputs
import Submission.NK.BrauerTwist.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The number-theoretic input is consumed.**  The Hasse norm theorem for cyclic extensions
(`Sha2Input.hasse_norm`) yields the field axiom `NK.GlobalCFT.FieldAxiom K L` of the on-disk
class formation for every cyclic extension `L/K` of number fields: the norm subgroup
`N_{L/K} C_L` has finite index `[L : K]` in `C_K`. -/
theorem fieldAxiom_of_sha2Input (p : ℕ)
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    {E F : Type u} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [FiniteDimensional E F] [IsGalois E F] [IsMulCommutative (F ≃ₐ[E] F)]
    (hcyc : IsCyclic (F ≃ₐ[E] F)) :
    NK.GlobalCFT.FieldAxiom E F :=
  NK.HassePrinciple.fieldAxiom_of_hasseNormTheorem h.hasse_norm hcyc

/-- **The twisted Hasse principle in the vocabulary of the consumer.**  Every non-zero class of
`H²(H, μ_p)`, for `H ≤ Gal(K'/K)` a closed subgroup isomorphic to `Gal(κ'/κ)`, has a non-zero local
component at some place of `K'` over a finite prime of `K`.

This is `NK.BrauerTwist.exists_loc_ne_zero` with the Hasse-principle hypothesis
`NK.BrauerTwist.Sha2Vanishing` discharged by `NK.HasseTwist.sha2Vanishing`. -/
theorem exists_loc_ne_zero (p : ℕ)
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Twist p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Twist.loc p H x A ≠ 0 :=
  NK.BrauerTwist.exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Vanishing (K := K) (K' := K') (κ := κ) (κ' := κ') p h) H hH hκ hx

/-- **The twisted Hasse principle in the vocabulary of `LocalH2Input`.**  A caller who supplies
`NK.BrauerTwist.LocalH2Input p K K' κ κ'` (the local Brauer input of local class field theory:
`Br(κ)[p] ≅ Z/p`, unconditional for a `p`-adic `κ`) obtains: for every closed subgroup
`H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, there is a non-zero class of `H²(H, μ_p)` with a
non-zero local component at some place of `K'` over a finite prime of `K`. -/
theorem exists_nonzero_class_with_loc_ne_zero (p : ℕ)
    (hLoc : LocalH2Input (K := K) (K' := K') p κ κ')
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    ∃ (x : H2Twist p H) (A : OverFinitePrime K K'),
      x ≠ 0 ∧ H2Twist.loc p H x A ≠ 0 := by
  obtain ⟨x, hx⟩ := hLoc H hH hκ
  obtain ⟨A, hA⟩ := exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p h H hH hκ hx
  exact ⟨x, A, hx, hA⟩

/-- **The twisted Hasse principle in the consumer's phrasing, with `LocalH2Input` as the only
hypothesis of the application.**  Under the local Brauer input `NK.BrauerTwist.LocalH2Input`
(which supplies non-zero classes of `H²(H, μ_p)` for the subgroups `H ≅ Gal(κ'/κ)`), every non-zero
class of `H²(H, μ_p)` has a non-zero local component at some place of `K'` over a finite prime
of `K`. -/
theorem exists_loc_ne_zero_of_localH2Input (p : ℕ)
    (_hLoc : LocalH2Input (K := K) (K' := K') p κ κ')
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Twist p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Twist.loc p H x A ≠ 0 :=
  exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p h H hH hκ hx

section Consumer

/-- **The consumer's interface in a single hypothesis.**  The two inputs that a caller in the
Neukirch–Uchida development needs in order to invoke the twisted Hasse principle in its local form:
the local Brauer input `NK.BrauerTwist.LocalH2Input` (which supplies non-zero classes of
`H²(H, μ_p)`) and the Hasse-principle inputs `NK.HasseTwist.Sha2Input` of this chapter. -/
structure ConsumerHypotheses (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the local Brauer input of local class field theory (`Br(κ)[p] ≅ Z/p`). -/
  localBrauer : LocalH2Input p K K' κ κ'
  /-- the Hasse-principle inputs of this chapter. -/
  hasse : Sha2Input p K K' κ κ'

/-- **The twisted Hasse principle, with the consumer's hypotheses supplied as one bundle.** -/
theorem exists_loc_ne_zero_of_consumerHypotheses (p : ℕ)
    (h : ConsumerHypotheses (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Twist p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Twist.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_localH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p
    h.localBrauer h.hasse H hH hκ hx

end Consumer

/-- **Neukirch's characterisation of decomposition groups, "if" direction, with `μ_p`-coefficients
and with the Hasse-principle hypothesis discharged** (CoNF XII (12.1.9)).

A closed subgroup `H ≤ G_K = Gal(K̄/K)` of the absolute Galois group of a number field `K` which is
self-normalising and isomorphic to the absolute Galois group `Gal(κ̄/κ)` of a `p`-adic field `κ` is
the decomposition group of a place of `K̄` over a finite prime of `K`.

This is `NK.BrauerTwist.exists_decompositionGroup_of_localGalois` with its `Sha2Vanishing`
hypothesis discharged by `NK.HasseTwist.sha2Vanishing`; only the local Brauer input
`NK.BrauerTwist.LocalH2Input` and Neukirch's local finishing step
`NK.BrauerTwist.LocalDecompositionCriterion` remain, together with the inputs of this chapter. -/
theorem exists_decompositionGroup_of_localGalois
    (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H)
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : LocalH2Input (K := K) (K' := K') p κ κ')
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') p κ κ') :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  NK.BrauerTwist.exists_decompositionGroup_of_localGalois (K := K) (K' := K')
    (κ := κ) (κ' := κ') p hp H hH hN hκ hLoc
    (sha2Vanishing (K := K) (K' := K') (κ := κ) (κ' := κ') p h) hStep

/-- **The same, in the `FinitePlace` vocabulary.** -/
theorem exists_finitePlace_of_localGalois
    (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H)
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : LocalH2Input (K := K) (K' := K') p κ κ')
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') p κ κ') :
    ∃ A : {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤},
      MulAction.stabilizer Gal(K'/K) A.1 = H :=
  NK.BrauerTwist.exists_finitePlace_of_localGalois (K := K) (K' := K')
    (κ := κ) (κ' := κ') p hp H hH hN hκ hLoc
    (sha2Vanishing (K := K) (K' := K') (κ := κ) (κ' := κ') p h) hStep

end NK.HasseTwist
