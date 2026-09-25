/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle: the corollaries in the consumer's vocabulary

Umbrella development: `Submission/Work/HassePrinciple/` (README §16, §22).

**Read `Submission/Work/HassePrinciple/Deliverable.lean` first**: it is the module written for the
requester (`fundmath3-neukirch_uchida`) and it names the single theorem to call.

This module records the corollaries that the Neukirch–Uchida development consumes, **with the
chapter's amended input as the only added hypothesis**:

* `NK.HassePrinciple.exists_loc_ne_zero_of_localH2Input` — **the corollary in the requested
  shape**: the caller supplies `NK.BrauerHasse.LocalH2Input p K K' κ κ'` (the local Brauer
  computation, owed by `NK.LocalCFT`) and the chapter's input
  `NK.HassePrinciple.RankInput p K K' κ κ'` (Neukirch's surjectivity at a place together with the
  local computations of local class field theory) and obtains
  `∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0` for every non-zero
  `x : H2Profinite p H`, `H ≤ Gal(K'/K)` closed with `Nonempty (H ≃* Gal(κ'/κ))`.  **The Hasse
  principle is not among the hypotheses**;
* `NK.HassePrinciple.exists_loc_ne_zero` — the same with `RankInput` as the only hypothesis of
  the application;
* `NK.HassePrinciple.exists_nonzero_class_with_loc_ne_zero` and the bundle
  `NK.HassePrinciple.ConsumerHypotheses` with
  `NK.HassePrinciple.exists_loc_ne_zero_of_consumerHypotheses` (single-hypothesis form);
* `NK.HassePrinciple.exists_decompositionGroup_of_localGalois` — Neukirch's characterisation of
  the decomposition groups with its Hasse-principle hypothesis discharged by the rank-count route
  (this is the endgame the sibling chapter `NK.LocalDecomposition` consumes);
* `NK.HassePrinciple.fieldAxiom_of_cyclicHasseInput` — the *licensed* cyclic input
  (`NK.HassePrinciple.CyclicHasseInput`) consumed: it yields the field axiom
  `NK.GlobalCFT.FieldAxiom E F` of the on-disk global class field theory for every cyclic
  extension of number fields.  This is where the Hasse norm theorem is used; it is *not* used by
  the reduction to `Sha2Vanishing` (README §22).

### The legacy level-wise route (kept for the record, **not** for use)

The statements below carry the old input `NK.HassePrinciple.Sha2Input` (whose second field is the
*fine* level-wise Hasse principle, a form that the classical theory does not produce and that the
licensed cyclic input cannot reach: README §12.2, §13.7(iv), §14.6, §17).  They are kept under
names of the form `..._of_sha2Input` so that nothing is lost, and they are excluded from the
chapter's interface.  Do not build on them.
-/

import Submission.NK.HassePrinciple.Inputs
import Submission.NK.HassePrinciple.CyclicBase
import Submission.NK.HassePrinciple.RankInput
import Submission.NK.HassePrinciple.Spec
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

/-! ## The licensed cyclic input is consumed here

The Hasse norm theorem for cyclic extensions of number fields is used by the chapter to prove the
relative Hasse–Brauer–Noether theorem (`NK.HassePrinciple.hbnUnits_from_cyclicInput`) and, here,
to produce the *field axiom* of the on-disk global class field theory.  It plays no role in the
reduction of `NK.BrauerHasse.Sha2Vanishing` to Neukirch's input; see the module docstring of
`Spec.lean` and README §22. -/

/-- **The number-theoretic (licensed) input is consumed.**  The Hasse norm theorem for cyclic
extensions — the second field of the licensed `NK.HassePrinciple.CyclicHasseInput` — yields the
field axiom `NK.GlobalCFT.FieldAxiom E F` of the on-disk class formation for every cyclic
extension `F/E` of number fields: the norm subgroup `N_{F/E} C_F` has finite index `[F : E]` in
`C_E`. -/
theorem fieldAxiom_of_cyclicHasseInput (h : CyclicHasseInput)
    {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [FiniteDimensional E F] [IsGalois E F] [IsMulCommutative (F ≃ₐ[E] F)]
    (hcyc : IsCyclic (F ≃ₐ[E] F)) :
    NK.GlobalCFT.FieldAxiom E F :=
  fieldAxiom_of_hasseNormTheorem h.hasse_norm hcyc

/-- The same, from the legacy input structure `NK.HassePrinciple.Sha2Input` (whose licensed field
is this theorem's hypothesis). -/
theorem fieldAxiom_of_sha2Input (p : ℕ)
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    {E F : Type u} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [FiniteDimensional E F] [IsGalois E F] [IsMulCommutative (F ≃ₐ[E] F)]
    (hcyc : IsCyclic (F ≃ₐ[E] F)) :
    NK.GlobalCFT.FieldAxiom E F :=
  fieldAxiom_of_hasseNormTheorem h.hasse_norm hcyc

/-! ## The amended consumer corollaries

The chapter's input `NK.HassePrinciple.RankInput` is Neukirch's: the *finiteness* of
`H²(U, Z/p)` at the labelled subgroups and the *surjectivity* of the localisation at a place where
the local group is at least as large (Neukirch, Invent. Math. **6** (1969), Theorem 1; NSW (9.2.1))
— together with the local computations of local class field theory.  The Hasse principle itself is
not assumed. -/

/-- **The Hasse principle in the vocabulary of the consumer**, from the chapter's input: every
non-zero class of `H²(H, Z/p)`, for `H ≤ Gal(K'/K)` a closed subgroup isomorphic to `Gal(κ'/κ)`, has
a non-zero local component at some place of `K'` over a finite prime of `K`.

This is `NK.BrauerHasse.exists_loc_ne_zero` with the Hasse-principle hypothesis discharged by
`NK.HassePrinciple.sha2Vanishing_of_rankInput`. -/
theorem exists_loc_ne_zero (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Vanishing_of_rankInput h) H hH hκ hx

/-- **The Hasse principle in the consumer's phrasing, with `LocalH2Input` as the first
hypothesis.**  The two mathematical inputs are the local Brauer computation
`NK.BrauerHasse.LocalH2Input p K K' κ κ'` (owed by `NK.LocalCFT`) and the chapter's
`NK.HassePrinciple.RankInput` (Neukirch's (9.2.1) plus the local computations of local class
field theory); the conclusion is the requested local non-vanishing.

`LocalH2Input` is not needed for the mathematical content of the statement (which is
`sha2Vanishing_of_rankInput`); it is displayed here because it is the input the consumer's
development has to hand, and the deliverable's requested shape.  See
`Submission/Work/HassePrinciple/Deliverable.lean` for the headlined version of this theorem. -/
theorem exists_loc_ne_zero_of_localH2Input (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ)
    (κ' := κ') p) (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') h H hH hκ hx

/-- **The Hasse principle in the vocabulary of `LocalH2Input`**, in the form that also produces
the non-zero class: a caller who supplies the local Brauer input obtains, for every closed subgroup
`H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, a non-zero class of `H²(H, Z/p)` with a non-zero local
component at some place of `K'` over a finite prime of `K`. -/
theorem exists_nonzero_class_with_loc_ne_zero
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    ∃ (x : H2Profinite p H) (A : OverFinitePrime K K'),
      x ≠ 0 ∧ H2Profinite.loc p H x A ≠ 0 := by
  obtain ⟨x, hx⟩ := hLoc H hH hκ
  obtain ⟨A, hA⟩ := exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') h H hH hκ hx
  exact ⟨x, A, hx, hA⟩

section Consumer

/-- **The consumer's interface in a single hypothesis.**  The two inputs that a caller in the
Neukirch–Uchida development supplies to invoke the Hasse principle in its local form: their own
local Brauer input `NK.BrauerHasse.LocalH2Input` and the chapter's single arithmetic input
`NK.HassePrinciple.RankInput` (Neukirch's (9.2.1) plus the local computations of local class
field theory).  No Hasse-principle statement occurs in either field. -/
structure ConsumerHypotheses (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the local Brauer input of local class field theory (`Br(κ)[p] ≅ Z/p`). -/
  localBrauer : LocalH2Input p K K' κ κ'
  /-- the chapter's input: Neukirch's rank count (`NK.HassePrinciple.RankInput`). -/
  rank : RankInput p K K' κ κ'

/-- **The Hasse principle, with the consumer's hypotheses supplied as one bundle.**  Under
`NK.HassePrinciple.ConsumerHypotheses p K K' κ κ'` every non-zero class of `H²(H, Z/p)`, for
`H ≤ Gal(K'/K)` closed and isomorphic to `Gal(κ'/κ)`, has a non-zero local component at some place
of `K'` over a finite prime of `K`. -/
theorem exists_loc_ne_zero_of_consumerHypotheses
    (h : ConsumerHypotheses (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_localH2Input (K := K) (K' := K') (κ := κ) (κ' := κ')
    h.localBrauer h.rank H hH hκ hx

end Consumer

/-- **Neukirch's characterisation of decomposition groups**, with the Hasse-principle hypothesis
discharged by `NK.HassePrinciple.sha2Vanishing_of_rankInput`: a closed, self-normalising subgroup
`H ≤ Gal(K'/K)` isomorphic to the absolute Galois group of a `p`-adic field is the decomposition
group of a place of `K'` over a finite prime of `K`.

The local Brauer input, the chapter's input and the local finishing step
(`NK.BrauerHasse.LocalDecompositionCriterion`, the endgame of the sibling chapter
`NK.LocalDecomposition`) are the hypotheses; the Hasse principle is discharged. -/
theorem exists_decompositionGroup_of_localGalois
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  NK.BrauerHasse.exists_decompositionGroup_of_localGalois (K := K) (K' := K')
    (κ := κ) (κ' := κ') p h.hp H hH hN hκ hLoc
    (sha2Vanishing_of_rankInput h) hStep

/-! ## The legacy level-wise route (do not build on this) -/

/-- **Superseded.**  The Hasse principle from the legacy input `NK.HassePrinciple.Sha2Input`
(whose second field is the *fine* level-wise Hasse principle, a form the classical theory does not
produce; README §12.2, §13.7(iv)).  Kept for the record only. -/
theorem exists_loc_ne_zero_of_sha2Input (p : ℕ)
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Vanishing_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p h) H hH hκ hx

/-- **Superseded.**  See `NK.HassePrinciple.exists_loc_ne_zero_of_sha2Input`. -/
theorem exists_loc_ne_zero_of_localH2Input_of_sha2Input (p : ℕ)
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p h H hH hκ hx

/-- **Superseded.**  Neukirch's criterion from the legacy level-wise input. -/
theorem exists_decompositionGroup_of_localGalois_of_sha2Input (p : ℕ)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : LocalDecompositionCriterion (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  NK.BrauerHasse.exists_decompositionGroup_of_localGalois (K := K) (K' := K')
    (κ := κ) (κ' := κ') p h.hp H hH hN hκ hLoc
    (sha2Vanishing_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p h) hStep

/-- **Superseded.**  The Hasse principle from the arithmetic form of the legacy input. -/
theorem exists_loc_ne_zero_of_arithInput (p : ℕ)
    (h : Sha2InputArith (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Input_of_arithInput (K := K) (K' := K') (κ := κ) (κ' := κ') p h) H hH hκ hx

end NK.HassePrinciple
