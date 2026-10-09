/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle is Neukirch's local characterisation of the decomposition groups

Umbrella development: `Submission/Work/HassePrinciple/` (README §17).

The target of the chapter, `NK.BrauerHasse.Sha2Vanishing p K K' κ κ'`, asks for the *vanishing of
the limiting `Ш²`*: a class of `H²(U, Z/p)`, for `U ≤ Gal(K'/K)` a closed subgroup isomorphic to
`Gal(κ'/κ)` (`κ` a `p`-adic field), whose localisation at every place of `K'` over a finite prime of
`K` vanishes, is zero.

This module records, as a *proved equivalence*, that this is not an auxiliary Hasse-principle
statement at all: modulo the local Brauer input `NK.BrauerHasse.LocalH2Input` and the local
finishing step `NK.BrauerHasse.LocalDecompositionCriterion` (both classical inputs of the
Neukirch–Uchida development, and both recorded as such by the sibling chapters
`NK.LocalDecomposition`, `NK.BrauerTwist`), it is **equivalent** to

`NK.HassePrinciple.LocalCharacterisation p K K' κ κ'`:

*every closed subgroup `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` is contained in the decomposition
group of a place of `K'` over a finite prime of `K`.*

That statement is Neukirch, *Kennzeichnung der `p`-adischen und der endlich algebraischen
Zahlkörper*, Invent. Math. **6** (1969), Theorem 1 — the "if" direction of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, (12.1.9), i.e. **the core theorem of the paper whose Hasse-principle
input this chapter was asked to discharge**.  The equivalence is the formal content of §14.6 and of
the headline of the README: the deliverable is not a corollary of the Hasse norm theorem or of the
two inequalities, and the licensed cyclic input cannot produce it.

## The two directions

* `NK.HassePrinciple.sha2Vanishing_of_localCharacterisation` — the easy direction, **unconditional**
  (`NK.HassePrinciple.sha2Vanishing_of_inert`): if every labelled closed `U` is contained in a
  decomposition group, then the localisation at that place is injective
  (`NK.HassePrinciple.loc_injective_of_le_stabSubgroup`), so the Hasse principle follows.  This is
  Neukirch's "the prime is indecomposed" step; everything local is proved.
* `NK.HassePrinciple.localCharacterisation_of_sha2Vanishing` — the converse: from the Hasse
  principle and the local Brauer input, a non-zero class of `H²(U, Z/p)` has a non-zero local
  component at some place (`NK.BrauerHasse.exists_loc_ne_zero`), and the local finishing step
  produces a place whose decomposition group is `U`.  It carries the self-normalising hypothesis of
  `NK.BrauerHasse.LocalDecompositionCriterion`, which is the hypothesis under which the classical
  criterion is stated.

The packaged form is `NK.HassePrinciple.sha2Vanishing_iff_localCharacterisation`, and the
specialisations to the chapter's input structures are
`NK.HassePrinciple.localCharacterisation_of_rankInput` and
`NK.HassePrinciple.localCharacterisation_of_indexInput`.
-/

import Submission.NK.HassePrinciple.Inert
import Submission.NK.HassePrinciple.RankInput
import Submission.NK.HassePrinciple.IndexInput
import Submission.NK.BrauerHasse.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Neukirch's local characterisation of the decomposition groups, in the `κ`-labelled form in
which the Hasse principle consumes it.**  Every closed subgroup `U ≤ Gal(K'/K)` isomorphic to
`Gal(κ'/κ)` is contained in the decomposition group `stabSubgroup A` of a place `A` of `K'` over a
finite prime of `K`.

This is the hypothesis of `NK.HassePrinciple.sha2Vanishing_of_inert` (and hence, by that theorem,
a sufficient condition for the chapter's target `NK.BrauerHasse.Sha2Vanishing`), and it is the
labelled form of the conclusion of Neukirch, *Kennzeichnung der `p`-adischen und der endlich
algebraischen Zahlkörper*, Invent. Math. **6** (1969), Theorem 1 = Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, (12.1.9) ("if" direction).  By
`NK.HassePrinciple.sha2Vanishing_iff_localCharacterisation` it is *equivalent* to the chapter's
target, modulo the local Brauer input and the local finishing step. -/
def LocalCharacterisation (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Nonempty (U ≃* Gal(κ'/κ)) →
    ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1

/-- **The self-normalising hypothesis on the labelled subgroups.**  Every closed subgroup
`U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` is self-normalising.

This is the hypothesis under which Neukirch's criterion is classically stated (`a decomposition
group is self-normalising`, CoNF (12.1.4); `NK.LocalDecomposition.normalizer_stabSubgroup_eq`,
and `NK.BrauerHasse.LocalDecompositionCriterion` carries `Subgroup.normalizer H = H`), and it is
the only bridge between the *general* form of the local characterisation
(`NK.HassePrinciple.LocalCharacterisation`) and the self-normalising form that the criterion
produces:

`LocalCharacterisationSN + SelfNormalisingLabeled ⟹ LocalCharacterisation`,

which is how `NK.HassePrinciple.sha2Vanishing_of_localDecomposition`
(`Deliverable.lean`) composes the criterion with the chapter's reduction.  For decomposition groups
the hypothesis is a *theorem* (`normalizer_stabSubgroup_eq`); for an arbitrary closed `U` isomorphic
to a local Galois group it is the statement that such a `U` *is* a decomposition group's group,
i.e. it is (a weak form of) Neukirch's conclusion — which is why it is isolated here as a named
hypothesis rather than assumed silently. -/
def SelfNormalisingLabeled (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Nonempty (U ≃* Gal(κ'/κ)) →
    Subgroup.normalizer U = U

/-- **The self-normalising form of Neukirch's local characterisation**: every closed *self-normalising*
subgroup `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` is contained in the decomposition group of a
place over a finite prime of `K`.  This is the form that Neukirch's criterion
(`NK.BrauerHasse.LocalDecompositionCriterion`) produces, and
`NK.HassePrinciple.SelfNormalisingLabeled` turns it into the general
`NK.HassePrinciple.LocalCharacterisation`. -/
def LocalCharacterisationSN (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → Subgroup.normalizer U = U →
    Nonempty (U ≃* Gal(κ'/κ)) → ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1

/-- `LocalCharacterisation` implies its self-normalising form (trivially). -/
theorem localCharacterisationSN_of_localCharacterisation (p : ℕ)
    (h : LocalCharacterisation (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    LocalCharacterisationSN (K := K) (K' := K') (κ := κ) (κ' := κ') p :=
  fun U hU _ hκ => h U hU hκ

/-- **The general local characterisation from the self-normalising one.**  If every closed
self-normalising `U ≅ Gal(κ'/κ)` lies in a decomposition group and every closed `U ≅ Gal(κ'/κ)` is
self-normalising, then every closed `U ≅ Gal(κ'/κ)` lies in a decomposition group. -/
theorem localCharacterisation_of_selfNormalisingLabeled (p : ℕ)
    (h : LocalCharacterisationSN (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hSN : SelfNormalisingLabeled (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    LocalCharacterisation (K := K) (K' := K') (κ := κ) (κ' := κ') p :=
  fun U hU hκ => h U hU (hSN U hU hκ) hκ

/-- **The Hasse principle from Neukirch's local characterisation** (unconditional).  This is
`NK.HassePrinciple.sha2Vanishing_of_inert` restated: the only arithmetic input is the existence of
a place whose decomposition group contains the subgroup under consideration, and the localisation at
such a place is injective by `NK.HassePrinciple.loc_injective_of_le_stabSubgroup`. -/
theorem sha2Vanishing_of_localCharacterisation (p : ℕ)
    (h : LocalCharacterisation (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_inert p h

/-- **Neukirch's local characterisation from the Hasse principle.**  From the local Brauer input
(`H²(U, Z/p) ≠ 0` for the labelled `U`), the Hasse principle and the local finishing step of the
Neukirch argument, a closed self-normalising subgroup `U ≅ Gal(κ'/κ)` is contained in the
decomposition group of a place over a finite prime of `K`.

Proof: pick `0 ≠ x ∈ H²(U, Z/p)`; by the Hasse principle `x` has a non-zero local component at some
place `A` (`NK.BrauerHasse.exists_loc_ne_zero`); the local finishing step
`NK.BrauerHasse.LocalDecompositionCriterion` turns that into a place `A'` with `D_{A'} = U`. -/
theorem localCharacterisation_of_sha2Vanishing (p : ℕ)
    (hLoc : LocalH2Input p K K' κ κ') (hStep : LocalDecompositionCriterion p K K' κ κ')
    (h : Sha2Vanishing (K := K) (K' := K') p κ κ')
    (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (hN : Subgroup.normalizer U = U) (hκ : Nonempty (U ≃* Gal(κ'/κ))) :
    ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1 := by
  obtain ⟨x, hx⟩ := hLoc U hU hκ
  obtain ⟨A, hA⟩ := NK.BrauerHasse.exists_loc_ne_zero (K := K) (K' := K') p h U hU hκ hx
  obtain ⟨A', hA'ne, hA'stab⟩ := hStep U hU hN hκ A x hA
  exact ⟨⟨A', hA'ne⟩, le_of_eq hA'stab.symm⟩

/-- **The Hasse principle *is* Neukirch's local characterisation** (modulo the local Brauer input and
the local finishing step).  Under the classical hypothesis that the closed subgroups isomorphic to
`Gal(κ'/κ)` are self-normalising — which is the hypothesis of Neukirch's criterion and the shape in
which the development consumes it — the chapter's target `NK.BrauerHasse.Sha2Vanishing` is
*equivalent* to the statement that every such subgroup is contained in the decomposition group of a
place over a finite prime of `K`.

This is the formal counterpart of README §14.6 and §17: the target is not a consequence of the
licensed cyclic input (the Hasse norm theorem / the reciprocity isomorphism), but the core theorem of
Neukirch (Invent. Math. **6** (1969), Theorem 1). -/
theorem sha2Vanishing_iff_localCharacterisation (p : ℕ)
    (hLoc : LocalH2Input p K K' κ κ') (hStep : LocalDecompositionCriterion p K K' κ κ')
    (hSN : ∀ U : Subgroup Gal(K'/K), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → Subgroup.normalizer U = U) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' ↔
      LocalCharacterisation (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  constructor
  · intro h U hU hκ
    exact localCharacterisation_of_sha2Vanishing p hLoc hStep h U hU (hSN U hU hκ) hκ
  · exact sha2Vanishing_of_localCharacterisation p

/-! ## The characterisation from the chapter's input structures -/

/-- **Neukirch's local characterisation from the chapter's rank input.**  The composition of
`NK.HassePrinciple.sha2Vanishing_of_rankInput` with
`NK.HassePrinciple.localCharacterisation_of_sha2Vanishing`: the rank input (Neukirch's
surjectivity at a place, plus the local computations) yields the decomposition groups. -/
theorem localCharacterisation_of_rankInput (p : ℕ)
    (hin : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hLoc : LocalH2Input p K K' κ κ') (hStep : LocalDecompositionCriterion p K K' κ κ')
    (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (hN : Subgroup.normalizer U = U) (hκ : Nonempty (U ≃* Gal(κ'/κ))) :
    ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1 :=
  localCharacterisation_of_sha2Vanishing p hLoc hStep (sha2Vanishing_of_rankInput hin)
    U hU hN hκ

/-- **Neukirch's local characterisation from the chapter's local-degree input**
(`NK.HassePrinciple.IndexInput`): a place whose local degree inside every labelled closed `U` is
prime to `p` at every finite level gives the decomposition groups, with no cohomological hypothesis
other than the local Brauer input and the local finishing step. -/
theorem localCharacterisation_of_indexInput (p : ℕ)
    (hin : IndexInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hLoc : LocalH2Input p K K' κ κ') (hStep : LocalDecompositionCriterion p K K' κ κ')
    (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (hN : Subgroup.normalizer U = U) (hκ : Nonempty (U ≃* Gal(κ'/κ))) :
    ∃ A : OverFinitePrime K K', U ≤ stabSubgroup A.1 :=
  localCharacterisation_of_sha2Vanishing p hLoc hStep (sha2Vanishing_of_indexInput hin)
    U hU hN hκ

/-- **The Hasse principle from the self-normalising local characterisation and the
self-normalising hypothesis** (this is the form in which the consumer's own chapter
`NK.LocalDecomposition` delivers the characterisation; see
`NK.HassePrinciple.sha2Vanishing_of_localDecomposition` in `Deliverable.lean`). -/
theorem sha2Vanishing_of_localCharacterisationSN (p : ℕ)
    (h : LocalCharacterisationSN (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hSN : SelfNormalisingLabeled (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_localCharacterisation (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (localCharacterisation_of_selfNormalisingLabeled (K := K) (K' := K') (κ := κ) (κ' := κ') p
      h hSN)

end NK.HassePrinciple
