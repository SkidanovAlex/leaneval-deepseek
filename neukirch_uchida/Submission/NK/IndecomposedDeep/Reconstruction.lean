/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Block (i), part (C): instantiating `NK.Indecomposed.LocalReconstruction`

The structure `NK.Indecomposed.LocalReconstruction p K K' κ κ'` has two fields:

* `korollar1 : NK.Indecomposed.LocalKorollar1 κ κ'` — Neukirch's Korollar 1 in the form consumed by
  the criterion, *proved* in `Korollar1.lean` from the closed-subgroup form
  `NK.LocalDecomposition.LocalInjectionFiniteIndex` (Ivanov's `lm:locfinindex`) and the closedness
  input `NK.IndecomposedDeep.LocalSubgroupClosed`;
* `finishingStep : NK.LocalStructure.LocalFinishingStep p K K' κ κ'` — Neukirch's Theorem 1, the
  maximality of decomposition groups.  Here the on-disk input
  `NK.LocalDecomposition.IndexOneOfSelfNormalizing` is used: the on-disk equivalence
  `NK.LocalDecomposition.localFinishingStep_iff_indexOne` identifies the requester's existential
  form (a place `A'` with `D_{A'} = H`) with the index-one form, and
  `NK.LocalDecomposition.localFinishingStep_of_indexOne` converts.

**Warning (audited in `README.md` §6 and `Corrected.lean`).**  `IndexOneOfSelfNormalizing` — and with
it the `finishingStep` field — is the classical statement only if the labelling `H ≅ Gal(κ'/κ)` is
the *geometric* one: Neukirch's theorem applies to `H ⊆ D_A` when `κ` is (isomorphic to) the local
field `K_𝔭` at the prime below `A`, which is exactly how the endgame instantiates it (the
isomorphism is produced by the local correspondence
`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`, see
`Submission/Work/BrauerTwist/Preserves.lean`).  For an *arbitrary* p-adic field `κ` with
`H ≅ Gal(κ'/κ)` and `[D_A : H] > 1` the statement is not the classical one and is not enough to
force `H = D_A`; the corrected statement, and the exact place where the extra hypothesis is needed,
are in `Corrected.lean`.  The present module therefore proves the structure *from the on-disk input
as stated*; the audit tells the caller exactly what has to be verified to instantiate it.
-/

import Submission.NK.IndecomposedDeep.Korollar1

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The finishing step from the index-one (maximality) input**: the on-disk reduction
`NK.LocalDecomposition.localFinishingStep_of_indexOne`, re-exported so that the chapter's caller
sees the finishing step of `NK.Indecomposed.LocalReconstruction` as a *consequence* of the
on-disk named input `NK.LocalDecomposition.IndexOneOfSelfNormalizing`. -/
theorem localFinishingStep_of_indexOne
    (h : NK.LocalDecomposition.IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.LocalStructure.LocalFinishingStep p K K' κ κ' :=
  NK.LocalDecomposition.localFinishingStep_of_indexOne (p := p) (K := K) (K' := K')
    (κ := κ) (κ' := κ') h

/-- **`NK.Indecomposed.LocalReconstruction` from the classical input catalogue.**

* `korollar1` is proved from `LocalSubgroupClosed` (Serre's closedness) and
  `NK.LocalDecomposition.LocalInjectionFiniteIndex` (Ivanov's `lm:locfinindex`);
* `finishingStep` is the on-disk input `NK.LocalDecomposition.IndexOneOfSelfNormalizing` through
  `localFinishingStep_of_indexOne`.

The two inputs are *not* redundant: `korollar1` is Neukirch's Korollar 1 (the finiteness of the
relative index `[D_A : H]`), the finishing step is the maximality of decomposition groups among the
closed subgroups isomorphic to absolute Galois groups of `p`-adic fields; by
`NK.LocalDecomposition.indexOne_of_localDecompositionCriterion` the criterion together with the
local Brauer non-vanishing *implies* the finishing step, so the pair is exactly a splitting of the
content of Neukirch's Theorem 1 into a local half and a local-global-arithmetic half. -/
theorem localReconstruction_of_inputs (hclosed : LocalSubgroupClosed.{u} κ κ')
    (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ')
    (hidx : NK.LocalDecomposition.IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.Indecomposed.LocalReconstruction p K K' κ κ' where
  korollar1 := localKorollar1_of_inputs (κ := κ) (κ' := κ') hclosed hfin
  finishingStep := localFinishingStep_of_indexOne hidx

/-- The same theorem with the closedness of the subgroup supplied as a plain function. -/
theorem localReconstruction_of_closed_function
    (hclosed : ∀ (L : Type u) [Field L] [NumberField L]
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
      [IsSepClosure (𝔮.adicCompletion L) L']
      (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
      Nonempty (H ≃* Gal(κ'/κ)) → IsClosed (H : Set Gal(L'/𝔮.adicCompletion L)))
    (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ')
    (hidx : NK.LocalDecomposition.IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.Indecomposed.LocalReconstruction p K K' κ κ' :=
  localReconstruction_of_inputs (κ := κ) (κ' := κ') hclosed hfin hidx

/-- **`korollar1` in the form in which the criterion uses it.**  Given the local reconstruction, a
subgroup `H ≤ D_A` of a decomposition group which is isomorphic to the absolute Galois group of the
`p`-adic field `κ` has positive relative index in `D_A`.  This is the on-disk
`NK.Indecomposed.relIndex_pos_of_localKorollar1`, re-exported. -/
theorem relIndex_pos_of_localReconstruction (hrec : NK.Indecomposed.LocalReconstruction p K K' κ κ')
    (A : ValuationSubring K') (hA : A.comap (algebraMap K K') ≠ ⊤) (H : Subgroup Gal(K'/K))
    (hHle : H ≤ stabSubgroup A) (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    0 < H.relIndex (stabSubgroup A) :=
  NK.Indecomposed.relIndex_pos_of_localKorollar1 (K := K) (K' := K') (κ := κ) (κ' := κ')
    hrec.korollar1 A hA H hHle hκ

end NK.IndecomposedDeep
