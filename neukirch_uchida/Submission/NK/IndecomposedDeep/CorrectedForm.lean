/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The corrected local reconstruction: Neukirch's Theorem 1 with the local field of the place

`Corrected.lean` proves the *local* maximality statement (`localFinishingStep_local`) and
`indexOne_of_localGaloisField.lean` transports it to the global picture along the local
correspondence.  This module packages the result as the honest replacement for
`NK.Indecomposed.LocalReconstruction`,

```
NK.IndecomposedDeep.LocalReconstructionAtLocalField p K K' κ κ'
```

whose finishing step carries the *correct* hypothesis — the subgroup `H ≤ D_A` must be isomorphic to
the absolute Galois group of the **local field of the place `A`**, rather than to `Gal(κ'/κ)` for an
arbitrary `p`-adic field `κ` (see `README.md` §7).  It also records, as a proved statement, that the
two forms differ by exactly that labelling compatibility
(`localReconstruction_of_atLocalField`), so a consumer can see precisely what has to be verified to
use the formalised structure `NK.Indecomposed.LocalReconstruction`.

The inputs are Neukirch's local reconstruction `NK.LocalStructure.LocalNUExistence` (reduced by
`Submission/Work/Ramification/` to the Kennzeichnung), the degree rigidity of `p`-adic fields
`NK.IndecomposedDeep.LocalDegreeRigidity`, and Serre's closedness statement
(`NK.IndecomposedDeep.LocalSubgroupClosed`, in the two instances needed).
-/

import Submission.NK.IndecomposedDeep.Corrected
import Submission.NK.IndecomposedDeep.indexOne_of_localGaloisField

open IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## The corrected finishing step -/

/-- **Serre's closedness statement for the labellings at the local fields.**

Every subgroup of the absolute Galois group `Gal(L'/L_𝔮)` of a `p`-adic field which is isomorphic to
`Gal(L_𝔮'/L_𝔮)` — the labelling at the local field of the place — is closed.  This is the instance of
`NK.IndecomposedDeep.LocalSubgroupClosed` which the transport of the finishing step along the local
correspondence needs (there the subgroup arises as the image of a closed subgroup under an abstract
`MulEquiv`, so closedness does not descend and has to be supplied here). -/
def LocalSubgroupClosedAtLocalField : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
    Nonempty (H ≃* Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L)) →
      IsClosed (H : Set Gal(L'/𝔮.adicCompletion L))

/-- **The finishing step with the local field of the place in the hypothesis.**

For a closed self-normalising `H ≤ Gal(K'/K)` which is contained in the decomposition group `D_A` of
a place `A` over the finite prime `𝔭`, has finite relative index in `D_A`, and is isomorphic to the
absolute Galois group of the *local field* `𝔭.adicCompletion K` of that place, there is a place over
a finite prime whose decomposition group is `H` (namely `A` itself).

This is Neukirch's maximality statement (Invent. Math. **6** (1969); CoNF (12.1.9)–(12.1.10)) in its
classical form; cf. `NK.LocalStructure.LocalFinishingStep`, which asks the same with an arbitrary
`p`-adic field `κ` in place of the local field of `A` (see `README.md` §7). -/
def LocalFinishingStepAtLocalField (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Subgroup.normalizer H = H →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (A : ValuationSubring K'),
      A.comap (algebraMap K K')
        = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 →
      H ≤ stabSubgroup A → 0 < H.relIndex (stabSubgroup A) →
      Nonempty (H ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)) →
      ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧ stabSubgroup A' = H

/-- **The corrected finishing step is *proved*** from Neukirch's local reconstruction, the degree
rigidity of `p`-adic fields and Serre's closedness statement: this is
`NK.IndecomposedDeep.indexOne_of_localGaloisField`, restated in the shape above. -/
theorem localFinishingStepAtLocalField_of_inputs
    (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (hrig : LocalDegreeRigidity.{u})
    (hclosed : LocalSubgroupClosedAtLocalField.{u}) :
    LocalFinishingStepAtLocalField p K K' κ κ' := by
  intro H hHcl hN hκ 𝔭 A h𝔭 hHle hrel hloc
  refine ⟨A, ?_, ?_⟩
  · rw [h𝔭]
    exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭
  · exact indexOne_of_localGaloisField (K := K) (K' := K') hNU hrig hclosed 𝔭 A h𝔭 H hHcl hHle
      hrel hloc

/-! ## The corrected local reconstruction -/

/-- **Neukirch's local reconstruction, with the finishing step in its classical form.** -/
structure LocalReconstructionAtLocalField (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- Neukirch's Korollar 1 (Ivanov's `lm:locfinindex`) -/
  korollar1 : NK.Indecomposed.LocalKorollar1.{u} κ κ'
  /-- the finishing step, with the local field of the place in the hypothesis -/
  finishingStep : LocalFinishingStepAtLocalField p K K' κ κ'

/-- **The corrected local reconstruction, *proved*** from the on-disk finiteness input
`NK.LocalDecomposition.LocalInjectionFiniteIndex` (for Korollar 1), Neukirch's local reconstruction
`NK.LocalStructure.LocalNUExistence` and the degree rigidity of `p`-adic fields (for the finishing
step), and Serre's closedness statement (in the two instances needed). -/
theorem localReconstructionAtLocalField_of_inputs
    (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (hrig : LocalDegreeRigidity.{u})
    (hclosed : LocalSubgroupClosed.{u} κ κ')
    (hclosedLocal : LocalSubgroupClosedAtLocalField.{u})
    (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ') :
    LocalReconstructionAtLocalField p K K' κ κ' where
  korollar1 := localKorollar1_of_inputs (κ := κ) (κ' := κ') hclosed hfin
  finishingStep := localFinishingStepAtLocalField_of_inputs (K := K) (K' := K') (κ := κ)
    (κ' := κ') hNU hrig hclosedLocal

/-- **The two reconstructions differ by exactly the labelling compatibility.**

If the corrected reconstruction holds and, in addition, every abstract labelling
`H ≅ Gal(κ'/κ)` (for a closed self-normalising `H ≤ D_A` of finite relative index) is *also* a
labelling at the local field of the place, then `NK.Indecomposed.LocalReconstruction` holds.  This
is the precise form of the audit finding of `README.md` §7: the formalised structure and the
classical one differ by the hypothesis `hcompat` below. -/
theorem localReconstruction_of_atLocalField
    (h : LocalReconstructionAtLocalField p K K' κ κ')
    (hcompat : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
      Subgroup.normalizer H = H → Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        (A : ValuationSubring K'),
        A.comap (algebraMap K K')
          = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 →
        H ≤ stabSubgroup A → 0 < H.relIndex (stabSubgroup A) →
        Nonempty (H ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K))) :
    NK.Indecomposed.LocalReconstruction p K K' κ κ' where
  korollar1 := h.korollar1
  finishingStep := fun H hHcl hN hκ A hA hHle hrel => by
    obtain ⟨𝔭, h𝔭⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K') A hA
    exact h.finishingStep H hHcl hN hκ 𝔭 A h𝔭 hHle hrel (hcompat H hHcl hN hκ 𝔭 A h𝔭 hHle hrel)

end NK.IndecomposedDeep
