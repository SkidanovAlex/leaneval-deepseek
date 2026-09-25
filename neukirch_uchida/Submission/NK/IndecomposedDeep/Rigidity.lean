/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The degree rigidity of `p`-adic fields is a *theorem*, and the corrected reconstruction without it

`NK.IndecomposedDeep.localDegreeRigidity` (`localDegreeRigidity.lean`) proves the degree-rigidity
statement isolated in `Corrected.lean`: a finite extension `M` of the `p`-adic field
`α = 𝔮.adicCompletion L` which is isomorphic to `α` *as a ring* is trivial (`M = ⊥`), i.e.

```
NK.IndecomposedDeep.LocalDegreeRigidity
```

holds.  This module turns the input into a theorem (`localDegreeRigidity_holds`) and records the
consequences: the corrected local maximality of decomposition groups and the corrected local
reconstruction now depend only on

* `NK.LocalStructure.LocalNUExistence` — Neukirch's local reconstruction (the workspace's single
  residual local input),
* Serre's closedness statement (`LocalSubgroupClosed`, and its local-field instance
  `LocalSubgroupClosedAtLocalField`),
* the on-disk `NK.LocalDecomposition.LocalInjectionFiniteIndex` (Ivanov's `lm:locfinindex`, for
  Neukirch's Korollar 1).
-/

import Submission.NK.IndecomposedDeep.CorrectedForm
import Submission.NK.IndecomposedDeep.localDegreeRigidity

open IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist

/-- **The degree-rigidity of `p`-adic fields holds.**  This is the input `LocalDegreeRigidity` of
`Corrected.lean`, now a theorem (`NK.IndecomposedDeep.localDegreeRigidity`). -/
theorem localDegreeRigidity_holds : LocalDegreeRigidity.{u} :=
  fun L _ _ 𝔮 M _ h => localDegreeRigidity L 𝔮 M h

/-! ## The corrected local maximality, unconditionally -/

/-- **Neukirch's maximality in the local picture, with no residual local input beyond
`NK.LocalStructure.LocalNUExistence`.**  A closed finite-index subgroup `H` of the absolute Galois
group of a `p`-adic field which is isomorphic to the whole group is the whole group. -/
theorem localFinishingStep_local_of_localNU (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L))
    (hHcl : IsClosed (H : Set Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L)))
    (hHfin : H.FiniteIndex)
    (hκ : Nonempty (H ≃* Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L))) :
    H = ⊤ :=
  localFinishingStep_local (L := L) (𝔮 := 𝔮) (H := H) hNU localDegreeRigidity_holds hHcl hHfin hκ

/-- **The corrected finishing step `LocalFinishingStepAtLocalField`, unconditionally** (modulo
Neukirch's local reconstruction and Serre's closedness statement). -/
theorem localFinishingStepAtLocalField_of_localNU
    {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (hclosed : LocalSubgroupClosedAtLocalField.{u}) :
    LocalFinishingStepAtLocalField p K K' κ κ' :=
  localFinishingStepAtLocalField_of_inputs (K := K) (K' := K') (κ := κ) (κ' := κ') hNU
    localDegreeRigidity_holds hclosed

/-! ## The corrected local reconstruction, unconditionally -/

/-- **The corrected local reconstruction `LocalReconstructionAtLocalField`, unconditionally**
(modulo Neukirch's local reconstruction, Serre's closedness statement in two instances, and the
on-disk finiteness input `NK.LocalDecomposition.LocalInjectionFiniteIndex`).

This is the honest replacement for `NK.Indecomposed.LocalReconstruction`: its finishing step
carries the local field of the place in the hypothesis, as the classical sources state it (see
`README.md` §7). -/
theorem localReconstructionAtLocalField_of_localNU
    {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (hclosed : LocalSubgroupClosed.{u} κ κ')
    (hclosedLocal : LocalSubgroupClosedAtLocalField.{u})
    (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ') :
    LocalReconstructionAtLocalField p K K' κ κ' :=
  localReconstructionAtLocalField_of_inputs (K := K) (K' := K') (κ := κ) (κ' := κ') hNU
    localDegreeRigidity_holds hclosed hclosedLocal hfin

/-- **The corrected local reconstruction implies the formalised one, given the labelling
compatibility** (the audit statement of `README.md` §7, with the degree rigidity discharged). -/
theorem localReconstruction_of_localNU
    {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (hclosed : LocalSubgroupClosed.{u} κ κ')
    (hclosedLocal : LocalSubgroupClosedAtLocalField.{u})
    (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ')
    (hcompat : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
      Subgroup.normalizer H = H → Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        (A : ValuationSubring K'),
        A.comap (algebraMap K K')
          = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 →
        H ≤ stabSubgroup A → 0 < H.relIndex (stabSubgroup A) →
        Nonempty (H ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K))) :
    NK.Indecomposed.LocalReconstruction p K K' κ κ' :=
  localReconstruction_of_atLocalField (K := K) (K' := K') (κ := κ) (κ' := κ')
    (localReconstructionAtLocalField_of_localNU (K := K) (K' := K') (κ := κ) (κ' := κ') hNU
      hclosed hclosedLocal hfin) hcompat

end NK.IndecomposedDeep
