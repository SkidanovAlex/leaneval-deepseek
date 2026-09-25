/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The structure theorem in the vocabulary of the places of a number field

This file states the deliverable of `Submission/Work/TameData/` in the place vocabulary of
`Submission/Work/FrobeniusBridge/Basic.lean`: for a number field `K`, a place `A` of a separable
closure `K'` over `K` (a `FinitePlaceOf K K'`) and the prime `𝔭` of `K` below it, the local field
is `NK.FrobeniusBridge.localField A = K_𝔭` and its separable closure is
`NK.FrobeniusBridge.localClosure A`; the chapter provides

  `TameData p q (localField A) (localClosure A)`  with `q = #(𝓞 K ⧸ 𝔭)`

from the three reduced inputs at the completion `K_𝔭`.

**Import note.**  This module is deliberately *not* imported by `NK.TameData.All`: it depends on
`Submission.NK.FrobeniusBridge.Basic`, and importing it back from `NK.FrobeniusBridge` would
create a cycle.  Consumers of the place vocabulary import it explicitly
(`import Submission.NK.TameData.Places`).
-/
import Submission.NK.TameData.Adic
import Submission.NK.FrobeniusBridge.Basic

open scoped Classical
open NK.LocalTame

set_option linter.unusedSectionVars false

namespace NK.TameData

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The prime of `K` below the place `A`. -/
noncomputable abbrev primeBelow (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  Submission.NeukirchUchida.primeOf A.1 A.2

/-- **The structure theorem at a place of a number field**, in the vocabulary of
`Submission/Work/FrobeniusBridge/Basic.lean`: for the local field `K_𝔭 = localField A` of a place
`A` and its separable closure `localClosure A`,

  `TameData p (residueCard K (primeBelow A)) (localField A) (localClosure A)`,

where `residueCard K (primeBelow A) = #(𝓞 K ⧸ primeBelow A)` is the residue field cardinality. -/
theorem tameData_localField (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p : ℕ}
    (hT : NK.LocalStructure.TameCore p K (primeBelow A) (NK.FrobeniusBridge.localClosure A))
    (hA : TameAbelianisationInput p (NK.LocalStructure.residueCard K (primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hF : NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K (primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) :
    TameData p (NK.LocalStructure.residueCard K (primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) :=
  tameData_adicCompletion (K := K) (primeBelow A) hT hA hF

/-- **The structure theorem at every place of `K'`.**  If the three reduced inputs are available
at the completion of `K` at the prime below every place of `K'`, then
`NK.LocalTame.TameData` holds at every place.  This is the `NK.LocalTame.TameData` part of
`NK.FrobeniusBridge.TameDataAtPlaces`, in the same shape (an existential over `p` and `q`); the
other part of that definition, `NK.LocalTame.Zl2ResidueChar`, is not part of this chapter. -/
theorem exists_tameData_at_places
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', ∃ p : ℕ,
      NK.LocalStructure.TameCore p K (primeBelow A) (NK.FrobeniusBridge.localClosure A) ∧
      TameAbelianisationInput p (NK.LocalStructure.residueCard K (primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) ∧
      NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K (primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) :
    ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', ∃ p q : ℕ,
      TameData p q (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) := by
  intro A
  obtain ⟨p, hT, hA, hF⟩ := h A
  exact ⟨p, _, tameData_localField A hT hA hF⟩

/-- **The local structure inputs at every place, in the shape of
`NK.FrobeniusBridge.TameDataAtPlaces`.**

If for every place `A` of `K'` the three reduced inputs of this chapter *and* Shimizu's
`ℤ_ℓ²`-criterion `NK.LocalTame.Zl2ResidueChar` (which is not part of this chapter) are available
at the completion `K_𝔭` below `A`, then `NK.LocalTame.TameData` and
`NK.LocalTame.Zl2ResidueChar` hold at every place — which is exactly the hypothesis
`NK.FrobeniusBridge.TameDataAtPlaces` of the Frobenius bridge. -/
theorem tameDataAtPlaces_of_inputs
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', ∃ p : ℕ,
      NK.LocalStructure.TameCore p K (primeBelow A) (NK.FrobeniusBridge.localClosure A) ∧
      TameAbelianisationInput p (NK.LocalStructure.residueCard K (primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) ∧
      NK.LocalStructure.TameFrobeniusCore p (NK.LocalStructure.residueCard K (primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) ∧
      NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
        (NK.FrobeniusBridge.localClosure A)) :
    ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', ∃ p q : ℕ,
      NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
        (NK.FrobeniusBridge.localClosure A) ∧
      NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
        (NK.FrobeniusBridge.localClosure A) := by
  intro A
  obtain ⟨p, hT, hA, hF, hZ⟩ := h A
  exact ⟨p, _, tameData_localField A hT hA hF, hZ⟩

end NK.TameData
