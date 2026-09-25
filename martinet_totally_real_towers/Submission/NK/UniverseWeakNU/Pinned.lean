/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Universe-pinned aliases of the polymorphic `Prop`s

The `Prop`s of `Submission/Work/UniverseWeakNU/Defs.lean` are closed definitions carrying a
universe parameter that does *not* occur in their type, so Lean cannot infer it from a bare
occurrence (`IsUchidaModuleDataU 2` leaves the universe a fresh parameter).  A caller who prefers
the universe to be inferred from a `Type u` argument can use the aliases below: for every such
`Prop` there is an `…UAt` version whose first argument is an explicit `Type u` witness that pins the
universe.

For a field `K₁ : Type u` one may therefore write

```lean
(hU : NK.UniverseWeakNU.IsUchidaModuleDataUAt K₁ 2)
(hC : NK.UniverseWeakNU.ChebotarevFrobeniusInputUAt K₁)
```

instead of `IsUchidaModuleDataU.{u} 2`, `ChebotarevFrobeniusInputU.{u}`; the two are
definitionally equal, and the main theorems are restated below in this form.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Main

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-- `ChebotarevFrobeniusInputU.{u}`, pinned at the universe of the witness `w : Type u`. -/
def ChebotarevFrobeniusInputUAt (_w : Type u) : Prop := ChebotarevFrobeniusInputU.{u}

/-- `PrimeCountOrbitInputU.{u}`, pinned at the universe of the witness `w : Type u`. -/
def PrimeCountOrbitInputUAt (_w : Type u) : Prop := PrimeCountOrbitInputU.{u}

/-- `PrimeCountOrbitInputPlaceU.{u}`, pinned at the universe of the witness `w : Type u`. -/
def PrimeCountOrbitInputPlaceUAt (_w : Type u) : Prop := PrimeCountOrbitInputPlaceU.{u}

/-- `PerlisGassmannInputU.{u}`, pinned at the universe of the witness `w : Type u`. -/
def PerlisGassmannInputUAt (_w : Type u) : Prop := PerlisGassmannInputU.{u}

/-- `IsUchidaModuleDataU.{u}`, pinned at the universe of the witness `w : Type u`. -/
def IsUchidaModuleDataUAt (_w : Type u) (ℓ : ℕ) : Prop := IsUchidaModuleDataU.{u} ℓ

/-- `IsUchidaModuleDataKummerU.{u}`, pinned at the universe of the witness `w : Type u`. -/
def IsUchidaModuleDataKummerUAt (_w : Type u) (ℓ : ℕ) : Prop := IsUchidaModuleDataKummerU.{u} ℓ

/-- `IsUchidaModuleDataArithU.{u}`, pinned at the universe of the witness `w : Type u`. -/
def IsUchidaModuleDataArithUAt (_w : Type u) (ℓ : ℕ) : Prop := IsUchidaModuleDataArithU.{u} ℓ

/-! ## The main derivations, in pinned form

The hypotheses are the `…UAt` aliases, which are definitionally the corresponding `…U.{u}`. -/

/-- `perlisGassmannInputU` with the universe pinned by a `Type u` witness. -/
theorem perlisGassmannInputUAt (w : Type u) (hC : ChebotarevFrobeniusInputUAt w) :
    PerlisGassmannInputUAt w :=
  perlisGassmannInputU hC

/-- `primeCountOrbitInputU` with the universe pinned by a `Type u` witness. -/
theorem primeCountOrbitInputUAt (w : Type u) : PrimeCountOrbitInputUAt w := primeCountOrbitInputU

/-- `isWeakUchidaU` with the universe pinned by a `Type u` witness. -/
theorem isWeakUchidaUAt (w : Type u) {ℓ : ℕ} (hU : IsUchidaModuleDataUAt w 2)
    (hP : PerlisGassmannInputUAt w) : IsWeakUchidaU.{u} ℓ :=
  isWeakUchidaU hU hP

/-- **The end goal**, with the universe pinned by the witness `K₁ : Type u`. -/
theorem levelIsoInput_of_chebotarevUAt {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataUAt K₁ 2) (hC : ChebotarevFrobeniusInputUAt K₁)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarevU hU hC ϕ hϕ

end

end NK.UniverseWeakNU
