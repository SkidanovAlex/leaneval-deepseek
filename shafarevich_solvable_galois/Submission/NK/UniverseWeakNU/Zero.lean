/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `u = 0` instance: the polymorphic chapter is a conservative extension of `NK.WeakNU`

Every `Prop` of `Submission/Work/UniverseWeakNU/Defs.lean` is a copy of a definition of
`Submission/Work/WeakNU/` or `Submission/Work/UchidaKummer/` in which `Type` has been replaced by
`Type u`.  At `u = 0` the two are therefore *definitionally equal*, and the fact is recorded here by
`rfl`-proofs: no statement of the polymorphic chapter is a new axiom, and the universe-0 chain of
`Submission/Work/WeakNU/` is recovered by instantiation (`isWeakUchida`,
`levelIsoInput_of_chebotarev`, and the derivations below).

This is the consistency check requested of the area: the `.{0}` instance of the polymorphic
definitions is the universe-0 chain, on the nose.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.UniverseWeakNU.PrimeOrbitU
import Submission.NK.UniverseWeakNU.Main
import Submission.NK.UniverseWeakNU.ChebotarevU
import Submission.NK.UniverseWeakNU.ChebotarevAssemblyU
import Submission.NK.UniverseWeakNU.ArbitraryUniverses
import Submission.NK.ChebotarevGeneral.Main
import Submission.NK.WeakNU.PrimeOrbit
import Submission.NK.WeakNU.UchidaModuleData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-! ## Definitional equalities of the `Prop`s at `u = 0` -/

theorem chebotarevFrobeniusInputU_zero :
    ChebotarevFrobeniusInputU.{0} = NK.WeakNU.ChebotarevFrobeniusInput := rfl

theorem primeCountOrbitInputU_zero :
    PrimeCountOrbitInputU.{0} = NK.WeakNU.PrimeCountOrbitInput := rfl

theorem primeCountOrbitInputPlaceU_zero :
    PrimeCountOrbitInputPlaceU.{0} = NK.WeakNU.PrimeCountOrbitInputPlace := rfl

theorem perlisGassmannInputU_zero :
    PerlisGassmannInputU.{0} = NK.UchidaKummer.PerlisGassmannInput := rfl

theorem isUchidaModuleDataU_zero (ℓ : ℕ) :
    IsUchidaModuleDataU.{0} ℓ = NK.UchidaKummer.IsUchidaModuleData ℓ := rfl

theorem isUchidaModuleDataKummerU_zero (ℓ : ℕ) :
    IsUchidaModuleDataKummerU.{0} ℓ = NK.WeakNU.IsUchidaModuleDataKummer ℓ := rfl

theorem isUchidaModuleDataArithU_zero (ℓ : ℕ) :
    IsUchidaModuleDataArithU.{0} ℓ = NK.WeakNU.IsUchidaModuleDataArith ℓ := rfl

theorem isWeakUchidaU_zero (ℓ : ℕ) :
    IsWeakUchidaU.{0} ℓ = NK.UchidaKummer.IsWeakUchida ℓ := rfl

theorem isWeakUchidaOfU_zero (ℓ : ℕ) :
    IsWeakUchidaOfU.{0} ℓ = NK.WeakNU.IsWeakUchidaOf ℓ := rfl

theorem hasIsomorphicAbsGaloisU_zero (K₁ K₂ : Type) [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] :
    HasIsomorphicAbsGaloisU.{0} K₁ K₂ = NK.UchidaKummer.HasIsomorphicAbsGalois K₁ K₂ := rfl

/-! ## Definitional equalities of the Čebotarev props at `u = 0` -/

theorem abelianChebotarevDensityU_zero :
    AbelianChebotarevDensityU.{0} = NK.ChebotarevGeneral.AbelianChebotarevDensity := rfl

theorem chebotarevInfiniteU_zero :
    ChebotarevInfiniteU.{0} = NK.ChebotarevGeneral.ChebotarevInfinite := rfl

theorem chebotarevInfiniteU_of_abelianU_zero (h : NK.ChebotarevGeneral.AbelianChebotarevDensity) :
    NK.ChebotarevGeneral.ChebotarevInfinite :=
  chebotarevInfiniteU_of_abelianU h

theorem chebotarevFrobeniusInputU_of_abelianU_zero
    (h : NK.ChebotarevGeneral.AbelianChebotarevDensity) :
    NK.WeakNU.ChebotarevFrobeniusInput :=
  chebotarevFrobeniusInputU_of_abelianU h

/-! ## Definitional equalities of the orbit-counting vocabulary at `u = 0` -/

section OrbitZero

variable {N : Type} [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]

theorem primeCountAboveU_zero (M : IntermediateField ℚ N)
    (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) :
    primeCountAbove M 𝔭 = NK.WeakNU.primeCountAbove M 𝔭 := rfl

theorem primeOrbitCountU_zero (H : Subgroup Gal(N/ℚ))
    (𝔭 : NK.Chebotarev.PrimeIdeal ℚ) :
    primeOrbitCount H 𝔭 = NK.WeakNU.primeOrbitCount H 𝔭 := rfl

end OrbitZero

/-! ## The `.{0}` instance of the derivations

These are the same statements as the corresponding theorems of `Submission/Work/WeakNU/`, obtained
by instantiating the polymorphic chain at `u = 0`.  (The originals remain available; these versions
are the ones the polymorphic API produces.) -/

/-- `perlisGassmannInputU` at `u = 0` is `NK.WeakNU.perlisGassmannInput_of_chebotarev`. -/
theorem perlisGassmannInput_zero (hC : NK.WeakNU.ChebotarevFrobeniusInput) :
    NK.UchidaKummer.PerlisGassmannInput :=
  perlisGassmannInputU hC

/-- `primeCountOrbitInputU` at `u = 0` is `NK.WeakNU.primeCountOrbitInput`. -/
theorem primeCountOrbitInput_zero : NK.WeakNU.PrimeCountOrbitInput :=
  primeCountOrbitInputU

/-- `levelIsoInput_of_chebotarevU` at `u = 0` is `NK.WeakNU.levelIsoInput_of_chebotarev`. -/
theorem levelIsoInput_of_chebotarev_zero {k₁ k₂ k₁' k₂' : Type} [Field k₁] [NumberField k₁]
    [Field k₂] [NumberField k₂] [Field k₁'] [Field k₂'] [Algebra k₁ k₁'] [Algebra k₂ k₂']
    [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarev hU hC ϕ hϕ

/-- **The four-universe chain at `u₁ = u₂ = u₃ = u₄ = w = 0`** is the universe-0 chain: this is
`NK.WeakNU.levelIsoInput_of_chebotarev` with the endpoints renamed. -/
theorem levelIsoInput_of_chebotarev_universePoly_zero {k₁ k₂ k₁' k₂' : Type} [Field k₁]
    [NumberField k₁] [Field k₂] [NumberField k₂] [Field k₁'] [Field k₂'] [Algebra k₁ k₁']
    [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarev_universePoly hU hC ϕ hϕ

end

end NK.UniverseWeakNU
