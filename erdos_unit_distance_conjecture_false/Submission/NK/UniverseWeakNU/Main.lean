/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The weak Neukirch–Uchida chain at an arbitrary universe: end goals

* `NK.UniverseWeakNU.isWeakUchida_of_chebotarevU` — `IsWeakUchidaU ℓ` from the residual
  catalogue `{IsUchidaModuleDataU 2, ChebotarevFrobeniusInputU}`;
* `NK.UniverseWeakNU.levelIsoInput_of_chebotarevU` — **the end goal**: the endgame hypothesis
  `NK.ReconstructField.LevelIsoInput ϕ hϕ` for `{K₁ K₂ K₁' K₂' : Type u}`, from the residual
  catalogue;
* `NK.UniverseWeakNU.isWeakUchida`, `NK.UniverseWeakNU.levelIsoInput_of_chebotarev` — the same
  statements at `u = 0`, where the `U`-props are *definitionally* the originals, as a consistency
  check: the universe-0 chain of `Submission/Work/WeakNU/` is recovered.

A caller must write the universe explicitly on the hypothesis props
(`IsUchidaModuleDataU.{u} 2`, `ChebotarevFrobeniusInputU.{u}`); see `MainWeak.lean` for the reason
and `Pinned.lean` for an alternative with the universe inferred from a `Type u` argument.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.MainWeak
import Submission.NK.UniverseWeakNU.PrimeCountU

namespace NK.UniverseWeakNU

open IntermediateField

noncomputable section

universe u

/-- **The weak Neukirch–Uchida theorem from the residual catalogue of the polymorphic chapter**,
at an arbitrary universe.  Copy of `NK.WeakNU.isWeakUchida_of_chebotarev`. -/
theorem isWeakUchida_of_chebotarevU {ℓ : ℕ} (hU : IsUchidaModuleDataU.{u} 2)
    (hC : ChebotarevFrobeniusInputU.{u}) : IsWeakUchidaU.{u} ℓ :=
  isWeakUchidaU hU (perlisGassmannInputU hC)

/-- The same, with the counting statement (a theorem here) kept as an explicit input. -/
theorem isWeakUchida_of_chebotarev_and_primeCountU {ℓ : ℕ} (hU : IsUchidaModuleDataU.{u} 2)
    (hC : ChebotarevFrobeniusInputU.{u}) (hPC : PrimeCountOrbitInputU.{u}) : IsWeakUchidaU.{u} ℓ :=
  isWeakUchidaU hU (perlisGassmannInputU_of_chebotarev_and_primeCountU hC hPC)

/-- **The level-wise input of the reconstruction, at an arbitrary universe, from Čebotarev and
Uchida's module data at `ℓ = 2`.**  This is the end goal of the polymorphic re-run of the
weak-Neukirch–Uchida chain:

`NK.ReconstructField.LevelIsoInput ϕ hϕ` is the endgame hypothesis of
`Submission.NeukirchUchida.Endgame`, and this theorem produces it at `{K₁ K₂ K₁' K₂' : Type u}`
instead of only at `Type`. -/
theorem levelIsoInput_of_chebotarevU {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataU.{u} 2) (hC : ChebotarevFrobeniusInputU.{u})
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_isWeakUchidaU (ℓ := 2) (isWeakUchidaU (ℓ := 2) hU (perlisGassmannInputU hC))
    ϕ hϕ

/-- The same, with the counting statement (a theorem here) kept as an explicit input. -/
theorem levelIsoInput_of_chebotarev_and_primeCountU {K₁ K₂ K₁' K₂' : Type u} [Field K₁]
    [NumberField K₁] [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataU.{u} 2) (hC : ChebotarevFrobeniusInputU.{u})
    (hPC : PrimeCountOrbitInputU.{u})
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_isWeakUchidaU (ℓ := 2)
    (isWeakUchidaU (ℓ := 2) hU (perlisGassmannInputU_of_chebotarev_and_primeCountU hC hPC)) ϕ hϕ

/-- **The weak Neukirch–Uchida theorem in the σ-free vocabulary of the reconstruction**, at an
arbitrary universe.  Copy of `NK.WeakNU.weakNeukirchUchidaIso`. -/
theorem weakNeukirchUchidaIsoU {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataU.{u} 2) (hP : PerlisGassmannInputU.{u})
    (h : Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))) :
    NK.ReconstructField.WeakNeukirchUchidaIso K₁ K₂ :=
  isWeakUchidaU (ℓ := 2) hU hP K₁ K₂ K₁' K₂' h

/-! ## Consistency check: the `.{0}` instance

At `u = 0` the `U`-props are *definitionally equal* to the originals
(`Submission/Work/UniverseWeakNU/Zero.lean`), so the polymorphic chain instantiates to the
universe-0 chain of `Submission/Work/WeakNU/`: these two theorems are `NK.WeakNU.isWeakUchida`
and `NK.WeakNU.levelIsoInput_of_chebotarev` up to the definitional unfolding of the props. -/

/-- **The `.{0}` instance of `isWeakUchidaU`**: the universe-0 weak Neukirch–Uchida theorem, from
`NK.UchidaKummer.IsUchidaModuleData 2` and Čebotarev. -/
theorem isWeakUchida {ℓ : ℕ} (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hC : NK.WeakNU.ChebotarevFrobeniusInput) : NK.UchidaKummer.IsWeakUchida ℓ :=
  isWeakUchidaU (ℓ := ℓ) hU (perlisGassmannInputU hC)

/-- **The `.{0}` instance of `levelIsoInput_of_chebotarevU`**: the endgame input
`NK.ReconstructField.LevelIsoInput ϕ hϕ` at `Type`, from `NK.UchidaKummer.IsUchidaModuleData 2`
and Čebotarev. -/
theorem levelIsoInput_of_chebotarev {k₁ k₂ k₁' k₂' : Type} [Field k₁] [NumberField k₁]
    [Field k₂] [NumberField k₂] [Field k₁'] [Field k₂'] [Algebra k₁ k₁'] [Algebra k₂ k₂']
    [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarevU (K₁ := k₁) (K₂ := k₂) (K₁' := k₁') (K₂' := k₂') hU hC ϕ hϕ

end

end NK.UniverseWeakNU
