/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Calling the polymorphic chain

Three worked examples of the end goal `NK.UniverseWeakNU.levelIsoInput_of_chebotarevU`:

1. at an arbitrary universe `u`, with the universe written explicitly on the hypothesis props
   (`IsUchidaModuleDataU.{u}`, `ChebotarevFrobeniusInputU.{u}`) — this is the form mirroring the
   requestor's blocked example;
2. the same with the universe inferred from a `Type u` argument, using the `…UAt` aliases of
   `Submission/Work/UniverseWeakNU/Pinned.lean`;
3. at `u = 0`, reproducing the universe-0 chain of `Submission/Work/WeakNU/`.

The examples are proofs, not `sorry`s.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Main
import Submission.NK.UniverseWeakNU.Pinned
import Submission.NK.UniverseWeakNU.Zero
import Submission.NK.WeakNU.Main
import Submission.NK.UniverseWeakNU.ArbitraryUniverses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-- **Pattern 1 (explicit universes).**  The requestor's example, at an arbitrary universe. -/
example {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataU.{u} 2) (hC : ChebotarevFrobeniusInputU.{u})
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarevU hU hC ϕ hϕ

/-- **Pattern 2 (universes pinned by a `Type u` argument).** -/
example {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataUAt K₁ 2) (hC : ChebotarevFrobeniusInputUAt K₁)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarevU hU hC ϕ hϕ

/-- **Pattern 3 (`u = 0`).**  The universe-0 chain of `Submission/Work/WeakNU/`, recovered by
instantiating the polymorphic chain. -/
example {k₁ k₂ k₁' k₂' : Type} [Field k₁] [NumberField k₁] [Field k₂] [NumberField k₂]
    [Field k₁'] [Field k₂'] [Algebra k₁ k₁'] [Algebra k₂ k₂'] [IsSepClosure k₁ k₁']
    [IsSepClosure k₂ k₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  NK.WeakNU.levelIsoInput_of_chebotarev hU hC ϕ hϕ

/-- **Pattern 0: the requestor's blocked example, now working.**

`hU` and `hC` are the *universe-0* inputs `NK.UchidaKummer.IsUchidaModuleData 2` and
`NK.WeakNU.ChebotarevFrobeniusInput`; the conclusion is `LevelIsoInput ϕ hϕ` at `Type u`.  This is
the example whose universe error is quoted in the request; it is now a proof, because the §6
argument only ever evaluates the module data at the *working universe* `w = 0` (the common field
`AlgebraicClosure ℚ`) and transports everything else along ring isomorphisms. -/
example {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarev_universePoly hU hC ϕ hϕ

/-- **Pattern 0': the same with four independent universes**, matching
`{K₁ K₂ K₁' K₂' : Type*}` of `Submission.neukirch_uchida` and of
`NK.Reconstruct.exists_sigma_of_weakNeukirchUchida_and_levelIso`. -/
example {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput_of_chebotarev_universePoly hU hC ϕ hϕ

/-- The weak theorem at four independent universes, from the universe-0 inputs. -/
example {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hC : NK.WeakNU.ChebotarevFrobeniusInput)
    (h : Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))) : Nonempty (K₁ ≃+* K₂) :=
  isWeakUchidaRat (ℓ := 2) hU hC K₁ K₂ K₁' K₂' h

/-- The weak theorem itself, at an arbitrary universe. -/
example {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂']
    (hU : IsUchidaModuleDataU.{u} 2) (hC : ChebotarevFrobeniusInputU.{u})
    (h : Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))) : Nonempty (K₁ ≃+* K₂) :=
  isWeakUchida_of_chebotarevU (ℓ := 2) hU hC K₁ K₂ K₁' K₂' h

end

end NK.UniverseWeakNU
