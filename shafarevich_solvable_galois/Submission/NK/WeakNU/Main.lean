/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The weak Neukirch–Uchida theorem, and the level-wise input of the reconstruction

This file assembles the headline of the chapter from

* `NK.WeakNU.perlisGassmannInput_of_chebotarev_and_primeCount` — the Perlis/Gassmann input of §6,
  proved here from Čebotarev plus the prime count (`Submission/Work/WeakNU/PerlisGassmann.lean`);
* `NK.UchidaKummer.IsUchidaModuleData ℓ` — the Kummer-theoretic embedding problem of §6
  Lemma 6.1 in module form (reduced in `Submission/Work/WeakNU/UchidaModuleData.lean`).

## The two forms of the weak theorem

`NK.UchidaKummer.IsWeakUchida ℓ` is stated *without* the hypothesis `μ_ℓ ⊆ K_i` of
arXiv:2601.01251 §6, and its statement does not mention `ℓ`: it is the weak Neukirch–Uchida theorem
in its full form ("number fields with isomorphic absolute Galois groups are isomorphic"), which
Neukirch–Uchida prove for all `ℓ`.  The Uchida §6 route delivers it with the paper's hypothesis
`μ_ℓ ⊆ K_i` (`NK.WeakNU.IsWeakUchidaOf`), and with `ℓ = 2` the hypothesis is automatic (`-1` is a
primitive second root of unity in every number field).  Since `IsWeakUchida` does not depend on
`ℓ`, the case `ℓ = 2` gives `NK.UchidaKummer.IsWeakUchida ℓ` for *every* `ℓ`:

```
NK.WeakNU.isWeakUchida (hU : IsUchidaModuleData 2) (hP : PerlisGassmannInput) :
    NK.UchidaKummer.IsWeakUchida ℓ
```

Combined with the reduction of `PerlisGassmannInput` (which is a theorem of this chapter, from
Čebotarev's theorem alone), the residual catalogue of the weak theorem is

* `NK.UchidaKummer.IsUchidaModuleData 2` — the binding constraint;
* `NK.WeakNU.ChebotarevFrobeniusInput` — Čebotarev's density theorem.

See `README.md` for the full statement list, the audit of each input and the references.
-/

import Submission.NK.WeakNU.Defs
import Submission.NK.WeakNU.PrimeCount
import Submission.NK.UchidaKummer.Uchida.Main
import Submission.NK.ReconstructField.LevelCandidate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.WeakNU

noncomputable section

/-! ## The weak theorem with the paper's cyclotomic hypothesis -/

/-- **§6 of arXiv:2601.01251: `IsWeakUchidaOf ℓ` from Uchida's module data and Perlis/Gassmann.**

Number fields containing `μ_ℓ` (`ℓ` prime) with isomorphic absolute Galois groups are isomorphic,
from Uchida's module data (`NK.UchidaKummer.IsUchidaModuleData ℓ`) and the Perlis/Gassmann input
(`NK.UchidaKummer.PerlisGassmannInput`). -/
theorem isWeakUchidaOf {ℓ : ℕ} [Fact ℓ.Prime] (hU : NK.UchidaKummer.IsUchidaModuleData ℓ)
    (hP : NK.UchidaKummer.PerlisGassmannInput) : IsWeakUchidaOf ℓ := by
  intro K₁ K₂ _ _ _ _ K₁' _ _ _ K₂' _ _ _ hμ₁ hμ₂ hiso
  obtain ⟨ϕ⟩ := hiso
  exact NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs hU hP K₁ K₂
    hμ₁ hμ₂ (NK.UchidaKummer.hasIsomorphicAbsGalois_of_galoisEquiv ϕ)

/-- **The Perlis/Gassmann input is not needed separately: it follows from the two arithmetic
statements of this chapter.**  (This is the requested name
`NK.WeakNU.perlisGassmannInput`; it is
`NK.WeakNU.perlisGassmannInput_of_chebotarev_and_primeCount` of
`Submission/Work/WeakNU/PerlisGassmann.lean`.) -/
theorem perlisGassmannInput (hC : ChebotarevFrobeniusInput)
    (hPC : PrimeCountOrbitInput) : NK.UchidaKummer.PerlisGassmannInput :=
  perlisGassmannInput_of_chebotarev_and_primeCount hC hPC

/-- Alias of `NK.WeakNU.perlisGassmannInput`. -/
theorem perlisGassmannInput_of_inputs (hC : ChebotarevFrobeniusInput)
    (hPC : PrimeCountOrbitInput) : NK.UchidaKummer.PerlisGassmannInput :=
  perlisGassmannInput_of_chebotarev_and_primeCount hC hPC

/-! ## The weak theorem in the form used by the reconstruction -/

/-- **The weak Neukirch–Uchida theorem from `IsUchidaModuleData 2`.**

`NK.UchidaKummer.IsWeakUchida ℓ` does not depend on `ℓ`; taking `ℓ = 2`, where the hypothesis
`μ_ℓ ⊆ K_i` of Uchida's §6 is automatic, therefore gives the statement for every `ℓ`.  This is the
form consumed by `NK.ReconstructField.levelIsoInput_of_isWeakUchida`. -/
theorem isWeakUchida {ℓ : ℕ} (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput) : NK.UchidaKummer.IsWeakUchida ℓ := by
  intro K₁ K₂ _ _ _ _ K₁' _ _ _ K₂' _ _ _ hiso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isWeakUchidaOf (ℓ := 2) hU hP K₁ K₂ K₁' K₂'
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩ hiso

/-- **The weak Neukirch–Uchida theorem from the residual catalogue of this chapter.**

`PrimeCountOrbitInput` is a theorem of this chapter (`NK.WeakNU.primeCountOrbitInput`), so the
arithmetic input of the Perlis/Gassmann step can be omitted. -/
theorem isWeakUchida_of_chebotarev {ℓ : ℕ}
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hC : ChebotarevFrobeniusInput) : NK.UchidaKummer.IsWeakUchida ℓ :=
  isWeakUchida hU (perlisGassmannInput_of_chebotarev hC)

/-- The previous form, with the (now proved) counting statement kept as an explicit input. -/
theorem isWeakUchida_of_chebotarev_and_primeCount {ℓ : ℕ}
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hC : ChebotarevFrobeniusInput) (hPC : PrimeCountOrbitInput) :
    NK.UchidaKummer.IsWeakUchida ℓ :=
  isWeakUchida hU (perlisGassmannInput_of_chebotarev_and_primeCount hC hPC)

/-- **`NK.ReconstructField.WeakNeukirchUchidaIso K₁ K₂` from an isomorphism of absolute Galois
groups.**

This is the weak Neukirch–Uchida theorem in the σ-free vocabulary of the reconstruction component:
two number fields with isomorphic absolute Galois groups are isomorphic. -/
theorem weakNeukirchUchidaIso {K₁ K₂ K₁' K₂' : Type} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput)
    (h : Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))) :
    NK.ReconstructField.WeakNeukirchUchidaIso K₁ K₂ :=
  isWeakUchida (ℓ := 2) hU hP K₁ K₂ K₁' K₂' h

/-- **The level-wise weak input of the reconstruction.**

`NK.ReconstructField.LevelIsoInput ϕ hϕ` — for every finite level `L ⊆ K₁'`, the level `L` is
isomorphic to its `ϕ`-image `levelMap ϕ L` — is a consequence of the weak Neukirch–Uchida theorem
(`NK.ReconstructField.levelIsoInput_of_isWeakUchida`), hence of the residual catalogue of this
chapter.  This is the input `(W)` of
`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelIsoInput`. -/
theorem levelIsoInput {k₁ k₂ k₁' k₂' : Type} [Field k₁] [NumberField k₁] [Field k₂]
    [NumberField k₂] [Field k₁'] [Field k₂'] [Algebra k₁ k₁'] [Algebra k₂ k₂']
    [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hP : NK.UchidaKummer.PerlisGassmannInput)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  NK.ReconstructField.levelIsoInput_of_isWeakUchida (isWeakUchida (ℓ := 2) hU hP) ϕ hϕ

/-- **The level-wise weak input, from Čebotarev and Uchida's module data at `ℓ = 2`.** -/
theorem levelIsoInput_of_chebotarev {k₁ k₂ k₁' k₂' : Type} [Field k₁]
    [NumberField k₁] [Field k₂] [NumberField k₂] [Field k₁'] [Field k₂'] [Algebra k₁ k₁']
    [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hC : ChebotarevFrobeniusInput)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput hU (perlisGassmannInput_of_chebotarev hC) ϕ hϕ

/-- The same, with the (now proved) counting statement kept as an explicit input. -/
theorem levelIsoInput_of_chebotarev_and_primeCount {k₁ k₂ k₁' k₂' : Type} [Field k₁]
    [NumberField k₁] [Field k₂] [NumberField k₂] [Field k₁'] [Field k₂'] [Algebra k₁ k₁']
    [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (hU : NK.UchidaKummer.IsUchidaModuleData 2)
    (hC : ChebotarevFrobeniusInput) (hPC : PrimeCountOrbitInput)
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  levelIsoInput hU (perlisGassmannInput_of_chebotarev_and_primeCount hC hPC) ϕ hϕ

end

end NK.WeakNU
