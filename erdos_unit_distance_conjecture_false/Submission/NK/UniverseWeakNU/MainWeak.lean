/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The weak Neukirch–Uchida theorem at an arbitrary universe, and the level-wise input

Universe-polymorphic copies of the headline of `Submission/Work/WeakNU/`:

* `NK.UniverseWeakNU.isWeakUchidaOfU` — §6 with the paper's cyclotomic hypothesis
  (copy of `NK.WeakNU.isWeakUchidaOf`);
* `NK.UniverseWeakNU.isWeakUchidaU` — the weak Neukirch–Uchida theorem, `IsWeakUchidaU ℓ`, from
  Uchida's module data at `ℓ = 2` (copy of `NK.WeakNU.isWeakUchida`);
* `NK.UniverseWeakNU.levelIsoInput_of_isWeakUchidaU` — the level-wise input
  `NK.ReconstructField.LevelIsoInput ϕ hϕ`, at `{K₁ K₂ K₁' K₂' : Type u}` (copy of
  `NK.ReconstructField.levelIsoInput_of_isWeakUchida`).

## Universes: read this before using the API

`IsUchidaModuleDataU`, `PerlisGassmannInputU`, `ChebotarevFrobeniusInputU`, `IsWeakUchidaU`, … are
`Prop`-valued *closed* definitions carrying a universe parameter `u` which does note appear in
their type (`IsUchidaModuleDataU : (ℓ : ℕ) → Prop`).  Lean therefore cannot infer `u` from a bare
occurrence, and one must write it explicitly:

```lean
example {K₁ K₂ K₁' K₂' : Type u} […] (hU : NK.UniverseWeakNU.IsUchidaModuleDataU.{u} 2)
    (hP : NK.UniverseWeakNU.PerlisGassmannInputU.{u})
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  NK.UniverseWeakNU.levelIsoInput_of_isWeakUchidaU (NK.UniverseWeakNU.isWeakUchidaU hU hP) ϕ hϕ
```

The same applies at `u = 0`, where the `U`-props are *definitionally equal* to the originals
(`Submission/Work/UniverseWeakNU/Zero.lean`), so no annotation is needed there.

For callers who would rather have the universe inferred from a `Type u` argument,
`Submission/Work/UniverseWeakNU/Pinned.lean` provides the aliases `…UAt (w : Type u)` (for instance
`IsUchidaModuleDataUAt K₁ 2`, `ChebotarevFrobeniusInputUAt K₁`), together with the main theorems in
that form.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.UniverseWeakNU.UchidaU
import Submission.NK.UniverseWeakNU.IsomorphicAbsGaloisU
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.UchidaKummer.Uchida.Main

namespace NK.UniverseWeakNU

open IntermediateField

noncomputable section

universe u

/-! ## The weak theorem with the paper's cyclotomic hypothesis -/

/-- **§6 of arXiv:2601.01251: `IsWeakUchidaOfU ℓ` from Uchida's module data and Perlis/Gassmann**,
at an arbitrary universe.  Copy of `NK.WeakNU.isWeakUchidaOf`. -/
theorem isWeakUchidaOfU {ℓ : ℕ} [Fact ℓ.Prime] (hU : IsUchidaModuleDataU.{u} ℓ)
    (hP : PerlisGassmannInputU.{u}) : IsWeakUchidaOfU.{u} ℓ := by
  intro K₁ K₂ _ _ _ _ K₁' _ _ _ K₂' _ _ _ hμ₁ hμ₂ hiso
  obtain ⟨ϕ⟩ := hiso
  exact nonempty_ringEquiv_of_uchidaModuleData_and_perlis_absU hU hP K₁ K₂ hμ₁ hμ₂
    (hasIsomorphicAbsGaloisU_of_galoisEquiv ϕ)

/-! ## The weak theorem in the form used by the reconstruction -/

/-- **The weak Neukirch–Uchida theorem from `IsUchidaModuleDataU 2`**, at an arbitrary universe.
Copy of `NK.WeakNU.isWeakUchida`. -/
theorem isWeakUchidaU {ℓ : ℕ} (hU : IsUchidaModuleDataU.{u} 2) (hP : PerlisGassmannInputU.{u}) :
    IsWeakUchidaU.{u} ℓ := by
  intro K₁ K₂ _ _ _ _ K₁' _ _ _ K₂' _ _ _ hiso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isWeakUchidaOfU (ℓ := 2) hU hP K₁ K₂ K₁' K₂'
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩ hiso

/-- **The level-wise weak input of the reconstruction**, at an arbitrary universe.  Copy of
`NK.ReconstructField.levelIsoInput_of_isWeakUchida`. -/
theorem levelIsoInput_of_isWeakUchidaU {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ℓ : ℕ} (hW : IsWeakUchidaU.{u} ℓ)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) :
    NK.ReconstructField.LevelIsoInput ϕ hϕ :=
  fun L _ =>
    @hW ↥L ↥(NK.Reconstruct.levelMap ϕ L) _ _ _
      (NK.Reconstruct.numberField_levelMap hϕ L) K₁' _ _
      (NK.Reconstruct.isSepClosure_level L) K₂' _ _
      (NK.Reconstruct.isSepClosure_level (NK.Reconstruct.levelMap ϕ L))
      ⟨NK.ReconstructField.levelGalEquiv ϕ hϕ L⟩

end

end NK.UniverseWeakNU
