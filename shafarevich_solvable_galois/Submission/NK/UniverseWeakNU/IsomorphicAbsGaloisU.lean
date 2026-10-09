/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `HasIsomorphicAbsGaloisU`: invariance of the absolute Galois group, at an arbitrary universe

Universe-polymorphic copies of

* `NK.UchidaKummer.hasIsomorphicAbsGalois_of_ringEquiv`
  (`Submission/Work/UchidaKummer/Uchida/IsomorphicAbsGalois.lean`),
* `NK.UchidaKummer.Uchida.hasIsomorphicAbsGalois_symm` and `..._congr`
  (`Submission/Work/UchidaKummer/Uchida/hasIsomorphicAbsGalois_congr.lean`),
* `NK.UchidaKummer.hasIsomorphicAbsGalois_of_galoisEquiv`
  (`Submission/Work/UchidaKummer/Uchida/Main.lean`),

with `HasIsomorphicAbsGalois` replaced by `NK.UniverseWeakNU.HasIsomorphicAbsGaloisU`.

The proofs are those of the originals: none of them uses anything specific to the bottom universe
(the only universe-sensitivity is in the *statement* of the two `Prop`s, both of which are here
replaced by their `Type u` versions).  In particular the key tool is the universe-polymorphic
uniqueness of the separable closure,
`NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure`
(`{K : Type u_1} {L : Type u_2} {M : Type u_3}`).
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.UchidaKummer.Uchida.IsomorphicAbsGalois
import Submission.NK.UchidaKummer.Uchida.hasIsomorphicAbsGalois_congr
import Submission.NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-- **Isomorphic number fields have isomorphic absolute Galois groups**, at an arbitrary universe.
Copy of `NK.UchidaKummer.hasIsomorphicAbsGalois_of_ringEquiv`. -/
theorem hasIsomorphicAbsGaloisU_of_ringEquiv {K₁ K₂ : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] (e : K₁ ≃+* K₂) : HasIsomorphicAbsGaloisU K₁ K₂ := by
  intro K₁' _ _ _ K₂' _ _ _
  -- Regard `K₂'` as a `K₁`-algebra by pulling back scalars along `e`.
  let φ : K₁ →+* K₂' := (algebraMap K₂ K₂').comp e.toRingHom
  letI : Algebra K₁ K₂' := φ.toAlgebra
  have hsep : Algebra.IsSeparable K₁ K₂' :=
    (Algebra.IsSeparable.iff_of_equiv_equiv e (RingEquiv.refl K₂') (by ext x; rfl)).mpr
      (inferInstance : Algebra.IsSeparable K₂ K₂')
  haveI : IsSepClosure K₁ K₂' :=
    ⟨(inferInstance : IsSepClosure K₂ K₂').sep_closed, hsep⟩
  exact ⟨(AlgEquiv.autCongr (IsSepClosure.equiv K₁ K₁' K₂')).trans
    (NK.UchidaKummer.algEquivCongrOfAlgebraMap e (fun x => rfl))⟩

/-- `HasIsomorphicAbsGaloisU` is symmetric.  Copy of
`NK.UchidaKummer.Uchida.hasIsomorphicAbsGalois_symm`. -/
theorem hasIsomorphicAbsGaloisU_symm {K₁ K₂ : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] (h : HasIsomorphicAbsGaloisU K₁ K₂) :
    HasIsomorphicAbsGaloisU K₂ K₁ := by
  intro K₂' _ _ _ K₁' _ _ _
  obtain ⟨f⟩ := h K₁' K₂'
  exact ⟨f.symm⟩

/-- `HasIsomorphicAbsGaloisU` depends only on the isomorphism class of the number field.  Copy of
`NK.UchidaKummer.Uchida.hasIsomorphicAbsGalois_congr`. -/
theorem hasIsomorphicAbsGaloisU_congr {K₁ K₂ M₁ M₂ : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field M₁] [NumberField M₁] [Field M₂] [NumberField M₂]
    (e₁ : K₁ ≃+* M₁) (e₂ : K₂ ≃+* M₂) (h : HasIsomorphicAbsGaloisU K₁ K₂) :
    HasIsomorphicAbsGaloisU M₁ M₂ := by
  intro M₁' _ _ _ M₂' _ _ _
  let φ₁ : K₁ →+* M₁' := (algebraMap M₁ M₁').comp e₁.toRingHom
  letI : Algebra K₁ M₁' := φ₁.toAlgebra
  have hsep₁ : Algebra.IsSeparable K₁ M₁' :=
    (Algebra.IsSeparable.iff_of_equiv_equiv e₁ (RingEquiv.refl M₁') (by ext x; rfl)).mpr
      (inferInstance : Algebra.IsSeparable M₁ M₁')
  haveI : IsSepClosure K₁ M₁' := ⟨(inferInstance : IsSepClosure M₁ M₁').sep_closed, hsep₁⟩
  let φ₂ : K₂ →+* M₂' := (algebraMap M₂ M₂').comp e₂.toRingHom
  letI : Algebra K₂ M₂' := φ₂.toAlgebra
  have hsep₂ : Algebra.IsSeparable K₂ M₂' :=
    (Algebra.IsSeparable.iff_of_equiv_equiv e₂ (RingEquiv.refl M₂') (by ext x; rfl)).mpr
      (inferInstance : Algebra.IsSeparable M₂ M₂')
  haveI : IsSepClosure K₂ M₂' := ⟨(inferInstance : IsSepClosure M₂ M₂').sep_closed, hsep₂⟩
  obtain ⟨k⟩ := h M₁' M₂'
  exact ⟨(NK.UchidaKummer.algEquivCongrOfAlgebraMap e₁ (fun x => rfl)).symm.trans
    (k.trans (NK.UchidaKummer.algEquivCongrOfAlgebraMap e₂ (fun x => rfl)))⟩

/-- **An isomorphism of absolute Galois groups gives `HasIsomorphicAbsGaloisU`.**  Copy of
`NK.UchidaKummer.hasIsomorphicAbsGalois_of_galoisEquiv`; the transport to arbitrary separable
closures uses the universe-polymorphic uniqueness of the separable closure. -/
theorem hasIsomorphicAbsGaloisU_of_galoisEquiv {K₁ K₂ : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂]
    {K₁' : Type u} [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    {K₂' : Type u} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) : HasIsomorphicAbsGaloisU K₁ K₂ := by
  intro A _ _ _ C _ _ _
  refine ⟨(NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure
        (K := K₁) (L := A) (M := K₁')).some.trans (ϕ.trans ?_)⟩
  exact (NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure
        (K := K₂) (L := C) (M := K₂')).some.symm

end

end NK.UniverseWeakNU
