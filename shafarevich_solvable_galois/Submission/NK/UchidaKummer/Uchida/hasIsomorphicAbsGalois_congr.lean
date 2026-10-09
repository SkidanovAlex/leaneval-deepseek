import Mathlib
import Submission.NK.UchidaKummer.Uchida.ModuleData
import Submission.NK.UchidaKummer.Uchida.IsomorphicAbsGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Uchida

open NK.UchidaKummer (algEquivCongrOfAlgebraMap)

/-- `HasIsomorphicAbsGalois` is symmetric: `Gal(K₁'/K₁) ≃ Gal(K₂'/K₂)` may be inverted. -/
theorem hasIsomorphicAbsGalois_symm {K₁ K₂ : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] (h : NK.UchidaKummer.HasIsomorphicAbsGalois K₁ K₂) :
    NK.UchidaKummer.HasIsomorphicAbsGalois K₂ K₁ := by
  intro K₂' _ _ _ K₁' _ _ _
  obtain ⟨f⟩ := h K₁' K₂'
  exact ⟨f.symm⟩

/-- `NK.UchidaKummer.HasIsomorphicAbsGalois` depends only on the isomorphism class of the number
field: if `K₁ ≅ M₁` and `K₂ ≅ M₂` are isomorphisms of number fields and `K₁`, `K₂` have isomorphic
absolute Galois groups (for every choice of separable closure), then so do `M₁`, `M₂`. -/
theorem hasIsomorphicAbsGalois_congr {K₁ K₂ M₁ M₂ : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field M₁] [NumberField M₁] [Field M₂] [NumberField M₂]
    (e₁ : K₁ ≃+* M₁) (e₂ : K₂ ≃+* M₂) (h : NK.UchidaKummer.HasIsomorphicAbsGalois K₁ K₂) :
    NK.UchidaKummer.HasIsomorphicAbsGalois M₁ M₂ := by
  -- Let `M₁'` (resp. `M₂'`) be a separable closure of `M₁` (resp. `M₂`).  Pulling scalars back
  -- along `e₁` (resp. `e₂`) turns it into a separable closure of `K₁` (resp. `K₂`), so `h` may be
  -- applied to it directly.  This avoids having to produce a separable closure of `K₁` out of
  -- thin air: the closures we are handed are exactly the ones we feed to `h`.
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
  -- `h` compares the two pulled-back closures, and `algEquivCongrOfAlgebraMap` replaces
  -- `Kᵢ`-linearity by `Mᵢ`-linearity at both ends.
  obtain ⟨k⟩ := h M₁' M₂'
  exact ⟨(algEquivCongrOfAlgebraMap e₁ (fun x => rfl)).symm.trans
    (k.trans (algEquivCongrOfAlgebraMap e₂ (fun x => rfl)))⟩

end NK.UchidaKummer.Uchida
