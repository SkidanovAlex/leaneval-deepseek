/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# §6 without a chosen common field: the weak Neukirch–Uchida theorem

Reference: arXiv:2601.01251, §6, proof of `thm:uchida isomorphism`.

`NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis` proves §6 for two subfields
`L^{H₁}`, `L^{H₂}` of a common finite Galois extension `L/ℚ`.  This file removes the common field:
two number fields with isomorphic absolute Galois groups are embedded into the algebraic closure of
`ℚ` (via `IsAlgClosed.lift`), and the normal closure of the compositum of the two images supplies the
common finite Galois extension `L/ℚ` of the theorem above.
-/

import Submission.NK.UchidaKummer.Uchida.Assembly
import Submission.NK.UchidaKummer.Uchida.IsomorphicAbsGalois
import Submission.NK.UchidaKummer.Uchida.exists_isGalois_sup_le
import Submission.NK.UchidaKummer.Uchida.hasIsomorphicAbsGalois_congr
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

open IntermediateField

/-- The image of a number field under an embedding into a field is finite dimensional over `ℚ`. -/
theorem finiteDimensional_fieldRange {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra ℚ Ω] (i : K →ₐ[ℚ] Ω) : FiniteDimensional ℚ ↥(i.fieldRange) :=
  i.toLinearMap.finiteDimensional_range

/-- **§6 of arXiv:2601.01251, without a chosen common field.**

Two number fields `K₁`, `K₂` containing `μ_ℓ` whose absolute Galois groups are isomorphic (for every
choice of separable closure, `NK.UchidaKummer.HasIsomorphicAbsGalois`) are isomorphic.

The proof embeds both fields into the algebraic closure of `ℚ`, passes to the normal closure of the
compositum of the two images — a common finite Galois extension `L/ℚ` — and applies
`NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis`.

The hypotheses `hU` and `hP` are the two classical inputs: Uchida's module data (the embedding
problem of §6 Lemma 6.1 in module form, plus `cor:arith equiv`) and Perlis/Gassmann. -/
theorem nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : IsUchidaModuleData ℓ) (hP : PerlisGassmannInput)
    (K₁ K₂ : Type*) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hiso : HasIsomorphicAbsGalois K₁ K₂) :
    Nonempty (K₁ ≃+* K₂) := by
  classical
  haveI : IsAlgClosed (AlgebraicClosure ℚ) := inferInstance
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let i : K₁ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let j : K₂ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  haveI hi : FiniteDimensional ℚ ↥(i.fieldRange) := finiteDimensional_fieldRange i
  haveI hj : FiniteDimensional ℚ ↥(j.fieldRange) := finiteDimensional_fieldRange j
  obtain ⟨N, hN₁, hN₂, hfinN, hgalN⟩ := Uchida.exists_isGalois_sup_le i.fieldRange j.fieldRange
  haveI : FiniteDimensional ℚ ↥N := hfinN
  haveI : IsGalois ℚ ↥N := hgalN
  haveI : NumberField ↥N :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ℚ) N
  let iN : K₁ →ₐ[ℚ] ↥N :=
    i.codRestrict N.toSubalgebra (fun x => hN₁ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let jN : K₂ →ₐ[ℚ] ↥N :=
    j.codRestrict N.toSubalgebra (fun x => hN₂ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let H₁ : Subgroup Gal(↥N/ℚ) := iN.fieldRange.fixingSubgroup
  let H₂ : Subgroup Gal(↥N/ℚ) := jN.fieldRange.fixingSubgroup
  -- The isomorphisms `K_i ≃+* ↥(fixedField H_i)`.
  have hiso₁ : Nonempty (K₁ ≃+* ↥(IntermediateField.fixedField H₁)) :=
    ⟨(AlgEquiv.ofInjective iN iN.injective).toRingEquiv.trans
      ((IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup iN.fieldRange)).symm.toRingEquiv)⟩
  have hiso₂ : Nonempty (K₂ ≃+* ↥(IntermediateField.fixedField H₂)) :=
    ⟨(AlgEquiv.ofInjective jN jN.injective).toRingEquiv.trans
      ((IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup jN.fieldRange)).symm.toRingEquiv)⟩
  obtain ⟨e₁⟩ := hiso₁
  obtain ⟨e₂⟩ := hiso₂
  have hμH₁ : ∃ ζ : ↥(IntermediateField.fixedField H₁), IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ₁
    exact ⟨e₁ ζ, hζ.map_of_injective e₁.injective⟩
  have hμH₂ : ∃ ζ : ↥(IntermediateField.fixedField H₂), IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ₂
    exact ⟨e₂ ζ, hζ.map_of_injective e₂.injective⟩
  obtain ⟨ζ, hζ⟩ := hμ₁
  obtain ⟨e⟩ := nonempty_ringEquiv_of_uchidaModuleData_and_perlis hU hP (L := ↥N)
    ⟨iN ζ, hζ.map_of_injective iN.injective⟩ H₁ H₂ hμH₁ hμH₂
    (Uchida.hasIsomorphicAbsGalois_congr e₁ e₂ hiso)
  exact ⟨e₁.trans (e.trans e₂.symm)⟩

end NK.UchidaKummer
