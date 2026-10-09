import Mathlib
import Submission.NK.UchidaKummer.Uchida.ModuleData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Uchida

/-- Two finite extensions of `ℚ` inside a common algebraically closed field are contained in a
common finite Galois extension of `ℚ`. -/
theorem exists_isGalois_sup_le {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic ℚ Ω] (L₁ L₂ : IntermediateField ℚ Ω) [FiniteDimensional ℚ ↥L₁]
    [FiniteDimensional ℚ ↥L₂] :
    ∃ (N : IntermediateField ℚ Ω), L₁ ≤ N ∧ L₂ ≤ N ∧ FiniteDimensional ℚ ↥N ∧ IsGalois ℚ ↥N := by
  -- `Ω` is an algebraic closure of `ℚ`, hence Galois over `ℚ`.
  haveI hΩ : Normal ℚ Ω :=
    { toIsAlgebraic := inferInstance
      splits' := fun x => IsAlgClosed.splits _ }
  haveI hGalΩ : IsGalois ℚ Ω :=
    isGalois_iff.mpr ⟨Algebra.IsSeparable.of_integral ℚ Ω, hΩ⟩
  -- Fix the `ℚ`-algebra structure on `↥(L₁ ⊔ L₂)` to be the canonical one induced by the
  -- inclusion into `Ω`; this is the structure used by `IntermediateField.normalClosure`.
  letI : Algebra ℚ ↥(L₁ ⊔ L₂) := IntermediateField.algebra' (K := ℚ) (L := Ω) (L₁ ⊔ L₂)
  let N : IntermediateField ℚ Ω := IntermediateField.normalClosure ℚ ↥(L₁ ⊔ L₂) Ω
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · exact le_sup_left.trans (IntermediateField.le_normalClosure (L₁ ⊔ L₂))
  · exact le_sup_right.trans (IntermediateField.le_normalClosure (L₁ ⊔ L₂))
  · exact normalClosure.is_finiteDimensional ℚ ↥(L₁ ⊔ L₂) Ω
  · -- `normalClosure` gives Galoisness for the `IntermediateField`-algebra structure; the
    -- statement asks for the canonical `ℚ`-algebra structure, and `Algebra ℚ _` is a subsingleton.
    have h := IsGalois.normalClosure ℚ ↥(L₁ ⊔ L₂) Ω
    rw [show (IntermediateField.algebra' (K := ℚ) (L := Ω) N) =
        (DivisionRing.toRatAlgebra (R := ↥N)) from Subsingleton.elim _ _] at h
    exact h

end NK.UchidaKummer.Uchida
