import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_hom_subtype

namespace Commons.LinearAlgebra.LinearMap

open _root_.LinearMap

/-- A linear map `A →ₗ[K] B` whose range lies in a submodule `P ≤ B` is the same thing as a
linear map `A →ₗ[K] P`. -/
noncomputable def homRangeLeEquiv {K : Type*} [Field K] {A B : Type*} [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (P : Submodule K B) :
    {f : A →ₗ[K] B // LinearMap.range f ≤ P} ≃ (A →ₗ[K] P) where
  toFun f := codRestrict P f.1 (fun x => f.2 (mem_range_self f.1 x))
  invFun g := ⟨P.subtype.comp g,
    (range_comp_le_range g P.subtype).trans (le_of_eq (Submodule.range_subtype P))⟩
  left_inv f := by
    apply Subtype.ext
    exact subtype_comp_codRestrict f.1 P (fun x => f.2 (mem_range_self f.1 x))
  right_inv g := by
    ext x
    simp [codRestrict_apply]

theorem card_hom_range_le_pow {K : Type*} [Field K] [Fintype K] {A B : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] [AddCommGroup B] [Module K B] [FiniteDimensional K B] (P : Submodule K B) : Nat.card {f : A →ₗ[K] B // LinearMap.range f ≤ P} = Nat.card K ^ (Module.finrank K A * Module.finrank K P) := by
  rw [Nat.card_congr (homRangeLeEquiv P)]
  exact Commons.LinearAlgebra.Submodule.natCard_linearMap K A P

end Commons.LinearAlgebra.LinearMap
