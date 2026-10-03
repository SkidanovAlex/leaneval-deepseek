import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Base

open scoped TensorProduct
open Work.ORTorsion

/-- In a monoid algebra, the basis monomial `single g 1` is a unit (with inverse
`single g⁻¹ 1`). -/
lemma isUnit_single_one {R : Type*} [Semiring R] {G : Type*} [Group G] (g : G) :
    IsUnit (MonoidAlgebra.single g (1 : R) : MonoidAlgebra R G) := by
  refine ⟨⟨MonoidAlgebra.single g (1 : R), MonoidAlgebra.single g⁻¹ (1 : R), ?_, ?_⟩, rfl⟩
  · rw [MonoidAlgebra.single_mul_single, mul_inv_cancel, mul_one]
    rfl
  · rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one]
    rfl

/-- Multiplication by a unit of a ring is injective on any module. -/
lemma injective_smul_of_isUnit {R : Type*} [Ring R] {M : Type*} [AddCommMonoid M]
    [DistribMulAction R M] {a : R} (ha : IsUnit a) : Function.Injective (fun m : M => a • m) := by
  obtain ⟨u, rfl⟩ := ha
  intro m n h
  change (↑u : R) • m = (↑u : R) • n at h
  have hm : (↑u⁻¹ : R) • ((↑u : R) • m) = m := by rw [← mul_smul, Units.inv_mul, one_smul]
  have hn : (↑u⁻¹ : R) • ((↑u : R) • n) = n := by rw [← mul_smul, Units.inv_mul, one_smul]
  rw [← hm, h, hn]

/-- The basis monomial `single g 1` of the group algebra `K[G]` acts injectively on the tensor
product `V ⊗[K] D(⊤)`.

Note on the scalar action: the `SMul (MonoidAlgebra K G) (V ⊗[K] ↥(L.D ⊤))` used below is
`TorsionData.instDiagTopSmul` (priority 2000, so it takes precedence over
`TensorProduct.leftHasSMul`), i.e. the *diagonal* action; see
`TorsionData.instDiagTopSmul_apply`.  The statement holds because `single g 1` is a unit of
`K[G]` (see `isUnit_single_one`), with inverse `single g⁻¹ 1`; the explicit computation is
`single_inv_diag_single_diag`. -/
theorem injective_single_smul {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] (g : G) :
    Function.Injective (fun m : V ⊗[K] ↥(L.D ⊤) =>
      (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) • m) := by
  intro m m' h
  have key : ∀ z : V ⊗[K] ↥(L.D ⊤),
      (MonoidAlgebra.single g⁻¹ (1 : K) : MonoidAlgebra K G) •
        ((MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) • z) = z := by
    intro z
    rw [TorsionData.instDiagTopSmul_apply (L := L) V,
      TorsionData.instDiagTopSmul_apply (L := L) V]
    simpa using single_inv_diag_single_diag (MonoidHom.id G) L.genTop g (c := (1 : K))
      one_ne_zero z
  have h' : (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) • m
      = (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) • m' := h
  rw [← key m, h', key m']

end Work.ORTorsion.Base
