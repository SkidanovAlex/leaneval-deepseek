import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Base

-- The proof should use `sum_coeff_smul_single` (β is the sum of its monomials, so a support of
-- cardinality one means β = single g c with c ≠ 0) and `injective_single_smul_coeff`.
open scoped TensorProduct
open Work.ORTorsion

/-- A monomial `single g c` with a nonzero coefficient `c` is a unit of `K[G]`, with inverse
`single g⁻¹ c⁻¹`; hence its (diagonal) action on `V ⊗[K] D ⊤` is injective, with explicit left
inverse given by the action of `single g⁻¹ c⁻¹`. This is the `injective_single_smul_coeff` step:
no freeness or flatness of `V` is needed, only that `single g c` is invertible in `K[G]`. -/
theorem single_inv_smul_single_smul {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (g : G) {c : K} (hc : c ≠ 0) (m : V ⊗[K] ↥(L.D ⊤)) :
    (MonoidAlgebra.single g⁻¹ c⁻¹ : MonoidAlgebra K G) •
      ((MonoidAlgebra.single g c : MonoidAlgebra K G) • m) = m := by
  rw [TorsionData.instDiagTopSmul_apply (L := L) V, TorsionData.instDiagTopSmul_apply (L := L) V]
  exact single_inv_diag_single_diag (MonoidHom.id G) L.genTop g hc m

/-- Multiplication by `single g c` is injective on the diagonal module, for `c ≠ 0`. -/
theorem injective_single_smul_coeff {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (g : G) {c : K} (hc : c ≠ 0) :
    Function.Injective (fun m : V ⊗[K] ↥(L.D ⊤) =>
      (MonoidAlgebra.single g c : MonoidAlgebra K G) • m) := by
  intro m m' h
  have h2 := congrArg
    (fun z => (MonoidAlgebra.single g⁻¹ c⁻¹ : MonoidAlgebra K G) • z) h
  rw [single_inv_smul_single_smul L g hc, single_inv_smul_single_smul L g hc] at h2
  exact h2

theorem injective_of_card_one {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (β : MonoidAlgebra K G) (h1 : β.coeff.support.card = 1) :
    Function.Injective (fun m : V ⊗[K] ↥(L.D ⊤) => β • m) := by
  -- `β` is the sum of its monomials; a support of cardinality one means `β = single g c`, `c ≠ 0`.
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h1
  have hc : β.coeff g ≠ 0 := (Finsupp.support_eq_singleton.mp hg).1
  have hβc : β.coeff = Finsupp.single g (β.coeff g) := (Finsupp.support_eq_singleton.mp hg).2
  have hβ : β = MonoidAlgebra.single g (β.coeff g) := by
    rw [← MonoidAlgebra.coeff_inj]
    simpa using hβc
  rw [hβ]
  exact injective_single_smul_coeff L g hc

end Work.ORTorsion.Base
