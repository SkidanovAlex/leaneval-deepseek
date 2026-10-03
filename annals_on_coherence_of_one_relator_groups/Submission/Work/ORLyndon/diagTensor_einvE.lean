import Mathlib
import Submission.Work.ORLyndon.diagTensor_freeSetup

set_option autoImplicit false
set_option linter.unusedVariables false

open TensorProduct

namespace Work.ORLyndon

universe u v

variable {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)}
  [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
  [IsScalarTower K (MonoidAlgebra K G) M]

/-- Unfolding `dsVtens` in components. -/
theorem dsVtens_apply (g : G) (m : M) (i : Module.Free.ChooseBasisIndex K M) :
    dsVtens (K := K) (G := G) (M := M) g m i =
      MonoidAlgebra.single g
        (dsB.repr (MonoidAlgebra.GroupSMul.linearMap K M g⁻¹ m) i) := by
  change Finsupp.mapRange (MonoidAlgebra.lsingle (M := G) g)
    (MonoidAlgebra.lsingle (M := G) g).map_zero
    (dsB.repr (MonoidAlgebra.GroupSMul.linearMap K M g⁻¹ m)) i = _
  rw [Finsupp.mapRange_apply, MonoidAlgebra.lsingle_apply]

/-- The two linear maps `u ↦ dsEinv (mapRange (lsingle h) u)` and
`u ↦ single h 1 ⊗ (single h 1 • (linearCombination dsB u))` agree. -/
theorem dsEinv_mapRange_lsingle (h : G) :
    dsEinv.comp
        (Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle (S := K) (M := G) h)) =
      (TensorProduct.mk K (MonoidAlgebra K G) M (MonoidAlgebra.single h (1 : K))).comp
        ((MonoidAlgebra.GroupSMul.linearMap K M h).comp (Finsupp.linearCombination K dsB)) := by
  apply Module.Basis.ext
    (Finsupp.basisSingleOne (R := K) (ι := Module.Free.ChooseBasisIndex K M))
  intro j
  simp only [LinearMap.comp_apply, Finsupp.coe_basisSingleOne, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, MonoidAlgebra.lsingle_apply]
  rw [dsEinv_apply, Finsupp.sum_single_index (by rw [zero_smul])]
  rw [MonoidAlgebra.GroupSMul.linearMap_apply, Finsupp.linearCombination_single,
    TensorProduct.mk_apply, diagModule_single_tmul]
  simp

/-- The basis expansion of an element of `M` in the basis `dsB`. -/
theorem linearCombination_repr_dsB (y : M) :
    (Finsupp.linearCombination K dsB) (dsB.repr.toLinearMap y) = y := by
  rw [← Module.Basis.repr_symm_apply]
  exact LinearEquiv.symm_apply_apply dsB.repr y

/-- The key computation: `dsEinv` is a left inverse of `dsE` on a spanning family. -/
theorem dsEinv_dsVtens (h : G) (m : M) :
    dsEinv (dsVtens (K := K) (G := G) (M := M) h m) =
      MonoidAlgebra.single h (1 : K) ⊗ₜ[K] m := by
  have hLR := dsEinv_mapRange_lsingle (K := K) (G := G) (M := M) h
  have hconv : (Finsupp.linearCombination K dsB)
      (dsB.repr.toLinearMap ((MonoidAlgebra.GroupSMul.linearMap K M h⁻¹) m)) =
        (MonoidAlgebra.GroupSMul.linearMap K M h⁻¹) m :=
    linearCombination_repr_dsB _
  have hcancel : MonoidAlgebra.single h (1 : K) •
      (MonoidAlgebra.single h⁻¹ (1 : K) • m) = m := by
    rw [← mul_smul, MonoidAlgebra.single_mul_single, mul_one, mul_inv_cancel,
      ← MonoidAlgebra.one_def, one_smul]
  have h1 : dsEinv (dsVtens (K := K) (G := G) (M := M) h m) =
      (dsEinv.comp
        (Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle (S := K) (M := G) h)))
        (dsB.repr.toLinearMap ((MonoidAlgebra.GroupSMul.linearMap K M h⁻¹) m)) := rfl
  rw [h1, hLR]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hconv,
    MonoidAlgebra.GroupSMul.linearMap_apply, MonoidAlgebra.GroupSMul.linearMap_apply,
    TensorProduct.mk_apply, hcancel]

/-- Every `single h 1 ⊗ m` lies in the basis `dsE0`. -/
theorem dsE0_apply (h : G) (i : Module.Free.ChooseBasisIndex K M) :
    dsE0 (K := K) (G := G) (M := M) (h, i) =
      MonoidAlgebra.single h (1 : K) ⊗ₜ[K] dsB i := by
  rw [dsE0, Module.Basis.tensorProduct_apply]
  rfl

theorem diagTensor_einvE {K : Type v} [Field K] {G : Type u} [Group G] {M : Type (max u v)}
    [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [IsScalarTower K (MonoidAlgebra K G) M]
    (x : TensorProduct K (MonoidAlgebra K G) M) :
    Work.ORLyndon.dsEinv (Work.ORLyndon.dsE x) = x := by
  have key : ∀ (h : G) (m : M),
      dsEinv (dsE (MonoidAlgebra.single h (1 : K) ⊗ₜ[K] m)) =
        MonoidAlgebra.single h (1 : K) ⊗ₜ[K] m := by
    intro h m
    rw [dsE_single_tmul]
    exact dsEinv_dsVtens h m
  have hmap : dsEinv.comp dsE =
      (LinearMap.id : TensorProduct K (MonoidAlgebra K G) M →ₗ[K]
        TensorProduct K (MonoidAlgebra K G) M) := by
    apply Module.Basis.ext (dsE0 (K := K) (G := G) (M := M))
    rintro ⟨h, i⟩
    rw [LinearMap.comp_apply, LinearMap.id_apply, dsE0_apply]
    exact key h (dsB i)
  change (dsEinv.comp dsE) x = x
  rw [hmap]
  rfl

end Work.ORLyndon
