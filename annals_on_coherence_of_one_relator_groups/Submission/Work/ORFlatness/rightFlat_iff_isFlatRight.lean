import Mathlib
import Submission.Work.ORHomAlg.Flat
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Tensor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

/-- The balancing relations defining the balanced tensor product of `Submission.Work.ORFlatness`
and of `Submission.Work.ORHomAlg` coincide, as `ℤ`-submodules of `X ⊗[ℤ] N`. -/
private theorem balRel_eq_balancedRel_aux (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (N : Type u) [AddCommGroup N] [Module R N] :
    balRel R X N = Work.ORHomAlg.balancedRel R X N := by
  apply le_antisymm
  · rw [balRel_le_iff]
    intro x n r
    exact Submodule.subset_span ⟨x, r, n, rfl⟩
  · rw [Work.ORHomAlg.balancedRel, Submodule.span_le]
    rintro y ⟨m, r, n, rfl⟩
    exact Submodule.subset_span ⟨(m, n, r), rfl⟩

/-- Injectivity is invariant under conjugation by equivalences: if `f` and `g` are related by
`eβ (f a) = g (eα a)`, then `f` is injective iff `g` is. -/
private theorem injective_congr_equiv_aux {α α' β β' : Type*}
    (eα : α ≃ α') (eβ : β ≃ β') {f : α → β} {g : α' → β'}
    (h : ∀ a, eβ (f a) = g (eα a)) : Function.Injective f ↔ Function.Injective g := by
  constructor
  · intro hf a b hab
    have h1f : f (eα.symm a) = f (eα.symm b) := by
      apply eβ.injective
      rw [h (eα.symm a), h (eα.symm b), eα.apply_symm_apply, eα.apply_symm_apply, hab]
    have h2 : eα.symm a = eα.symm b := hf h1f
    calc a = eα (eα.symm a) := (eα.apply_symm_apply a).symm
      _ = eα (eα.symm b) := by rw [h2]
      _ = b := eα.apply_symm_apply b
  · intro hg a b hab
    have h1 : g (eα a) = g (eα b) := by rw [← h a, ← h b, hab]
    exact eα.injective (hg h1)

/-- Tensoring on the left with `X`, computed in the two balanced tensor products of the
workspace, gives conjugate maps, hence the same injectivity statement. -/
private theorem injective_map_iff_aux (R : Type u) [Ring R] {X : Type u} [AddCommGroup X]
    [Module Rᵐᵒᵖ X] {M : Type u} [AddCommGroup M] [Module R M] {N : Type u} [AddCommGroup N]
    [Module R N] (g : M →ₗ[R] N) :
    Function.Injective (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g) ↔
    Function.Injective (Work.ORHomAlg.BalancedTensor.lTensor (M := X) g) := by
  have hM : balRel R X M = Work.ORHomAlg.balancedRel R X M := balRel_eq_balancedRel_aux R X M
  have hN : balRel R X N = Work.ORHomAlg.balancedRel R X N := balRel_eq_balancedRel_aux R X N
  let eM : BalTensor R X M ≃ₗ[ℤ] Work.ORHomAlg.BalancedTensor R X M :=
    Submodule.quotEquivOfEq (balRel R X M) (Work.ORHomAlg.balancedRel R X M) hM
  let eN : BalTensor R X N ≃ₗ[ℤ] Work.ORHomAlg.BalancedTensor R X N :=
    Submodule.quotEquivOfEq (balRel R X N) (Work.ORHomAlg.balancedRel R X N) hN
  have heM : ∀ (x : X) (m : M), eM (BalTensor.mk R x m) =
      Work.ORHomAlg.BalancedTensor.tmul R x m := by
    intro x m
    change Submodule.quotEquivOfEq (balRel R X M) (Work.ORHomAlg.balancedRel R X M) hM
        (Submodule.Quotient.mk (p := balRel R X M) (x ⊗ₜ[ℤ] m)) =
      Submodule.Quotient.mk (p := Work.ORHomAlg.balancedRel R X M) (x ⊗ₜ[ℤ] m)
    rw [Submodule.quotEquivOfEq_mk]
  have heN : ∀ (x : X) (n : N), eN (BalTensor.mk R x n) =
      Work.ORHomAlg.BalancedTensor.tmul R x n := by
    intro x n
    change Submodule.quotEquivOfEq (balRel R X N) (Work.ORHomAlg.balancedRel R X N) hN
        (Submodule.Quotient.mk (p := balRel R X N) (x ⊗ₜ[ℤ] n)) =
      Submodule.Quotient.mk (p := Work.ORHomAlg.balancedRel R X N) (x ⊗ₜ[ℤ] n)
    rw [Submodule.quotEquivOfEq_mk]
  have hkey : (eN.toAddMonoidHom.comp
        (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g)) =
      ((Work.ORHomAlg.BalancedTensor.lTensor (M := X) g).comp eM.toAddMonoidHom) := by
    apply BalTensor.ext R
    intro x m
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, BalTensor.map_mk]
    change eN (BalTensor.mk R x (g m)) =
      Work.ORHomAlg.BalancedTensor.lTensor (M := X) g (eM (BalTensor.mk R x m))
    rw [heM, heN, Work.ORHomAlg.BalancedTensor.lTensor_tmul]
  exact injective_congr_equiv_aux eM.toEquiv eN.toEquiv
    (fun a => DFunLike.congr_fun hkey a)

/-- The right-module counterpart of `Work.ORFlatness.leftFlat_iff_isFlatLeft`: the balanced tensor products of this area and of `Work.ORHomAlg` agree (`Work.ORFlatness.balRel = Work.ORHomAlg.balancedRel`), hence so do the flatness notions for a right `R`-module `X`:

`Work.ORFlatness.RightFlat R X ↔ Work.ORHomAlg.IsFlatRight R X`.

(`Work.ORFlatness.RightFlat R X` says that tensoring on the left with `X` preserves monomorphisms of left modules, `Work.ORHomAlg.IsFlatRight R X` that the functor `X ⊠[R] -` preserves them; the two functors agree by the identification of the two balanced tensor products, `Work.ORFlatness.BalTensor.map R (LinearMap.id) g = Work.ORHomAlg.BalancedTensor.lTensor g` on generators.) -/
theorem rightFlat_iff_isFlatRight (R : Type u) [Ring R] {X : Type u} [AddCommGroup X]
    [Module Rᵐᵒᵖ X] :
    Work.ORFlatness.RightFlat R X ↔ Work.ORHomAlg.IsFlatRight R X := by
  constructor
  · intro h N N' _ _ _ _ g hg
    exact (injective_map_iff_aux R (X := X) (M := N) (N := N') g).mp (h g hg)
  · intro h M N _ _ _ _ g hg
    exact (injective_map_iff_aux R (X := X) (M := M) (N := N) g).mpr (h g hg)

end Work.ORFlatness
