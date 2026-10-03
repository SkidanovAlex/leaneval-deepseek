import Mathlib
import Submission.Work.ORHomAlg.Tor
import Submission.Work.ORHomAlg.Basic
import Submission.Work.ORHomAlg.Map

namespace Work.ORBridgeTor

/-!
Route hint: `Work.ORHomAlg.Tor R n M N = ((tensorLeftFunctor R M).leftDerived n).obj (ModuleCat.of R N)`.
Build the natural isomorphism `tensorLeftFunctor R L ≅ tensorLeftFunctor R L'` from `eL`
(naturality is checked on pure tensors, via `BalancedTensor.map`/`lTensor` API), take its
`NatTrans.leftDerived n`, and evaluate at `ModuleCat.of R N`; then apply `mapIso` for `eN`
(`ModuleCat.isoOfLinearEquiv` / `ModuleCat.ofHom` of `eN`).
-/
open TensorProduct MulOpposite

universe u

open Work.ORHomAlg CategoryTheory

variable {R : Type u} [Ring R]
variable {L : Type u} [AddCommGroup L] [Module Rᵐᵒᵖ L]
variable {L' : Type u} [AddCommGroup L'] [Module Rᵐᵒᵖ L']

section Basic

/-- Composition of the maps induced by a map of the first variable of the balanced tensor
product. -/
theorem rTensor_comp {N : Type u} [AddCommGroup N] [Module R N]
    {L'' : Type u} [AddCommGroup L''] [Module Rᵐᵒᵖ L'']
    (f : L' →ₗ[Rᵐᵒᵖ] L'') (g : L →ₗ[Rᵐᵒᵖ] L') :
    (BalancedTensor.rTensor (M := L') (N := N) f).comp
        (BalancedTensor.rTensor (M := L) (N := N) g) =
      BalancedTensor.rTensor (M := L) (N := N) (f.comp g) := by
  apply BalancedTensor.hom_ext
  intro m n
  simp

/-- The maps induced by the first variable and by the second variable of the balanced tensor
product commute. -/
theorem rTensor_lTensor_comm {N₁ : Type u} [AddCommGroup N₁] [Module R N₁]
    {N₂ : Type u} [AddCommGroup N₂] [Module R N₂]
    (f : L →ₗ[Rᵐᵒᵖ] L') (g : N₁ →ₗ[R] N₂) :
    (BalancedTensor.rTensor (M := L) (N := N₂) f).comp
        (BalancedTensor.lTensor (M := L) (N := N₁) g) =
      (BalancedTensor.lTensor (M := L') (N := N₁) g).comp
        (BalancedTensor.rTensor (M := L) (N := N₁) f) := by
  apply BalancedTensor.hom_ext
  intro m n
  simp

variable (e : L ≃ₗ[Rᵐᵒᵖ] L')

/-- `rTensor e` followed by `rTensor e.symm` is the identity. -/
theorem rTensor_comp_symm {N : Type u} [AddCommGroup N] [Module R N] :
    (BalancedTensor.rTensor (M := L') (N := N) e.symm.toLinearMap).comp
        (BalancedTensor.rTensor (M := L) (N := N) e.toLinearMap) =
      AddMonoidHom.id _ := by
  rw [rTensor_comp]
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [h]
  simp [BalancedTensor.rTensor]

/-- `rTensor e.symm` followed by `rTensor e` is the identity. -/
theorem rTensor_comp_symm' {N : Type u} [AddCommGroup N] [Module R N] :
    (BalancedTensor.rTensor (M := L) (N := N) e.toLinearMap).comp
        (BalancedTensor.rTensor (M := L') (N := N) e.symm.toLinearMap) =
      AddMonoidHom.id _ := by
  rw [rTensor_comp]
  have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [h]
  simp [BalancedTensor.rTensor]

/-- The `ℤ`-linear equivalence `L ⊠[R] N ≃ L' ⊠[R] N` induced by a linear equivalence
`e : L ≃ₗ[Rᵐᵒᵖ] L'`. -/
noncomputable def tensorRMapEquiv (N : Type u) [AddCommGroup N] [Module R N] :
    BalancedTensor R L N ≃ₗ[ℤ] BalancedTensor R L' N where
  toFun := BalancedTensor.rTensor (M := L) (N := N) e.toLinearMap
  invFun := BalancedTensor.rTensor (M := L') (N := N) e.symm.toLinearMap
  left_inv x := by
    have h := DFunLike.congr_fun (rTensor_comp_symm (N := N) e) x
    simpa using h
  right_inv x := by
    have h := DFunLike.congr_fun (rTensor_comp_symm' (N := N) e) x
    simpa using h
  map_add' := map_add _
  map_smul' := map_zsmul _

/-- The natural isomorphism `tensorLeftFunctor R L ≅ tensorLeftFunctor R L'` induced by a linear
equivalence `L ≃ₗ[Rᵐᵒᵖ] L'`. -/
noncomputable def tensorLeftFunctorIso :
    tensorLeftFunctor (R := R) L ≅ tensorLeftFunctor (R := R) L' :=
  NatIso.ofComponents (fun X => LinearEquiv.toModuleIso (tensorRMapEquiv e X)) (fun {X Y} f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show BalancedTensor.rTensor (M := L) (N := ↑Y) e.toLinearMap
        (BalancedTensor.lTensor (M := L) (N := ↑X) (ModuleCat.Hom.hom f) x) =
      BalancedTensor.lTensor (M := L') (N := ↑X) (ModuleCat.Hom.hom f)
        (BalancedTensor.rTensor (M := L) (N := ↑X) e.toLinearMap x)
    exact DFunLike.congr_fun
      (rTensor_lTensor_comm (N₁ := ↑X) (N₂ := ↑Y) e.toLinearMap (ModuleCat.Hom.hom f)) x)

end Basic

theorem torEquivOfEquiv (R : Type u) [Ring R]
    {L L' : Type u} [AddCommGroup L] [Module Rᵐᵒᵖ L] [AddCommGroup L'] [Module Rᵐᵒᵖ L']
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (eL : L ≃ₗ[Rᵐᵒᵖ] L') (eN : N ≃ₗ[R] N') (n : ℕ) :
    Nonempty (Work.ORHomAlg.Tor (R := R) n L N ≃ₗ[ℤ] Work.ORHomAlg.Tor (R := R) n L' N') := by
  -- Natural isomorphisms of functors induce isomorphisms of their left derived functors.
  let α : tensorLeftFunctor (R := R) L ≅ tensorLeftFunctor (R := R) L' :=
    tensorLeftFunctorIso eL
  let β : ((tensorLeftFunctor (R := R) L).leftDerived n) ≅
      ((tensorLeftFunctor (R := R) L').leftDerived n) :=
    { hom := NatTrans.leftDerived α.hom n
      inv := NatTrans.leftDerived α.inv n
      hom_inv_id := by
        rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id α, NatTrans.leftDerived_id]
      inv_hom_id := by
        rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id α, NatTrans.leftDerived_id] }
  exact ⟨Iso.toLinearEquiv (β.app (ModuleCat.of R N) ≪≫
    (((tensorLeftFunctor (R := R) L').leftDerived n).mapIso (LinearEquiv.toModuleIso eN)))⟩

end Work.ORBridgeTor
