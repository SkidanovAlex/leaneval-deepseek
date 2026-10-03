/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Functoriality of the balanced tensor product

This file gives the functoriality of `M ⊠[R] N` in both variables
(`Work.ORHomAlg.BalancedTensor.map`) together with its basic API, and the induced module
structures: if `M` is an `(S,R)`-bimodule then `M ⊠[R] N` is a left `S`-module, and if `N` is an
`(R,T)`-bimodule then `M ⊠[R] N` is a right `T`-module.
-/
module

public import Submission.Work.ORHomAlg.Basic

@[expose] public section

namespace Work.ORHomAlg

open scoped TensorProduct

universe u v w v' w' u₁ u₂


namespace BalancedTensor

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {N : Type w} [AddCommGroup N] [Module R N]

@[simp]
theorem tmulAddHom_apply (m : M) (n : N) : tmulAddHom R m n = tmul R m n := rfl

section Map

variable {M' : Type v'} [AddCommGroup M'] [Module Rᵐᵒᵖ M']
variable {N' : Type w'} [AddCommGroup N'] [Module R N']

/-- The `ℤ`-linear map `M ⊗[ℤ] N → M' ⊠[R] N'` underlying `map`. -/
noncomputable def mapLinearMap (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    M ⊗[ℤ] N →ₗ[ℤ] BalancedTensor R M' N' :=
  (balancedRel R M' N').mkQ.comp
    (TensorProduct.map (f.toAddMonoidHom.toIntLinearMap) (g.toAddMonoidHom.toIntLinearMap))

theorem mapLinearMap_apply (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') (x : M ⊗[ℤ] N) :
    mapLinearMap f g x = Submodule.Quotient.mk (p := balancedRel R M' N')
      (TensorProduct.map (f.toAddMonoidHom.toIntLinearMap) (g.toAddMonoidHom.toIntLinearMap) x) :=
  rfl

@[simp]
theorem mapLinearMap_tmul (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') (m : M) (n : N) :
    mapLinearMap f g (m ⊗ₜ[ℤ] n) = tmul R (f m) (g n) := by
  simp only [mapLinearMap_apply, TensorProduct.map_tmul, tmul_def]
  rfl

/-- Functoriality of the balanced tensor product in both variables. -/
noncomputable def map (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    BalancedTensor R M N →+ BalancedTensor R M' N' :=
  ((balancedRel R M N).liftQ (R₂ := ℤ) (mapLinearMap f g) (by
    unfold balancedRel
    rw [Submodule.span_le]
    rintro x ⟨m, r, n, rfl⟩
    change mapLinearMap f g ((MulOpposite.op r • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (r • n)) = 0
    rw [map_sub, mapLinearMap_tmul, mapLinearMap_tmul, f.map_smul, g.map_smul, tmul_smul,
      sub_self])).toAddMonoidHom

@[simp]
theorem map_tmul (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') (m : M) (n : N) :
    map f g (tmul R m n) = tmul R (f m) (g n) := by
  have h1 : map f g (tmul R m n) = mapLinearMap f g (m ⊗ₜ[ℤ] n) := rfl
  rw [h1, mapLinearMap_tmul]

@[simp]
theorem map_id :
    map (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) (LinearMap.id : N →ₗ[R] N) =
      AddMonoidHom.id (BalancedTensor R M N) :=
  hom_ext fun m n => by simp

@[simp]
theorem map_zero_left (g : N →ₗ[R] N') : map (0 : M →ₗ[Rᵐᵒᵖ] M') g = 0 :=
  hom_ext fun m n => by simp

@[simp]
theorem map_zero_right (f : M →ₗ[Rᵐᵒᵖ] M') : map f (0 : N →ₗ[R] N') = 0 :=
  hom_ext fun m n => by simp

@[simp]
theorem map_add_left (f₁ f₂ : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    map (f₁ + f₂) g = map f₁ g + map f₂ g :=
  hom_ext fun m n => by simp

@[simp]
theorem map_add_right (f : M →ₗ[Rᵐᵒᵖ] M') (g₁ g₂ : N →ₗ[R] N') :
    map f (g₁ + g₂) = map f g₁ + map f g₂ :=
  hom_ext fun m n => by simp

/-- The map induced by a map of the second variable: `M ⊠[R] -`. -/
noncomputable def lTensor (g : N →ₗ[R] N') :
    BalancedTensor R M N →+ BalancedTensor R M N' :=
  map (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g

@[simp]
theorem lTensor_tmul (g : N →ₗ[R] N') (m : M) (n : N) :
    lTensor g (tmul R m n) = tmul R m (g n) := by
  simp [lTensor]

@[simp]
theorem lTensor_add {N₁ : Type w} [AddCommGroup N₁] [Module R N₁] (g₁ g₂ : N →ₗ[R] N₁) :
    lTensor (M := M) (g₁ + g₂) = lTensor (M := M) g₁ + lTensor (M := M) g₂ :=
  map_add_right (M := M) (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g₁ g₂

@[simp]
theorem lTensor_id :
    lTensor (R := R) (M := M) (N := N) (LinearMap.id : N →ₗ[R] N) =
      AddMonoidHom.id (BalancedTensor R M N) := by
  apply hom_ext
  intro m n
  simp

theorem lTensor_comp {N'' : Type w'} [AddCommGroup N''] [Module R N'']
    (g' : N' →ₗ[R] N'') (g : N →ₗ[R] N') :
    lTensor (M := M) (g'.comp g) = (lTensor (M := M) g').comp (lTensor (M := M) g) := by
  apply hom_ext
  intro m n
  simp

/-- The map induced by a map of the first variable: `- ⊠[R] N`. -/
noncomputable def rTensor (f : M →ₗ[Rᵐᵒᵖ] M') :
    BalancedTensor R M N →+ BalancedTensor R M' N :=
  map f (LinearMap.id : N →ₗ[R] N)

@[simp]
theorem rTensor_tmul (f : M →ₗ[Rᵐᵒᵖ] M') (m : M) (n : N) :
    rTensor f (tmul R m n) = tmul R (f m) n := by
  simp [rTensor]

theorem map_comp {M'' : Type*} [AddCommGroup M''] [Module Rᵐᵒᵖ M'']
    {N'' : Type*} [AddCommGroup N''] [Module R N'']
    (f' : M' →ₗ[Rᵐᵒᵖ] M'') (g' : N' →ₗ[R] N'') (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) :=
  hom_ext fun m n => by simp

end Map

section BimoduleLeft

variable {S : Type u₁} [Semiring S] [Module S M] [SMulCommClass S Rᵐᵒᵖ M]

/-- Left multiplication by `s` as an `Rᵐᵒᵖ`-linear endomorphism of `M`. -/
def smulLinear (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {S : Type u₁} [Semiring S] [Module S M] [SMulCommClass S Rᵐᵒᵖ M] (s : S) : M →ₗ[Rᵐᵒᵖ] M where
  toFun m := s • m
  map_add' a b := smul_add s a b
  map_smul' r m := smul_comm s r m

@[simp]
theorem smulLinear_apply (s : S) (m : M) : smulLinear R M s m = s • m := rfl

theorem smulLinear_one : smulLinear R M (1 : S) = (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) := by
  ext m; simp

theorem smulLinear_mul (s t : S) :
    smulLinear R M (s * t) = (smulLinear R M s).comp (smulLinear R M t) := by
  ext m; simp [mul_smul]

theorem smulLinear_add (s t : S) :
    smulLinear R M (s + t) = smulLinear R M s + smulLinear R M t := by
  ext m; simp [add_smul]

theorem smulLinear_zero : smulLinear R M (0 : S) = 0 := by
  ext m; simp

/-- The left `S`-action on `M ⊠[R] N` when `M` is an `(S,R)`-bimodule. -/
noncomputable def smulMap (s : S) : BalancedTensor R M N →+ BalancedTensor R M N :=
  map (smulLinear R M s) (LinearMap.id : N →ₗ[R] N)

theorem smulMap_one : smulMap (R := R) (M := M) (N := N) (1 : S) = AddMonoidHom.id (BalancedTensor R M N) := by
  simp only [smulMap, smulLinear_one, map_id]

theorem smulMap_mul (s t : S) :
    smulMap (R := R) (M := M) (N := N) (s * t) = (smulMap (R := R) (M := M) (N := N) s).comp (smulMap (R := R) (M := M) (N := N) t) := by
  simp only [smulMap, smulLinear_mul]
  rw [← map_comp (f' := smulLinear R M s) (f := smulLinear R M t)
    (g' := (LinearMap.id : N →ₗ[R] N)) (g := (LinearMap.id : N →ₗ[R] N))]
  simp

theorem smulMap_add (s t : S) :
    smulMap (R := R) (M := M) (N := N) (s + t) = smulMap (R := R) (M := M) (N := N) s + smulMap (R := R) (M := M) (N := N) t := by
  simp only [smulMap, smulLinear_add, map_add_left]

theorem smulMap_zero : smulMap (R := R) (M := M) (N := N) (0 : S) = 0 := by
  simp only [smulMap, smulLinear_zero, map_zero_left]

noncomputable instance instSMulS : SMul S (BalancedTensor R M N) := ⟨fun s x => smulMap s x⟩

@[simp]
theorem smul_tmul (s : S) (m : M) (n : N) : s • tmul R m n = tmul R (s • m) n := by
  show smulMap s (tmul R m n) = tmul R (s • m) n
  simp [smulMap]

noncomputable instance instModuleS : Module S (BalancedTensor R M N) where
  smul := fun s x => smulMap s x
  one_smul x := by show smulMap 1 x = x; rw [smulMap_one]; rfl
  mul_smul s t x := by show smulMap (s * t) x = smulMap s (smulMap t x); rw [smulMap_mul]; rfl
  smul_zero s := by show smulMap s 0 = 0; exact map_zero _
  smul_add s x y := by
    show smulMap s (x + y) = smulMap s x + smulMap s y
    exact map_add _ _ _
  add_smul s t x := by show smulMap (s + t) x = smulMap s x + smulMap t x; rw [smulMap_add]; rfl
  zero_smul x := by show smulMap 0 x = 0; rw [smulMap_zero]; rfl

end BimoduleLeft

section BimoduleRight

variable {T : Type u₂} [Semiring T] [Module Tᵐᵒᵖ N] [SMulCommClass R Tᵐᵒᵖ N]

/-- Multiplication by `t` on the right as an `R`-linear endomorphism of `N`. -/
def smulRightLinear (R : Type u) [Ring R] (N : Type w) [AddCommGroup N] [Module R N]
    {T : Type u₂} [Semiring T] [Module Tᵐᵒᵖ N] [SMulCommClass R Tᵐᵒᵖ N] (t : Tᵐᵒᵖ) :
    N →ₗ[R] N where
  toFun n := t • n
  map_add' a b := smul_add t a b
  map_smul' r n := (SMulCommClass.symm R Tᵐᵒᵖ N).smul_comm t r n

@[simp]
theorem smulRightLinear_apply (t : Tᵐᵒᵖ) (n : N) : smulRightLinear R N t n = t • n := rfl

theorem smulRightLinear_one : smulRightLinear R N (1 : Tᵐᵒᵖ) = (LinearMap.id : N →ₗ[R] N) := by
  ext n; simp

theorem smulRightLinear_mul (s t : Tᵐᵒᵖ) :
    smulRightLinear R N (s * t) = (smulRightLinear R N s).comp (smulRightLinear R N t) := by
  ext n; simp [mul_smul]

theorem smulRightLinear_add (s t : Tᵐᵒᵖ) :
    smulRightLinear R N (s + t) = smulRightLinear R N s + smulRightLinear R N t := by
  ext n; simp [add_smul]

theorem smulRightLinear_zero : smulRightLinear R N (0 : Tᵐᵒᵖ) = 0 := by
  ext n; simp

/-- The right `T`-action on `M ⊠[R] N` when `N` is an `(R,T)`-bimodule. -/
noncomputable def smulRightMap (t : Tᵐᵒᵖ) : BalancedTensor R M N →+ BalancedTensor R M N :=
  map (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) (smulRightLinear R N t)

theorem smulRightMap_one :
    smulRightMap (R := R) (M := M) (N := N) (1 : Tᵐᵒᵖ) = AddMonoidHom.id (BalancedTensor R M N) := by
  simp only [smulRightMap, smulRightLinear_one, map_id]

theorem smulRightMap_mul (s t : Tᵐᵒᵖ) :
    smulRightMap (R := R) (M := M) (N := N) (s * t) =
      (smulRightMap (R := R) (M := M) (N := N) s).comp (smulRightMap (R := R) (M := M) (N := N) t) := by
  simp only [smulRightMap, smulRightLinear_mul]
  rw [← map_comp (f' := (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M)) (f := (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M))
    (g' := smulRightLinear R N s) (g := smulRightLinear R N t)]
  simp

theorem smulRightMap_add (s t : Tᵐᵒᵖ) :
    smulRightMap (R := R) (M := M) (N := N) (s + t) = smulRightMap (R := R) (M := M) (N := N) s + smulRightMap (R := R) (M := M) (N := N) t := by
  simp only [smulRightMap, smulRightLinear_add, map_add_right]

theorem smulRightMap_zero : smulRightMap (R := R) (M := M) (N := N) (0 : Tᵐᵒᵖ) = 0 := by
  simp only [smulRightMap, smulRightLinear_zero, map_zero_right]

noncomputable instance instSMulTop : SMul Tᵐᵒᵖ (BalancedTensor R M N) :=
  ⟨fun t x => smulRightMap t x⟩

@[simp]
theorem smul_tmul_right (t : Tᵐᵒᵖ) (m : M) (n : N) :
    t • tmul R m n = tmul R m (t • n) := by
  show smulRightMap t (tmul R m n) = tmul R m (t • n)
  simp [smulRightMap]

noncomputable instance instModuleTop : Module Tᵐᵒᵖ (BalancedTensor R M N) where
  smul := fun t x => smulRightMap t x
  one_smul x := by show smulRightMap 1 x = x; rw [smulRightMap_one]; rfl
  mul_smul s t x := by
    show smulRightMap (s * t) x = smulRightMap s (smulRightMap t x); rw [smulRightMap_mul]; rfl
  smul_zero s := by show smulRightMap s 0 = 0; exact map_zero _
  smul_add s x y := by
    show smulRightMap s (x + y) = smulRightMap s x + smulRightMap s y
    exact map_add _ _ _
  add_smul s t x := by
    show smulRightMap (s + t) x = smulRightMap s x + smulRightMap t x; rw [smulRightMap_add]; rfl
  zero_smul x := by show smulRightMap 0 x = 0; rw [smulRightMap_zero]; rfl

end BimoduleRight

section Commute

variable {S : Type u₁} [Semiring S] [Module S M] [SMulCommClass S Rᵐᵒᵖ M]
variable {T : Type u₂} [Semiring T] [Module Tᵐᵒᵖ N] [SMulCommClass R Tᵐᵒᵖ N]

theorem smul_comm' (s : S) (t : Tᵐᵒᵖ) (x : BalancedTensor R M N) :
    s • (t • x) = t • (s • x) := by
  refine induction_on x ?_ ?_ ?_
  · rw [smul_zero, smul_zero, smul_zero]
  · intro a b ha hb
    rw [smul_add, smul_add, smul_add, smul_add, ha, hb]
  · intro m n
    rw [smul_tmul_right, smul_tmul, smul_tmul, smul_tmul_right]

instance instSMulCommClass : SMulCommClass S Tᵐᵒᵖ (BalancedTensor R M N) where
  smul_comm s t x := smul_comm' s t x

end Commute

end BalancedTensor

end Work.ORHomAlg
