/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The unit isomorphism `M ⊠[R] R ≃ M` for the balanced tensor product

For a ring `R` and a right `R`-module `M` (i.e. a left `Rᵐᵒᵖ`-module), the balanced tensor product
`M ⊠[R] R` of `M` with `R` (viewed as a left `R`-module) is canonically isomorphic to `M`, via
`m ⊠ r ↦ m·r` (that is `m ⊠ r ↦ op r • m`).

The construction is carried out here in the ambient `ℤ`-linear setting: the map `m ⊗[ℤ] r ↦ m·r`
factors through the quotient defining `M ⊠[R] R`, and the resulting `ℤ`-linear map is upgraded to
an `Rᵐᵒᵖ`-linear equivalence with inverse `m ↦ m ⊠ 1`.  Here the `Rᵐᵒᵖ`-module structure on
`M ⊠[R] R` is the one induced by the right regular `R`-module structure on the second variable.
-/
import Mathlib
import Submission.Work.ORHomAlg.Map

@[expose] public section

namespace Work.ORHomAlg

open scoped TensorProduct

namespace BalancedTensor

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The additive map `M →+ (R →+ M)`, `m ↦ (r ↦ op r • m)`, i.e. `m ↦ (r ↦ m·r)`. -/
def selfLeftHom : M →+ (R →+ M) where
  toFun m :=
    { toFun := fun r => MulOpposite.op r • m
      map_zero' := by simp
      map_add' := fun a b => by rw [MulOpposite.op_add, add_smul] }
  map_zero' := by ext r; simp
  map_add' m₁ m₂ := by ext r; exact smul_add _ _ _

@[simp]
theorem selfLeftHom_apply (m : M) (r : R) : selfLeftHom m r = MulOpposite.op r • m := rfl

/-- The `ℤ`-linear map `M ⊗[ℤ] R → M`, `m ⊗ r ↦ m·r`, descended to `M ⊠[R] R`. -/
noncomputable def selfLeftLift : BalancedTensor R M R →ₗ[ℤ] M :=
  lift selfLeftHom (fun m r n => by
    show MulOpposite.op n • (MulOpposite.op r • m) = MulOpposite.op (r * n) • m
    rw [← mul_smul, MulOpposite.op_mul])

@[simp]
theorem selfLeftLift_tmul (m : M) (r : R) :
    selfLeftLift (tmul R m r) = MulOpposite.op r • m :=
  lift_tmul _ _ m r

/-- The `Rᵐᵒᵖ`-linear map `M → M ⊠[R] R`, `m ↦ m ⊠ 1`. -/
def selfLeftBack : M →ₗ[Rᵐᵒᵖ] BalancedTensor R M R where
  toFun m := tmul R m 1
  map_add' m₁ m₂ := by rw [tmul_add]
  map_smul' t m := by
    show tmul R (t • m) 1 = t • tmul R m 1
    rw [smul_tmul_right]
    have h1 : t • m = MulOpposite.op (MulOpposite.unop t) • m := by rw [MulOpposite.op_unop]
    have h2 : t • (1 : R) = MulOpposite.unop t := by
      conv_lhs => rw [← MulOpposite.op_unop t]
      rw [op_smul_eq_mul, one_mul]
    rw [h1, h2, tmul_smul]
    simp

@[simp]
theorem selfLeftBack_apply (m : M) : selfLeftBack (R := R) m = tmul R m 1 := rfl

@[simp]
theorem selfLeftLift_selfLeftBack (m : M) : selfLeftLift (selfLeftBack (R := R) m) = m := by
  show selfLeftLift (tmul R m 1) = m
  rw [selfLeftLift_tmul, MulOpposite.op_one, one_smul]

@[simp]
theorem selfLeftBack_selfLeftLift (x : BalancedTensor R M R) :
    selfLeftBack (R := R) (selfLeftLift x) = x := by
  refine induction_on x ?_ ?_ ?_
  · simp
  · intro a b ha hb; rw [map_add, map_add, ha, hb]
  · intro m r
    rw [selfLeftLift_tmul]
    show selfLeftBack (R := R) (MulOpposite.op r • m) = tmul R m r
    rw [selfLeftBack_apply, tmul_smul]
    simp

/-- `selfLeftLift` is `Rᵐᵒᵖ`-linear. -/
theorem selfLeftLift_smul (t : Rᵐᵒᵖ) (x : BalancedTensor R M R) :
    selfLeftLift (t • x) = t • selfLeftLift x := by
  refine induction_on x ?_ ?_ ?_
  · simp
  · intro a b ha hb; rw [smul_add, map_add, ha, hb, map_add, smul_add]
  · intro m r
    rw [smul_tmul_right, selfLeftLift_tmul, selfLeftLift_tmul]
    rw [← MulOpposite.op_unop t, op_smul_eq_mul, ← mul_smul, MulOpposite.op_mul]

/-- The unit isomorphism `M ⊠[R] R ≃ M` of the balanced tensor product, `m ⊠ r ↦ m·r`. -/
noncomputable def selfLeftEquiv : BalancedTensor R M R ≃ₗ[Rᵐᵒᵖ] M where
  toFun := selfLeftLift
  invFun := selfLeftBack
  left_inv := selfLeftBack_selfLeftLift
  right_inv := selfLeftLift_selfLeftBack
  map_add' := map_add _
  map_smul' := selfLeftLift_smul

@[simp]
theorem selfLeftEquiv_apply (x : BalancedTensor R M R) : selfLeftEquiv x = selfLeftLift x := rfl

@[simp]
theorem selfLeftEquiv_symm_apply (m : M) : selfLeftEquiv.symm m = tmul R m 1 := rfl

@[simp]
theorem selfLeftEquiv_tmul (m : M) (r : R) : selfLeftEquiv (tmul R m r) = MulOpposite.op r • m :=
  selfLeftLift_tmul m r

end BalancedTensor

namespace TensorIsos

/-- The unit isomorphism `M ⊠[R] R ≃ M` for the balanced tensor product, as right modules. -/
theorem tensorSelfLeft {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Nonempty (Work.ORHomAlg.BalancedTensor R M R ≃ₗ[Rᵐᵒᵖ] M) :=
  ⟨BalancedTensor.selfLeftEquiv⟩

end TensorIsos

end Work.ORHomAlg
