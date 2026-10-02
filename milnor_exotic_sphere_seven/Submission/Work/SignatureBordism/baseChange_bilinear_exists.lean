import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SignatureBordism

open TensorProduct in
theorem baseChange_bilinear_exists {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : M →ₗ[ℤ] M →ₗ[ℤ] ℤ) :
    ∃ F : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M) →ₗ[ℚ] ℚ,
      ∀ (a b : ℚ) (m n : M), F (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] n) = (a * b) * (B m n : ℚ) := by
  -- The canonical ℤ-linear map `ℤ → ℚ` (casting into `ℚ`).
  let castT : ℤ →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ
  -- The `ℚ`-valued version of `B`: `Bq m n = (B m n : ℚ)`.
  let Bq : M →ₗ[ℤ] M →ₗ[ℤ] ℚ := (LinearMap.compRight ℤ castT).comp B
  -- `k m` is the `ℚ`-linear map `x ↦ x • (Bq m)` into the dual of `M`.
  let k : M →ₗ[ℤ] (ℚ →ₗ[ℚ] (M →ₗ[ℤ] ℚ)) :=
    (LinearMap.restrictScalars ℤ
      ((LinearMap.ringLmapEquivSelf ℚ ℚ (M →ₗ[ℤ] ℚ)).symm).toLinearMap).comp Bq
  -- Base change of `k m` along `ℤ → ℚ`: `h m` is `ℚ`-linear on `ℚ ⊗[ℤ] M`.
  let h : M →ₗ[ℤ] ((ℚ ⊗[ℤ] M) →ₗ[ℚ] ℚ) :=
    (TensorProduct.AlgebraTensorModule.uncurry ℤ ℚ ℤ ℚ M ℚ).comp k
  -- `g` is `ℚ`-linear in its first variable and `ℤ`-linear in the second.
  let g : ℚ →ₗ[ℚ] M →ₗ[ℤ] ((ℚ ⊗[ℤ] M) →ₗ[ℚ] ℚ) :=
    LinearMap.toSpanSingleton ℚ (M →ₗ[ℤ] ((ℚ ⊗[ℤ] M) →ₗ[ℚ] ℚ)) h
  refine ⟨TensorProduct.AlgebraTensorModule.lift g, ?_⟩
  intro a b m n
  have hBq : ∀ (m n : M), Bq m n = (B m n : ℚ) := by
    intro m n
    simp [Bq, castT, LinearMap.compRight_apply, Algebra.linearMap_apply]
  have hk : ∀ (m : M) (x : ℚ) (n : M), (k m) x n = x * (B m n : ℚ) := by
    intro m x n
    have e1 : k m = (LinearMap.restrictScalars ℤ
        ((LinearMap.ringLmapEquivSelf ℚ ℚ (M →ₗ[ℤ] ℚ)).symm).toLinearMap) (Bq m) := rfl
    rw [e1]
    have e2 : (LinearMap.restrictScalars ℤ
        ((LinearMap.ringLmapEquivSelf ℚ ℚ (M →ₗ[ℤ] ℚ)).symm).toLinearMap) (Bq m)
        = LinearMap.toSpanSingleton ℚ (M →ₗ[ℤ] ℚ) (Bq m) := rfl
    rw [e2, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, hBq m n, smul_eq_mul]
  have hh : ∀ (m : M) (x : ℚ) (n : M), h m (x ⊗ₜ[ℤ] n) = x * (B m n : ℚ) := by
    intro m x n
    have e1 : h m = TensorProduct.AlgebraTensorModule.lift (k m) := by
      simp only [h, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.uncurry_apply]
    rw [e1, TensorProduct.AlgebraTensorModule.lift_tmul]
    exact hk m x n
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  have e3 : g a m = a • h m := by
    simp only [g, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply]
  rw [e3, LinearMap.smul_apply, hh m b n, smul_eq_mul, mul_assoc]

end Work.SignatureBordism
