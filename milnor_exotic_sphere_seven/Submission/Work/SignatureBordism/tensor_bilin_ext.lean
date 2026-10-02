import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SignatureBordism

open TensorProduct in
theorem tensor_bilin_ext {M : Type*} [AddCommGroup M] [Module ℤ M]
    {F G : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M) →ₗ[ℚ] ℚ}
    (h : ∀ (a b : ℚ) (m n : M), F (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] n) = G (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] n)) :
    F = G := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b n => exact h a b m n
      | add y z hy hz => simp [map_add, hy, hz]
  | add x z hx hz => simp [map_add, hx, hz]

end Work.SignatureBordism
