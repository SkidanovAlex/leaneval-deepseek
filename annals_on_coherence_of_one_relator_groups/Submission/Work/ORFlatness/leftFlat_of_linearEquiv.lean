import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Tensor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

namespace Work.ORFlatness

universe u

/-- Left flatness of a left `R`-module is invariant under linear equivalence. -/
theorem leftFlat_of_linearEquiv {R : Type u} [Ring R] {M M' : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M')
    (h : Work.ORFlatness.LeftFlat R M) : Work.ORFlatness.LeftFlat R M' := by
  intro X Y _ _ _ _ f hf
  -- `Φ_Z = id_Z ⊗ e : Z ⊗ M → Z ⊗ M'` and `Ψ_Z = id_Z ⊗ e.symm : Z ⊗ M' → Z ⊗ M`
  -- are mutually inverse, and are natural in the right module `Z`.
  have hcomp : ∀ (Z : Type u) [AddCommGroup Z] [Module Rᵐᵒᵖ Z],
      (BalTensor.map R (LinearMap.id : Z →ₗ[Rᵐᵒᵖ] Z) (e : M →ₗ[R] M')).comp
        (BalTensor.map R (LinearMap.id : Z →ₗ[Rᵐᵒᵖ] Z) (e.symm : M' →ₗ[R] M))
      = AddMonoidHom.id _ := by
    intro Z _ _
    apply BalTensor.ext R
    intro x n
    simp
  -- Naturality of `(id ⊗ e.symm)`: `Ψ_Y ∘ (f ⊗ id_{M'}) = f ⊗ e.symm`.
  have hnt1 : (BalTensor.map R (LinearMap.id : Y →ₗ[Rᵐᵒᵖ] Y) (e.symm : M' →ₗ[R] M)).comp
        (BalTensor.map R f (LinearMap.id : M' →ₗ[R] M'))
      = BalTensor.map R f (e.symm : M' →ₗ[R] M) := by
    apply BalTensor.ext R
    intro x n
    simp
  -- Naturality of `(id ⊗ e.symm)`: `(f ⊗ id_M) ∘ Ψ_X = f ⊗ e.symm`.
  have hnt2 : (BalTensor.map R f (LinearMap.id : M →ₗ[R] M)).comp
        (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) (e.symm : M' →ₗ[R] M))
      = BalTensor.map R f (e.symm : M' →ₗ[R] M) := by
    apply BalTensor.ext R
    intro x n
    simp
  have key : ∀ z : BalTensor R X M',
      BalTensor.map R f (LinearMap.id : M' →ₗ[R] M') z = 0 → z = 0 := by
    intro z hz
    have h1 : BalTensor.map R (LinearMap.id : Y →ₗ[Rᵐᵒᵖ] Y) (e.symm : M' →ₗ[R] M)
        (BalTensor.map R f (LinearMap.id : M' →ₗ[R] M') z) = 0 := by
      rw [hz, map_zero]
    have h2 : BalTensor.map R f (e.symm : M' →ₗ[R] M) z = 0 := by
      rw [← hnt1]
      exact h1
    have h3 : BalTensor.map R f (LinearMap.id : M →ₗ[R] M)
        (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) (e.symm : M' →ₗ[R] M) z) = 0 := by
      change ((BalTensor.map R f (LinearMap.id : M →ₗ[R] M)).comp
        (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) (e.symm : M' →ₗ[R] M))) z = 0
      rw [hnt2]
      exact h2
    have h4 : BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) (e.symm : M' →ₗ[R] M) z = 0 := by
      apply h f hf
      simpa using h3
    have h5 : BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) (e : M →ₗ[R] M')
        (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) (e.symm : M' →ₗ[R] M) z) = z := by
      have := congrArg (fun g => g z) (hcomp X)
      simpa using this
    rw [h4, map_zero] at h5
    exact h5.symm
  intro z w hzw
  have hzw' : BalTensor.map R f (LinearMap.id : M' →ₗ[R] M') (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  exact sub_eq_zero.mp (key (z - w) hzw')

end Work.ORFlatness
