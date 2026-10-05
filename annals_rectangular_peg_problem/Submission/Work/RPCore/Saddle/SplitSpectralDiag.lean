import Mathlib

/-!
# Diagonal operators on `EuclideanSpace ℝ (Fin n)`

Auxiliary definitions for `Work.RPCore.Saddle.split_spectral`.

`diagLM d` (resp. `diagCLM d`) is the linear (resp. continuous linear) operator on
`EuclideanSpace ℝ (Fin n)` acting on coordinates by `x ↦ fun i => d i * x i`.
-/

namespace Work.RPCore.Saddle

/-- The linear operator on `EuclideanSpace ℝ (Fin n)` given in coordinates by
`x ↦ fun i => d i * x i`. -/
noncomputable def diagLM {n : ℕ} (d : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi (fun i : Fin n => (d i) • LinearMap.proj i) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap)

/-- The continuous linear operator on `EuclideanSpace ℝ (Fin n)` given in coordinates by
`x ↦ fun i => d i * x i`. -/
noncomputable def diagCLM {n : ℕ} (d : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (diagLM d).toContinuousLinearMap

@[simp]
theorem diagCLM_apply {n : ℕ} (d : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    diagCLM d x i = d i * x i := by
  simp [diagCLM, diagLM, LinearMap.pi, LinearMap.proj]

end Work.RPCore.Saddle
