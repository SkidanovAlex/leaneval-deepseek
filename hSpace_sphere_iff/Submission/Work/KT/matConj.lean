import Mathlib

namespace Work.KT

theorem matConj (n : ℕ) (φ : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
    (P : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    LinearMap.toMatrix' (φ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) *
        LinearMap.toMatrix' P *
        LinearMap.toMatrix' (φ.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
      = LinearMap.toMatrix' (φ.conj P)
    ∧ LinearMap.toMatrix' (φ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) *
        LinearMap.toMatrix' (φ.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 1
    ∧ LinearMap.toMatrix' (φ.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) *
        LinearMap.toMatrix' (φ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearEquiv.conj_apply, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      Matrix.mul_assoc]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]

end Work.KT
