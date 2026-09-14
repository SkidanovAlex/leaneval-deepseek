import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_one_le
import Submission.Commons.NumberTheory.NumberField.mahlerK_eq_prod_embeddings

namespace Commons.NumberTheory.NumberField

theorem mahlerK_eq_prod_algHom {K : Type*} [Field K] [NumberField K] {x : K} (hx : IsIntegral ℤ x) :
    Commons.NumberTheory.NumberField.mahlerK K x
      = ∏ χ : (K →ₐ[ℚ] ℂ), max 1 ‖χ x‖ := by
  rw [mahlerK_eq_prod_embeddings hx]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
    (fun σ : K →+* ℂ => max 1 ‖σ x‖)
    (fun χ : K →ₐ[ℚ] ℂ => max 1 ‖χ x‖)
    (fun σ => by simp)

end Commons.NumberTheory.NumberField
