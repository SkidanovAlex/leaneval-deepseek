import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT

/-- A matrix over `C(X, ℂ)` that is pointwise invertible is invertible, with an explicit inverse
whose values are the pointwise inverses. -/
theorem mat_inv_of_forall_isUnit {X : Type} [TopologicalSpace X] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) C(X, ℂ)) (h : ∀ x : X, IsUnit (A.map (fun F => evalC x F))) :
    ∃ B : Matrix (Fin k) (Fin k) C(X, ℂ), A * B = 1 ∧ B * A = 1 ∧
      ∀ x : X, B.map (fun F => evalC x F) = (A.map (fun F => evalC x F))⁻¹ := by
  -- The determinant of `A` is pointwise nonzero, hence a unit of `C(X, ℂ)`.
  have hdet : IsUnit A.det := by
    rw [ContinuousMap.isUnit_iff_forall_isUnit]
    intro x
    have h1 : A.det x = ((evalC x).mapMatrix A).det := AlgHom.map_det (evalC x) A
    rw [h1]
    exact (Matrix.isUnit_iff_isUnit_det (A.map (fun F => evalC x F))).mp (h x)
  -- Hence `A` is a unit of the matrix ring, and its inverse is the required `B`.
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet
  obtain ⟨U, hU⟩ := hA
  have hAB : A * (↑U⁻¹ : Matrix (Fin k) (Fin k) C(X, ℂ)) = 1 := by
    rw [← hU]; simp
  have hBA : (↑U⁻¹ : Matrix (Fin k) (Fin k) C(X, ℂ)) * A = 1 := by
    rw [← hU]; simp
  refine ⟨↑U⁻¹, hAB, hBA, ?_⟩
  intro x
  -- Evaluate the left inverse relation at `x`: it is a matrix inverse relation over `ℂ`.
  have key : (A.map (fun F => evalC x F)) *
      ((↑U⁻¹ : Matrix (Fin k) (Fin k) C(X, ℂ)).map (fun F => evalC x F)) = 1 := by
    rw [← Matrix.map_mul (f := (evalC x)), hAB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact (Matrix.inv_eq_right_inv key).symm

end Work.KT
