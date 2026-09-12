import Mathlib.Analysis.InnerProductSpace.ExteriorPower

set_option linter.unusedVariables false

namespace Commons.Analysis.InnerProductSpace

lemma norm_iMulti_orthonormal {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (u : Fin k → E)
    (hu : Orthonormal ℝ u) (hk : 0 < k) :
    ‖exteriorPower.ιMulti ℝ k u‖ = 1 := by
  classical
  have hsq : ‖exteriorPower.ιMulti ℝ k u‖ ^ 2 = 1 := by
    calc
      ‖exteriorPower.ιMulti ℝ k u‖ ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ k u) (exteriorPower.ιMulti ℝ k u) := by
        exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ k u)).symm
      _ = (Matrix.gram ℝ u).det := by rw [exteriorPower.inner_ιMulti_self]
      _ = (1 : Matrix (Fin k) (Fin k) ℝ).det := by
        rw [Matrix.gram_eq_one_iff_orthonormal.mpr hu]
      _ = 1 := by simp
  have hnonneg : 0 ≤ ‖exteriorPower.ιMulti ℝ k u‖ := norm_nonneg _
  rcases (sq_eq_one_iff.mp hsq) with h | h
  · exact h
  · linarith

end Commons.Analysis.InnerProductSpace
