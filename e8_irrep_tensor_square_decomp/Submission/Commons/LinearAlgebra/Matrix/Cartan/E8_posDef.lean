import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Matrix.Cartan

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- The eight linear forms realizing a Cholesky-type sum-of-squares decomposition
of the quadratic form of the `E₈` Cartan matrix. -/
private def e8Form (v : Fin 8 → ℚ) : Fin 8 → ℚ :=
  ![2 * v 0 - v 2, 2 * v 1 - v 3, 3 * v 2 - 2 * v 3, 5 * v 3 - 6 * v 4,
    4 * v 4 - 5 * v 5, 3 * v 5 - 4 * v 6, 2 * v 6 - 3 * v 7, v 7]

/-- The positive denominators in the sum-of-squares decomposition. -/
private def e8Coef : Fin 8 → ℚ := ![2, 2, 6, 30, 20, 12, 6, 2]

private lemma e8Form_injective : ∀ v : Fin 8 → ℚ, (∀ k, e8Form v k = 0) → v = 0 := by
  intro v h
  have h0 : 2 * v 0 - v 2 = 0 := by simpa [e8Form] using h 0
  have h1 : 2 * v 1 - v 3 = 0 := by simpa [e8Form] using h 1
  have h2 : 3 * v 2 - 2 * v 3 = 0 := by simpa [e8Form] using h 2
  have h3 : 5 * v 3 - 6 * v 4 = 0 := by simpa [e8Form] using h 3
  have h4 : 4 * v 4 - 5 * v 5 = 0 := by simpa [e8Form] using h 4
  have h5 : 3 * v 5 - 4 * v 6 = 0 := by simpa [e8Form] using h 5
  have h6 : 2 * v 6 - 3 * v 7 = 0 := by simpa [e8Form] using h 6
  have h7 : v 7 = 0 := by simpa [e8Form] using h 7
  funext k
  fin_cases k
  · show v 0 = 0; linarith
  · show v 1 = 0; linarith
  · show v 2 = 0; linarith
  · show v 3 = 0; linarith
  · show v 4 = 0; linarith
  · show v 5 = 0; linarith
  · show v 6 = 0; linarith
  · show v 7 = 0; linarith

private lemma e8Coef_pos (k : Fin 8) : 0 < e8Coef k := by
  fin_cases k <;> norm_num [e8Coef]

private lemma e8_sq_sum_pos : ∀ v : Fin 8 → ℚ, v ≠ 0 →
    0 < ∑ k : Fin 8, (e8Form v k) ^ 2 / e8Coef k := by
  intro v hv
  have hnonneg : ∀ k : Fin 8, 0 ≤ (e8Form v k) ^ 2 / e8Coef k := fun k =>
    div_nonneg (sq_nonneg _) (le_of_lt (e8Coef_pos k))
  have hex : ∃ k : Fin 8, 0 < (e8Form v k) ^ 2 / e8Coef k := by
    by_contra h
    rw [not_exists] at h
    have hle : ∀ k : Fin 8, (e8Form v k) ^ 2 / e8Coef k ≤ 0 := by
      intro k
      by_contra hc
      exact h k (not_le.mp hc)
    refine hv (e8Form_injective v ?_)
    intro k
    have hz : (e8Form v k) ^ 2 / e8Coef k = 0 := le_antisymm (hle k) (hnonneg k)
    rw [div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact sq_eq_zero_iff.mp hz
    · exact absurd hz (ne_of_gt (e8Coef_pos k))
  obtain ⟨k, hk⟩ := hex
  exact Finset.sum_pos' (fun k _ => hnonneg k) ⟨k, Finset.mem_univ k, hk⟩

theorem E8_posDef : ∀ v : Fin 8 → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (CartanMatrix.E₈ i j : ℚ) * v j := by
  intro v hv
  have hSOS : (∑ i, ∑ j, v i * (CartanMatrix.E₈ i j : ℚ) * v j)
      = ∑ k : Fin 8, (e8Form v k) ^ 2 / e8Coef k := by
    simp only [CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val,
      e8Form, e8Coef]
    ring
  rw [hSOS]
  exact e8_sq_sum_pos v hv

end Commons.LinearAlgebra.Matrix.Cartan