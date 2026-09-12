import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.perron_vector_of_nonneg_symm_card_pos_le_one_pos

namespace Commons.LinearAlgebra.Matrix

open Matrix Polynomial Set
open scoped BigOperators

theorem perron_vector_of_nonneg_symm_card_pos_le_one_nonzero
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hcard : (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1)
    (hAne : A ≠ 0) :
    ∃ u : Fin n → ℝ, ∃ λ : ℝ,
      0 < λ ∧ (∀ i, 0 ≤ u i) ∧ (∑ i, u i * u i) = 1 ∧
        A.mulVec u = λ • u ∧
        (∀ x : Fin n → ℝ, (∑ i, u i * x i) = 0 →
          (∑ i, ∑ j, x i * A i j * x j) ≤ 0) := by
  classical
  obtain ⟨u, lam, hu_nonneg, hu_norm, hlam_nonneg, hu_eigen, hquad_cond, hsupport⟩ :=
    perron_vector_of_nonneg_symm_card_pos_le_one_pos hn A hA hnn hcard
  have hlam_ne : lam ≠ 0 := by
    intro hlam0
    have hAu : A.mulVec u = 0 := by
      rw [hu_eigen, hlam0]
      simp
    have hAzero_entries : ∀ i j : Fin n, A i j = 0 := by
      intro i j
      by_cases huj : u j = 0
      · exact hsupport i j (Or.inr huj)
      · have hsum : (∑ k : Fin n, A i k * u k) = 0 := by
          have h := congr_fun hAu i
          rw [Matrix.mulVec_apply_eq_sum] at h
          simpa using h
        have hterm_nonneg : ∀ k : Fin n, k ∈ Finset.univ → 0 ≤ A i k * u k := by
          intro k hk
          exact mul_nonneg (hnn i k) (hu_nonneg k)
        have hterm_j : A i j * u j = 0 := by
          have hsum_iff := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
            (f := fun k : Fin n => A i k * u k) hterm_nonneg
          exact hsum_iff.mp hsum j (Finset.mem_univ j)
        exact (mul_eq_zero.mp hterm_j).resolve_right huj
    have hA0 : A = 0 := Matrix.ext (fun i j => hAzero_entries i j)
    exact hAne hA0
  have hlam_pos : 0 < lam := lt_of_le_of_ne' hlam_nonneg hlam_ne
  exact ⟨u, lam, hlam_pos, hu_nonneg, hu_norm, hu_eigen, hquad_cond⟩

end Commons.LinearAlgebra.Matrix
