import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.perron_vector_of_nonneg_symm_card_pos_le_one_nonzero
import Submission.Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots

namespace Commons.LinearAlgebra.Matrix


noncomputable section

theorem strictQuad_perron_vector {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hpos : ∀ i j : Fin n, 0 < A i j)
    (hcard : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1) :
    ∃ u : Fin n → ℝ, ∃ ρ : ℝ,
      0 < ρ ∧ (∀ i : Fin n, 0 < u i) ∧ (∑ i : Fin n, u i * u i) = 1 ∧
      A.mulVec u = ρ • u ∧
      (∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
        (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0) := by
  classical
  have hnn : ∀ i j : Fin n, 0 ≤ A i j := fun i j => le_of_lt (hpos i j)
  have hAne : A ≠ 0 := by
    intro hA0
    have h00 : A ⟨0, hn⟩ ⟨0, hn⟩ = 0 := congrFun (congrFun hA0 ⟨0, hn⟩) ⟨0, hn⟩
    exact (lt_irrefl (0 : ℝ)) (by simpa [h00] using hpos ⟨0, hn⟩ ⟨0, hn⟩)
  obtain ⟨u, ρ, hρ_pos, hu_nonneg, hu_norm, hu_eigen, hquad⟩ :=
    perron_vector_of_nonneg_symm_card_pos_le_one_nonzero (A := A) hn hA hnn (le_of_eq hcard) hAne
  refine ⟨u, ρ, hρ_pos, ?_, hu_norm, hu_eigen, hquad⟩
  intro i
  by_contra hnotpos
  have hui0 : u i = 0 := le_antisymm (le_of_not_gt hnotpos) (hu_nonneg i)
  have hrow0 : (A.mulVec u) i = 0 := by
    calc
      (A.mulVec u) i = (ρ • u) i := congr_fun hu_eigen i
      _ = ρ * u i := by rw [Pi.smul_def]; rfl
      _ = 0 := by rw [hui0]; ring
  have hsum_eq : (∑ j : Fin n, A i j * u j) = 0 := by
    rw [Matrix.mulVec_apply_eq_sum] at hrow0
    exact hrow0
  have hexists_pos : ∃ j : Fin n, 0 < u j := by
    have hnorm_pos : 0 < (∑ j : Fin n, u j * u j) := by
      rw [hu_norm]
      norm_num
    by_contra hno
    have hall_zero : ∀ j : Fin n, u j = 0 := by
      intro j
      by_contra hj_ne
      have hj_pos : 0 < u j := lt_of_le_of_ne' (hu_nonneg j) hj_ne
      exact hno ⟨j, hj_pos⟩
    have hsum0 : (∑ j : Fin n, u j * u j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hall_zero j]
      ring
    exact (ne_of_lt hnorm_pos) hsum0.symm
  obtain ⟨j0, hj0⟩ := hexists_pos
  have hsum_pos : 0 < (∑ j : Fin n, A i j * u j) := by
    have hterm_pos : 0 < A i j0 * u j0 := mul_pos (hpos i j0) hj0
    have hterm_nonneg : ∀ k : Fin n, k ∈ Finset.univ → 0 ≤ A i k * u k := by
      intro k hk
      exact mul_nonneg (le_of_lt (hpos i k)) (hu_nonneg k)
    have hle := Finset.single_le_sum hterm_nonneg (Finset.mem_univ j0)
    exact lt_of_lt_of_le hterm_pos hle
  linarith

end

end Commons.LinearAlgebra.Matrix
