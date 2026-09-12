import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.isClosed_symm_posRoots_card_le_one
import Submission.Commons.LinearAlgebra.Matrix.strict_lorentzian_quadratic_dense_pos

namespace Commons.LinearAlgebra.Matrix

open Matrix Polynomial Set Topology

theorem closure_strict_lorentzian_quadratic_core (n : ℕ) (hn : 0 < n) :
  closure {A : Matrix (Fin n) (Fin n) ℝ |
    A.IsSymm ∧ (∀ i j, 0 < A i j) ∧ IsUnit A ∧
      (A.charpoly.roots.filter (fun r => 0 < r)).card = 1} =
  {A : Matrix (Fin n) (Fin n) ℝ |
    A.IsSymm ∧ (∀ i j, 0 ≤ A i j) ∧
      (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1} := by
  classical
  let S : Set (Matrix (Fin n) (Fin n) ℝ) := {A |
    A.IsSymm ∧ (∀ i j, 0 < A i j) ∧ IsUnit A ∧
      (A.charpoly.roots.filter (fun r => 0 < r)).card = 1}
  let T : Set (Matrix (Fin n) (Fin n) ℝ) := {A |
    A.IsSymm ∧ (∀ i j, 0 ≤ A i j) ∧
      (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1}
  change closure S = T
  apply subset_antisymm
  · have hST : S ⊆ T := by
      intro A hA
      rcases hA with ⟨hSymm, hpos, _hUnit, hcard⟩
      exact ⟨hSymm, fun i j => le_of_lt (hpos i j), by omega⟩
    have hTclosed : IsClosed T := by
      have hNclosed : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, 0 ≤ A i j} := by
        let N : Set (Matrix (Fin n) (Fin n) ℝ) := ⋂ p : (Fin n × Fin n), {A | 0 ≤ A p.1 p.2}
        have hN : {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, 0 ≤ A i j} = N := by
          ext A
          simp [N]
        rw [hN]
        refine isClosed_iInter (fun p => ?_)
        have hcont : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A p.1 p.2) := by
          fun_prop
        exact isClosed_le continuous_const hcont
      let C : Set (Matrix (Fin n) (Fin n) ℝ) := {A |
        A.IsSymm ∧ (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1}
      have hT : T = C ∩ {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, 0 ≤ A i j} := by
        ext A
        simp [T, C, and_assoc, and_comm]
      rw [hT]
      exact IsClosed.inter (isClosed_symm_posRoots_card_le_one n) hNclosed
    exact closure_minimal hST hTclosed
  · intro A hA
    rcases hA with ⟨hSymm, hnn, hcard⟩
    obtain ⟨f, hf_mem, hf_lim⟩ :=
      strict_lorentzian_quadratic_dense_pos hn A hSymm hnn hcard
    exact mem_closure_of_tendsto hf_lim (Filter.Eventually.of_forall hf_mem)

end Commons.LinearAlgebra.Matrix
