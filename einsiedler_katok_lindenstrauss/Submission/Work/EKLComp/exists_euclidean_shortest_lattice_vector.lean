import Mathlib
import Submission.Work.EKLComp.EucDefs
import Submission.Work.EKLComp.enorm3_basic_bounds
import Submission.Work.EKLComp.exists_coord_bound_of_enorm3_le
import Submission.Work.EKLComp.short_vector_of_det_one

namespace Work.EKLComp

noncomputable section

theorem exists_euclidean_shortest_lattice_vector (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M.det = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hmin : ∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖(Matrix.mulVec M (fun i => (m i : ℝ)) : Fin 3 → ℝ)‖) :
    ∃ m : Fin 3 → ℤ, m ≠ 0 ∧
      (∀ m' : Fin 3 → ℤ, m' ≠ 0 →
        Work.EKLComp.enorm3 ((Matrix.mulVec M (fun i => (m i : ℝ)) : Fin 3 → ℝ)) ≤
          Work.EKLComp.enorm3 ((Matrix.mulVec M (fun i => (m' i : ℝ)) : Fin 3 → ℝ))) ∧
      Work.EKLComp.enorm3 ((Matrix.mulVec M (fun i => (m i : ℝ)) : Fin 3 → ℝ)) ≤ 2 * Real.sqrt 3 ∧
      ρ ≤ Work.EKLComp.enorm3 ((Matrix.mulVec M (fun i => (m i : ℝ)) : Fin 3 → ℝ)) := by
  classical
  obtain ⟨m₁, hm₁ne, hm₁bd⟩ := short_vector_of_det_one M hM
  set C : ℝ := enorm3 (Matrix.mulVec M (fun i => (m₁ i : ℝ))) with hC
  obtain ⟨K, hK⟩ := exists_coord_bound_of_enorm3_le M hM C
  let T : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(K : ℤ)) K)
  have memT : ∀ m : Fin 3 → ℤ, (∀ i, |(m i : ℝ)| ≤ (K : ℝ)) → m ∈ T := by
    intro m hm
    refine Fintype.mem_piFinset.mpr (fun i => ?_)
    have h1 : |(m i : ℝ)| ≤ (K : ℝ) := hm i
    have h2 : ((-(K : ℤ) : ℤ) : ℝ) ≤ (m i : ℝ) := by
      have := (abs_le.mp h1).1
      push_cast
      linarith
    have h3 : ((m i : ℤ) : ℝ) ≤ ((K : ℤ) : ℝ) := by
      have := (abs_le.mp h1).2
      push_cast
      linarith
    exact Finset.mem_Icc.mpr ⟨Int.cast_le.mp h2, Int.cast_le.mp h3⟩
  have hm₁T : m₁ ∈ T := memT m₁ (hK m₁ (le_of_eq hC.symm))
  have hSne : (T.filter (fun m : Fin 3 → ℤ => m ≠ 0)).Nonempty :=
    ⟨m₁, Finset.mem_filter.mpr ⟨hm₁T, hm₁ne⟩⟩
  obtain ⟨m, hm_mem, hm_min⟩ :=
    Finset.exists_min_image (T.filter (fun m : Fin 3 → ℤ => m ≠ 0))
      (fun m : Fin 3 → ℤ => enorm3 (Matrix.mulVec M (fun i => (m i : ℝ)))) hSne
  have hm_ne : m ≠ 0 := (Finset.mem_filter.mp hm_mem).2
  have hm₁mem : m₁ ∈ T.filter (fun m : Fin 3 → ℤ => m ≠ 0) :=
    Finset.mem_filter.mpr ⟨hm₁T, hm₁ne⟩
  have hmle : enorm3 (Matrix.mulVec M (fun i => (m i : ℝ))) ≤ C := by
    rw [hC]
    exact hm_min m₁ hm₁mem
  refine ⟨m, hm_ne, ?_, ?_, ?_⟩
  · intro m' hm'ne
    by_cases hle : enorm3 (Matrix.mulVec M (fun i => (m' i : ℝ))) ≤ C
    · exact hm_min m' (Finset.mem_filter.mpr ⟨memT m' (hK m' hle), hm'ne⟩)
    · have hlt : C < enorm3 (Matrix.mulVec M (fun i => (m' i : ℝ))) := not_le.mp hle
      linarith
  · linarith [hmle, hm₁bd, hC]
  · have h1 : ρ ≤ ‖(Matrix.mulVec M (fun i => (m i : ℝ)) : Fin 3 → ℝ)‖ := hmin m hm_ne
    have h2 : ‖(Matrix.mulVec M (fun i => (m i : ℝ)) : Fin 3 → ℝ)‖ ≤
        enorm3 (Matrix.mulVec M (fun i => (m i : ℝ))) := (enorm3_basic_bounds _).2.2.1
    linarith

end
end Work.EKLComp
