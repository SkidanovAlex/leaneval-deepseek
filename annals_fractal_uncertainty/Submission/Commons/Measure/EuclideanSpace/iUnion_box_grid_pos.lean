import Mathlib
import Submission.Commons.Measure.Real.exists_cell_Icc
set_option linter.unusedVariables false


namespace Commons.Measure.EuclideanSpace

theorem iUnion_box_grid_pos {d : ℕ} {R W : ℝ} (hW : 0 < W) {N : ℕ} (hNpos : 0 < N)
    (hN : 2 * R ≤ (N : ℝ) * W) :
    Set.pi Set.univ (fun _ : Fin d => Set.Icc (-R) R) ⊆
      ⋃ j : Fin d → Fin N, Set.pi Set.univ (fun i : Fin d =>
        Set.Icc (-R + ((j i : ℕ) : ℝ) * W) (-R + (((j i : ℕ) : ℝ) + 1) * W)) := by
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, forall_const] at hx
  rw [Set.mem_iUnion]
  have hxle : ∀ i : Fin d, x i ≤ -R + (N : ℝ) * W := by
    intro i
    have h1 : x i ≤ R := (hx i).2
    have h2 : R ≤ -R + (N : ℝ) * W := by linarith
    linarith
  have hex : ∀ i : Fin d, ∃ k : ℕ, k < N ∧
      x i ∈ Set.Icc (-R + (k : ℝ) * W) (-R + (((k + 1 : ℕ) : ℝ)) * W) :=
    fun i => Commons.Measure.Real.exists_cell_Icc N hNpos ⟨(hx i).1, hxle i⟩
  choose k hk using hex
  refine ⟨fun i => ⟨k i, (hk i).1⟩, ?_⟩
  simp only [Set.mem_pi, Set.mem_univ, forall_const]
  intro i
  simpa using (hk i).2

end Commons.Measure.EuclideanSpace
