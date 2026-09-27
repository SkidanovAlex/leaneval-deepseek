import Mathlib

namespace Work.EKLComp

/-- For a real `3 × 3` matrix `M` of determinant `1`, the map `G ↦ G.adjugate * M` is continuous
and takes the value `1` at `G = M` (because `M.adjugate * M = M.det • 1 = 1`).  Hence matrices
`G` sufficiently close to `M` entrywise satisfy `(G.adjugate * M) i j = 1 i j` up to any prescribed
`ε`.

The proof runs the metric `ε`-`δ` characterisation of continuity of the (everywhere continuous)
map `G ↦ ((Matrix.of G).adjugate * M)` on `Fin 3 → Fin 3 → ℝ`, and converts the sup-distance
bounds into the entrywise absolute-value bounds of the statement via `dist_pi_lt_iff`. -/
lemma exists_eta_inv_close (M : Matrix (Fin 3) (Fin 3) ℝ) (hMdet : M.det = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ G : Matrix (Fin 3) (Fin 3) ℝ, (∀ i j, |G i j - M i j| < η) → ∀ i j, |(G.adjugate * M) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε := by
  suffices h : ∃ η > 0, ∀ G : Fin 3 → Fin 3 → ℝ, (∀ i j, |G i j - M i j| < η) →
      ∀ i j, |(fun i j => ((Matrix.of G).adjugate * M) i j) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε
    from h
  let Mp : Fin 3 → Fin 3 → ℝ := fun i j => M i j
  have hcont : Continuous (fun G : Fin 3 → Fin 3 → ℝ => fun i j => ((Matrix.of G).adjugate * M) i j) := by
    fun_prop
  have hmetric := (Metric.continuous_iff).mp hcont Mp
  obtain ⟨δ, hδpos, hδ⟩ := hmetric ε hε
  have hMpM : (Matrix.of Mp) = M := rfl
  have hFMp : (fun i j => ((Matrix.of Mp).adjugate * M) i j) =
      (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
    funext i j
    rw [hMpM, Matrix.adjugate_mul, hMdet, one_smul]
  refine ⟨δ, hδpos, ?_⟩
  intro G hG i j
  have hdist : dist G Mp < δ := by
    rw [dist_pi_lt_iff hδpos]
    intro i'
    rw [dist_pi_lt_iff hδpos]
    intro j'
    rw [Real.dist_eq]
    have h := hG i' j'
    simp only [Mp] at h ⊢
    exact h
  have h2 := hδ G hdist
  rw [hFMp] at h2
  rw [dist_pi_lt_iff hε] at h2
  have h2i := h2 i
  rw [dist_pi_lt_iff hε] at h2i
  have h2ij := h2i j
  rw [Real.dist_eq] at h2ij
  exact h2ij

end Work.EKLComp
