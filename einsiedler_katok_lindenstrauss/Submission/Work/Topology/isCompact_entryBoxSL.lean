import Mathlib
import Submission.Work.EKLContract.Defs

namespace Work.Topology

/-- The entrywise box `{g ∈ SL₃(ℝ) | |g i j - c i j| ≤ s}` around an arbitrary matrix `c : M₃(ℝ)`
is a compact subset of `SL₃(ℝ)`. -/
theorem isCompact_entryBoxSL (c : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    IsCompact {g : Work.EKLContract.SL3 |
      ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - c i j| ≤ s} := by
  -- The corresponding entrywise box in the ambient matrix space is a product of closed intervals,
  -- hence compact by Tychonoff in the finite case.
  have hB : IsCompact {M : Matrix (Fin 3) (Fin 3) ℝ | ∀ i j, |M i j - c i j| ≤ s} := by
    change IsCompact {M : Fin 3 → Fin 3 → ℝ | ∀ i j, |M i j - c i j| ≤ s}
    have h : {M : Fin 3 → Fin 3 → ℝ | ∀ i j, |M i j - c i j| ≤ s}
        = Set.pi Set.univ (fun i : Fin 3 => Set.pi Set.univ
            (fun j : Fin 3 => Set.Icc (c i j - s) (c i j + s))) := by
      ext M
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
      constructor
      · intro h i j; exact ⟨by linarith [(h i j).1], by linarith [(h i j).2]⟩
      · intro h i j; exact ⟨by linarith [(h i j).1], by linarith [(h i j).2]⟩
    rw [h]
    exact isCompact_univ_pi (fun i => isCompact_univ_pi (fun j => isCompact_Icc))
  -- The topology on `SL₃(ℝ)` is the subspace topology of the closed embedding into matrices,
  -- so the box inside `SL₃(ℝ)` is the preimage of a compact set under a closed embedding.
  have hpre : {g : Work.EKLContract.SL3 |
      ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - c i j| ≤ s}
      = (↑) ⁻¹' {M : Matrix (Fin 3) (Fin 3) ℝ | ∀ i j, |M i j - c i j| ≤ s} := rfl
  rw [hpre]
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hB

end Work.Topology
