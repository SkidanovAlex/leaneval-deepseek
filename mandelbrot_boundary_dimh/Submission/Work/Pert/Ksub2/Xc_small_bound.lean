import Mathlib
import Submission.Work.Pert.Ksub2.Setup

namespace Work.Pert.Ksub2

/-- Iterated `ParabData.left_inv`: every backwards translate `w - j` (`j : ℕ`) of a point
`w ∈ d.Dφ` stays in `d.Dφ`. -/
theorem sub_nat_mem_Dφ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (hw : w ∈ d.Dφ) (j : ℕ) : w - (j : ℂ) ∈ d.Dφ := by
  induction j with
  | zero => simpa using hw
  | succ n ih =>
    have h : (w - (n : ℂ)) - 1 ∈ d.Dφ := d.left_inv _ ih
    have heq : w - ((n + 1 : ℕ) : ℂ) = (w - (n : ℂ)) - 1 := by push_cast; ring
    rw [heq]; exact h

/-- The finitely many translates of a compact `K' ⊆ d.Dφ` by `-1, …, -(J₀-1)` stay in the compact
`K' - {1,…,J₀-1} ⊆ d.Dφ` (by iterating `ParabData.left_inv`), on which the holomorphic `d.φ` is
bounded. -/
theorem Xc_small_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) (J₀ : ℕ) :
    ∃ B : ℝ, ∀ j : ℕ, 1 ≤ j → j < J₀ → ∀ w ∈ K', ‖d.φ (w - (j : ℂ))‖ ≤ B := by
  classical
  -- the union of the finitely many translates `K' - j`, `1 ≤ j < J₀`, is compact and lies in `Dφ`
  have hTcomp : IsCompact
      (⋃ j ∈ (Finset.Ico 1 J₀ : Set ℕ), (fun w : ℂ => w - (j : ℂ)) '' K') := by
    apply Set.Finite.isCompact_biUnion (Finset.finite_toSet _)
    intro j _
    exact hK'c.image (continuous_id.sub continuous_const)
  have hTsub :
      (⋃ j ∈ (Finset.Ico 1 J₀ : Set ℕ), (fun w : ℂ => w - (j : ℂ)) '' K') ⊆ d.Dφ := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨j, _, w, hw, rfl⟩ := hx
    exact sub_nat_mem_Dφ d (hK' hw) j
  -- `φ` is holomorphic on all of `Dφ`, hence bounded on this compact set
  obtain ⟨B, hB⟩ := hTcomp.exists_bound_of_continuousOn (d.φ_holo.continuousOn.mono hTsub)
  refine ⟨B, ?_⟩
  intro j hj1 hjJ w hw
  exact hB _ (by
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨j, by simp only [Finset.mem_coe, Finset.mem_Ico]; exact ⟨hj1, hjJ⟩, w, hw, rfl⟩)

end Work.Pert.Ksub2
