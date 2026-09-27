import Mathlib
import Submission.Work.PL.Subdiv

namespace Work.PL.SubdivFull

theorem exists_chain_of_subset_sd_face {N : ℕ} {K : PL.Cx N} {s t : Finset (PL.E N)}
    (hs : s ∈ (Work.PL.Subdiv.sd K).faces) (hts : t ⊆ s) :
    ∃ C : Finset (Finset (PL.E N)), Work.PL.Subdiv.IsChain K C ∧
      t = C.image Work.PL.Subdiv.bary ∧ ∀ ρ ∈ C, Work.PL.Subdiv.bary ρ ∈ t := by
  classical
  obtain ⟨-, C, hC, rfl⟩ := Work.PL.Subdiv.mem_sd_faces_iff.mp hs
  refine ⟨C.filter (fun ρ => Work.PL.Subdiv.bary ρ ∈ t),
    hC.mono (Finset.filter_subset _ _), ?_, ?_⟩
  · refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨ρ, hρ, hρx⟩ := Finset.mem_image.mp (hts hx)
      exact Finset.mem_image.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρ, hρx ▸ hx⟩, hρx⟩
    · obtain ⟨ρ, hρ, hρx⟩ := Finset.mem_image.mp hx
      rw [← hρx]
      exact (Finset.mem_filter.mp hρ).2
  · intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2

end Work.PL.SubdivFull
