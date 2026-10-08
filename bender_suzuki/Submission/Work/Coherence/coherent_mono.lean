import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section
open Classical
namespace Work.Coherence

theorem coherent_mono {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S T : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hST : T ⊆ S) (h : Coherent S τ) : Coherent T τ := by
  obtain ⟨τ', hτ', hι, hv⟩ := h
  refine ⟨τ', ?_, ?_, ?_⟩
  · intro α hα; exact hτ' α (zSpan0_mono hST hα)
  · exact ⟨fun α hα β hβ => hι.inner_eq α (zSpan_mono hST hα) β (zSpan_mono hST hβ)⟩
  · intro χ hχ; exact hv χ (hST hχ)

end Work.Coherence
