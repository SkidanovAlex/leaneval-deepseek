import Mathlib

namespace Work.HornCov

theorem isOpenEmbedding_of_section_of_isLocalHomeomorphOn {X : Type*} [TopologicalSpace X]
    {p : X → ℂ} {S : Set ℂ} (hSopen : IsOpen S)
    (hloc : IsLocalHomeomorphOn p (p ⁻¹' S))
    {σ : ↥S → X} (hσ : Continuous σ) (hσsec : ∀ u : ↥S, p (σ u) = (u : ℂ)) :
    Topology.IsOpenEmbedding σ := by
  -- `p ∘ σ` is the inclusion of `S` into `ℂ`.
  have hval : p ∘ σ = (Subtype.val : ↥S → ℂ) := by
    funext u; exact hσsec u
  -- hence `p ∘ σ` is a local homeomorphism
  have h1 : IsLocalHomeomorphOn (p ∘ σ) Set.univ := by
    rw [hval]
    exact (hSopen.isOpenEmbedding_subtypeVal).isLocalHomeomorph.isLocalHomeomorphOn
  -- and `p` is a local homeomorphism on the range of `σ`
  have h2 : IsLocalHomeomorphOn p (σ '' Set.univ) := by
    refine hloc.mono ?_
    rintro x ⟨u, -, rfl⟩
    rw [Set.mem_preimage, hσsec u]
    exact u.2
  have h3 : IsLocalHomeomorphOn σ Set.univ :=
    IsLocalHomeomorphOn.of_comp_left h1 h2 (fun u _ => hσ.continuousAt)
  have hlocσ : IsLocalHomeomorph σ :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr h3
  -- `σ` is injective since `p ∘ σ = id`, so it is an open embedding
  refine hlocσ.isOpenEmbedding_of_injective ?_
  intro a b hab
  have : (a : ℂ) = (b : ℂ) := by
    rw [← hσsec a, ← hσsec b, hab]
  exact Subtype.ext this

end Work.HornCov
