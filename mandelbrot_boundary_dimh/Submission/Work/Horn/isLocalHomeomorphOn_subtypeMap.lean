import Mathlib

namespace Work.Horn

open Set Topology Filter

/-- If `B ⊆ ℂ` is open, `f : ℂ → ℂ` maps `B` into itself, and `f` agrees on a neighbourhood of
every point of `B` with an open partial homeomorphism of `ℂ`, then the induced self-map of the
subtype `B` is a local homeomorphism.

The proof is a reduction to the ambient map: `Subtype.val : B → ℂ` is an open embedding (here `B`
is open), hence a local homeomorphism; the composite `Subtype.val ∘ g` is the restriction to `B`
of `f`, which is a local homeomorphism by composition of the ambient local homeomorphism with the
inclusion; and a continuous map whose composite with a local homeomorphism is a local
homeomorphism is itself a local homeomorphism. -/
theorem isLocalHomeomorphOn_subtypeMap {f : ℂ → ℂ} {B : Set ℂ} (hB : IsOpen B)
    (hmap : Set.MapsTo f B B)
    (hfold : ∀ c ∈ B, ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ B ∧
      (⇑e : ℂ → ℂ) = f) :
    IsLocalHomeomorphOn (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) Set.univ := by
  -- `f` is a local homeomorphism on `B`.
  have hf : IsLocalHomeomorphOn f B := by
    intro c hc
    obtain ⟨e, hce, _, he⟩ := hfold c hc
    exact ⟨e, hce, he.symm⟩
  -- The inclusion `B ↪ ℂ` is an open embedding, hence a local homeomorphism.
  have hiso : IsOpenEmbedding (Subtype.val : B → ℂ) := hB.isOpenEmbedding_subtypeVal
  have hlh : IsLocalHomeomorph (Subtype.val : B → ℂ) := hiso.isLocalHomeomorph
  -- The restriction of `f` to `B` is a local homeomorphism.
  have hcomp : IsLocalHomeomorph (fun x : B => f x.1) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hf.comp hlh.isLocalHomeomorphOn (fun x _ => x.2))
  -- The subtype self-map is continuous, since the inclusion is an embedding.
  have hcont : Continuous (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) := by
    refine hiso.toIsEmbedding.continuous_iff.mpr ?_
    have : (Subtype.val ∘ fun x : B => (⟨f x.1, hmap x.2⟩ : B)) = fun x => f x.1 := rfl
    rw [this]
    exact hcomp.continuous
  -- Peel off the inclusion: `Subtype.val ∘ g` is a local homeomorphism and `g` is continuous.
  have hfinal : IsLocalHomeomorph (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) :=
    IsLocalHomeomorph.of_comp (by
      have : (Subtype.val ∘ fun x : B => (⟨f x.1, hmap x.2⟩ : B)) = fun x => f x.1 := rfl
      rw [this]; exact hcomp) hlh hcont
  exact hfinal.isLocalHomeomorphOn

end Work.Horn
