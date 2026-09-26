import Mathlib

namespace Work.BoxShrink.PinchOff

theorem exists_unc :
    ∃ f : OnePoint ℂ → ℂ, (∀ c : ℂ, f (c : OnePoint ℂ) = c) ∧
      ContinuousOn f (({OnePoint.infty} : Set (OnePoint ℂ))ᶜ) := by
  refine ⟨fun x => x.elim 0 id, fun c => rfl, ?_⟩
  rw [OnePoint.compl_infty]
  rw [← Set.image_univ]
  rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuousOn_image_iff]
  exact continuous_id.continuousOn

end Work.BoxShrink.PinchOff
