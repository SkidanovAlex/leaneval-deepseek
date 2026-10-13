import Mathlib

namespace Work.WilkG4c

/-- **The image of an interval under a continuous function covers every value strictly between
its sharp lower and upper bounds.** `K` is order-convex, `f` is continuous at every point of `K`,
`α` resp. `β` are sharp lower resp. upper bounds of `f '' K` in the sense that for every `u > α`
there is an image point `< u`, and for every `u < β` there is an image point `> u`. -/
theorem exists_mem_image_ivt {K : Set ℝ} {f : ℝ → ℝ} {α β : ℝ}
    (hord : K.OrdConnected) (hcont : ∀ x ∈ K, ContinuousAt f x)
    (hα : ∀ u : ℝ, α < u → ∃ x ∈ K, f x < u)
    (hβ : ∀ u : ℝ, u < β → ∃ x ∈ K, u < f x) :
    ∀ η : ℝ, α < η → η < β → ∃ x ∈ K, f x = η := by
  intro η hαη hηβ
  -- `hα` at the level `η` gives an image point below `η`, `hβ` an image point above `η`.
  obtain ⟨a, haK, ha⟩ := hα η hαη
  obtain ⟨b, hbK, hb⟩ := hβ η hηβ
  -- `K` order-convex, so it contains the interval spanned by `a` and `b`; apply the IVT there.
  rcases le_total a b with hab | hba
  · have hsub : Set.Icc a b ⊆ K := hord.out haK hbK
    have hcontOn : ContinuousOn f (Set.Icc a b) :=
      fun x hx => (hcont x (hsub hx)).continuousWithinAt
    have hmem : η ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
    rcases intermediate_value_Icc hab hcontOn hmem with ⟨x, hxI, hfx⟩
    exact ⟨x, hsub hxI, hfx⟩
  · have hsub : Set.Icc b a ⊆ K := hord.out hbK haK
    have hcontOn : ContinuousOn f (Set.Icc b a) :=
      fun x hx => (hcont x (hsub hx)).continuousWithinAt
    have hmem : η ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
    rcases intermediate_value_Icc' hba hcontOn hmem with ⟨x, hxI, hfx⟩
    exact ⟨x, hsub hxI, hfx⟩

end Work.WilkG4c
