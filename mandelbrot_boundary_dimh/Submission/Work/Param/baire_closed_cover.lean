import Mathlib

namespace Work.Param

/-- Baire's theorem in the form needed here: if a nonempty open set `W` is covered by a
countable family of closed sets, then one of them has nonempty interior. -/
theorem baire_closed_cover {X : Type*} [TopologicalSpace X] [BaireSpace X] {W : Set X}
    (hWo : IsOpen W) (hWne : W.Nonempty) {Z : ℕ → Set X} (hZc : ∀ n, IsClosed (Z n))
    (hsub : W ⊆ ⋃ n, Z n) : ∃ n, (interior (Z n)).Nonempty := by
  by_contra h
  push Not at h
  have hnd : ∀ n, IsNowhereDense (Z n) := fun n => (hZc n).isNowhereDense_iff.mpr (h n)
  have hm : IsMeagre (⋃ n, Z n) := isMeagre_iUnion fun n => (hnd n).isMeagre
  exact not_isMeagre_of_isOpen hWo hWne (hm.mono hsub)

end Work.Param
