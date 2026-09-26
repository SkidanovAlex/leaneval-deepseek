import Mathlib
import Submission.Work.Spike.janiszewski_pointInter

/-!
# Janiszewski's theorem for two disjoint compact plane sets

`Work.BoxShrink.Pinch.janiszewskiDisjointCompact`: for disjoint compact `A B ⊆ ℂ` and points
`p q ∉ A ∪ B`, if `q` lies in the connected component of `p` both in `Aᶜ` and in `Bᶜ`, then it lies
in the connected component of `p` in `(A ∪ B)ᶜ`.

This is the *disjoint* case of Janiszewski's theorem, i.e. the Phragmén–Brouwer property of the
plane.  It is the classical input of `Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn`
(the frontier of a complementary domain of a continuum is preconnected), and is used by the planar
and spherical Janiszewski developments of the workspace.

The proof is immediate from the closed form of Phragmén–Brouwer recorded in
`Work.Spike.phragmen_brouwer_closed` (proved there from the square lemma of
`Work.Smooth.JordanSeparation.componentIn_inter_componentIn`): closedness is all that the
Phragmén–Brouwer argument uses, and compactness gives it.
-/

open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **Janiszewski's theorem for two disjoint compact subsets of `ℂ`.**  If `A` and `B` are disjoint
compact subsets of `ℂ` and `p, q ∉ A ∪ B` lie in the same connected component both of `Aᶜ` and of
`Bᶜ`, then they lie in the same connected component of `(A ∪ B)ᶜ`. -/
theorem janiszewskiDisjointCompact {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) {p q : ℂ} (hp : p ∉ A ∪ B) (hq : q ∉ A ∪ B)
    (hA' : q ∈ connectedComponentIn Aᶜ p) (hB' : q ∈ connectedComponentIn Bᶜ p) :
    q ∈ connectedComponentIn (A ∪ B)ᶜ p := by
  rw [← Work.Spike.phragmen_brouwer_closed hA.isClosed hB.isClosed hAB hp]
  exact ⟨hA', hB'⟩

end

end Work.BoxShrink.Pinch
