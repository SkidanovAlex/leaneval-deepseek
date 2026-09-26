import Mathlib
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square
import Submission.Work.Smooth.JordanSeparation.squareLemmaOfCrossing

/-!
# The plane disjoint Janiszewski case, in a fresh namespace

This is `Work.Smooth.SphereJordan.janiszewskiDisjoint` (the Phragmén–Brouwer property for two
disjoint compact plane sets, obtained from the square lemma by the straight-line-homotopy glue of
`phragmen_brouwer_of_square`), restated under the namespace `Work.Smooth.SphereJordan.Chain`.

It is placed here so that the cycle-free copy of the sphere-based chain
(`Submission/Work/Smooth/SphereJordan/janiszewskiChain/`) can use it *without* importing
`Submission.Work.Smooth.SphereJordan.janiszewskiConnectedInter`: that file is imported by
`janiszewskiDisjointSphere` inside the chain, so importing the chain from it would create an
import cycle.
-/

namespace Work.Smooth.SphereJordan.Chain

open Set

/-- The square lemma (proved by the finite Hex duality argument). -/
theorem squareLemma : ∀ {S1 S2 : Set (ℝ × ℝ)}, IsClosed S1 → IsClosed S2 → Disjoint S1 S2 →
    S1 ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ →
    S2 ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ →
    (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ →
    (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅ →
    ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S1 ∪ S2)ᶜ ((0, 0) : ℝ × ℝ) :=
  fun h1c h2c hdisj hL hR hB hT =>
    Work.Smooth.JordanSeparation.squareLemmaOfCrossing h1c h2c hdisj hL hR hB hT

/-- **Phragmén–Brouwer (disjoint case) for compact plane sets.** -/
theorem janiszewskiDisjoint {F₁ F₂ : Set ℂ}
    (h₁ : IsCompact F₁) (h₂ : IsCompact F₂) (hd : Disjoint F₁ F₂) {x y : ℂ}
    (hx : x ∉ F₁ ∪ F₂) (hy : y ∉ F₁ ∪ F₂)
    (h₁' : y ∈ connectedComponentIn F₁ᶜ x) (h₂' : y ∈ connectedComponentIn F₂ᶜ x) :
    y ∈ connectedComponentIn (F₁ ∪ F₂)ᶜ x :=
  (Work.Smooth.JordanSeparation.phragmen_brouwer_of_square h₁ h₂ hd hx squareLemma) ▸ ⟨h₁', h₂'⟩

end Work.Smooth.SphereJordan.Chain
