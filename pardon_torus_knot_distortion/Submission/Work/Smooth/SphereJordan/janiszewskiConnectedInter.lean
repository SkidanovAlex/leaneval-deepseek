import Mathlib
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square
import Submission.Work.Smooth.JordanSeparation.squareLemmaOfCrossing
import Submission.Work.Smooth.SphereJordan.janiszewskiChain.ConnectedInterPlane

/-!
# Janiszewski's theorem for two compact plane sets with connected intersection

If `F₁ F₂ ⊆ ℂ` are compact, their intersection is non-empty and preconnected, and `x y ∉ F₁ ∪ F₂`
lie in the same connected component both of `F₁ᶜ` and of `F₂ᶜ`, then they lie in the same connected
component of `(F₁ ∪ F₂)ᶜ`.  This is Janiszewski's theorem (Z. Janiszewski, *Sur les continus
irréductibles entre deux points*, J. École Polytech. (2) 16 (1911), 79–170), the topological input
of Pardon's distortion bound.

## What is recorded here

* The **square lemma** (`SquareHyp`), proved in this workspace by the finite Hex-duality argument
  as `Work.Smooth.JordanSeparation.squareLemmaOfCrossing`, and the **disjoint case** of
  Janiszewski's theorem (the Phragmén–Brouwer property for compact plane sets) which it implies
  through the straight-line-homotopy argument of
  `Submission/Work/Smooth/JordanSeparation/phragmen_brouwer_of_square.lean`;
* the theorem itself, whose proof is in
  `Submission/Work/Smooth/JordanSeparation/janiszewski_connectedInter_plane.lean` (which reduces
  the plane statement to the Riemann-sphere form
  `Submission/Work/Smooth/SphereJordan/janiszewski_sphere.lean`).

Note that the connectedness hypothesis `hcon` on the intersection is *essential*: it is not implied
by the disjoint case, and dropping it makes the statement false (two closed arcs of a circle whose
intersection is a pair of points, e.g. `[0°, 200°]` and `[160°, 360°]`, cover the circle).  See
`janiszewskiConnectedInter_NOTES.md` for the details and for the analysis of that "counterexample".
-/

namespace Work.Smooth.SphereJordan

open Set Topology

noncomputable section

/-- The **square lemma**: in the unit square, two disjoint closed sets, the first missing the left
edge and the second the right edge, whose union misses the bottom and the top edge, cannot separate
the bottom-left from the top-left corner. -/
abbrev SquareHyp : Prop :=
  ∀ {S1 S2 : Set (ℝ × ℝ)}, IsClosed S1 → IsClosed S2 → Disjoint S1 S2 →
    S1 ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ →
    S2 ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ →
    (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ →
    (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅ →
    ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S1 ∪ S2)ᶜ ((0, 0) : ℝ × ℝ)

/-- The square lemma (`Work.Smooth.JordanSeparation.squareLemmaOfCrossing`). -/
theorem squareLemma : SquareHyp := fun h1c h2c hdisj hL hR hB hT =>
  Work.Smooth.JordanSeparation.squareLemmaOfCrossing h1c h2c hdisj hL hR hB hT

/-- **Phragmén–Brouwer (the disjoint case of Janiszewski's theorem) for compact plane sets.** -/
theorem janiszewskiDisjoint {F₁ F₂ : Set ℂ}
    (h₁ : IsCompact F₁) (h₂ : IsCompact F₂) (hd : Disjoint F₁ F₂) {x y : ℂ}
    (hx : x ∉ F₁ ∪ F₂) (hy : y ∉ F₁ ∪ F₂)
    (h₁' : y ∈ connectedComponentIn F₁ᶜ x) (h₂' : y ∈ connectedComponentIn F₂ᶜ x) :
    y ∈ connectedComponentIn (F₁ ∪ F₂)ᶜ x :=
  (Work.Smooth.JordanSeparation.phragmen_brouwer_of_square h₁ h₂ hd hx squareLemma) ▸ ⟨h₁', h₂'⟩

/-- **Janiszewski's theorem for a connected intersection** (Janiszewski 1913): if `F₁ F₂ ⊆ ℂ` are
compact with non-empty preconnected intersection, and `x y ∉ F₁ ∪ F₂` lie in the same component
both of `F₁ᶜ` and of `F₂ᶜ`, then they lie in the same component of `(F₁ ∪ F₂)ᶜ`. -/
theorem janiszewskiConnectedInter {F₁ F₂ : Set ℂ} (h₁ : IsCompact F₁) (h₂ : IsCompact F₂)
    (hne : (F₁ ∩ F₂).Nonempty) (hcon : IsPreconnected (F₁ ∩ F₂)) {x y : ℂ}
    (hx : x ∉ F₁ ∪ F₂) (hy : y ∉ F₁ ∪ F₂)
    (h₁' : y ∈ connectedComponentIn F₁ᶜ x) (h₂' : y ∈ connectedComponentIn F₂ᶜ x) :
    y ∈ connectedComponentIn (F₁ ∪ F₂)ᶜ x :=
  _root_.Work.Smooth.SphereJordan.Chain.janiszewski_connectedInter_plane h₁ h₂ hne hcon hx hy h₁' h₂'

end

end Work.Smooth.SphereJordan
