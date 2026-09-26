import Mathlib
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square
import Submission.Work.Smooth.JordanSeparation.square_lemma_aux

/-!
# Phragmén–Brouwer (Alexander's lemma) and the intersection of two complementary domains

We prove `Work.Smooth.JordanSeparation.componentIn_inter_componentIn`: for disjoint compact
`A B ⊆ ℂ` and `x ∉ A ∪ B`, the set
`connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x` is preconnected.

The mathematical content is the classical **Phragmén–Brouwer / Alexander lemma**: two points that
lie in the same component both of `Aᶜ` and of `Bᶜ` also lie in the same component of `(A ∪ B)ᶜ`.
Equivalently, `connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x =
connectedComponentIn (A ∪ B)ᶜ x`, and the left-hand side is preconnected because it is a connected
component.

The plane case of Phragmén–Brouwer is reduced here to the *square lemma* — two disjoint closed
subsets of the plane, the first missing the left edge of the unit square, the second missing the
right edge, whose union misses the top and bottom edges, do not separate the two left corners.
That reduction is `Work.Smooth.JordanSeparation.phragmen_brouwer_of_square` (proved from the square
lemma by the standard straight-line-homotopy argument), and the square lemma itself is
`Work.Smooth.JordanSeparation.square_lemma_aux`, proved by a colleague from the grid/duality
development (`square_cut_lemma`, `grid_spanning_continuum`).
-/

namespace Work.Smooth.JordanSeparation

open Set Topology

noncomputable section

/-- **The square lemma.**  Two disjoint closed sets `S1`, `S2` of the plane, `S1` missing the left
edge `{0} × [0,1]` of the unit square and `S2` the right edge `{1} × [0,1]`, whose union misses the
bottom edge `[0,1] × {0}` and the top edge `[0,1] × {1}`, do not separate the two left corners
`(0,0)` and `(0,1)`.

This is the form of the Phragmén–Brouwer theorem used by `phragmen_brouwer_of_square`; it is proved
in `square_lemma_aux`. -/
theorem square_lemma {S1 S2 : Set (ℝ × ℝ)} (h1c : IsClosed S1) (h2c : IsClosed S2)
    (hdisj : Disjoint S1 S2)
    (hL : S1 ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅)
    (hR : S2 ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅)
    (hB : (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅)
    (hT : (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅) :
    ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S1 ∪ S2)ᶜ ((0, 0) : ℝ × ℝ) :=
  square_lemma_aux h1c h2c hdisj hL hR hB hT

/-- **The target.**  For disjoint compact `A B ⊆ ℂ` and `x ∉ A ∪ B`, the intersection of the
connected components of `x` in `Aᶜ` and in `Bᶜ` is preconnected.  This is the plane case of the
Phragmén–Brouwer / Alexander lemma, obtained from `phragmen_brouwer_of_square` applied to
`square_lemma`. -/
theorem componentIn_inter_componentIn {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) {x : ℂ} (hxA : x ∈ Aᶜ) (hxB : x ∈ Bᶜ) :
    IsPreconnected (connectedComponentIn Aᶜ x ∩ connectedComponentIn Bᶜ x) := by
  have hx : x ∉ A ∪ B := by
    rintro (h | h)
    · exact hxA h
    · exact hxB h
  rw [phragmen_brouwer_of_square hA hB hAB hx square_lemma]
  exact isPreconnected_connectedComponentIn

end

end Work.Smooth.JordanSeparation
