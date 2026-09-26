import Mathlib
import Submission.Work.Smooth.JordanSeparation.squareGrid
import Submission.Work.Smooth.JordanSeparation.hexDualityGrid

/-!
# The square lemma (Phragmén–Brouwer / Janiszewski, disjoint-crossing form)

Two disjoint closed sets `S1`, `S2` in the plane, the first missing the *left* edge
`L = {0} × [0,1]` of the unit square `Q = [0,1]²`, the second missing the *right* edge
`R = {1} × [0,1]`, whose union misses the *bottom* edge and the *top* edge, do not separate the
bottom-left corner `(0,0)` from the top-left corner `(0,1)`.

The proof is the classical "crossing" argument, assembled here from two results of this
workspace:

* `Work.Smooth.JordanSeparation.hexDualityGrid` — the **finite Hex duality** (the "no-draw"
  theorem for an `N × N` grid): either there is an `8`-connected chain of blocked cells running
  from the leftmost to the rightmost column, or there is a `4`-connected chain of free cells
  running from the bottom to the top row;
* `Work.Smooth.JordanSeparation.squareLemma_of_hex` — the **grid reduction**: choosing `h = 1/N`
  small enough that the thickenings of the four edges and the two sets `S1 ∩ Q`, `S2 ∩ Q` separate
  the relevant compact sets, no `8`-connected chain of cells meeting `S1 ∪ S2` can run from the
  left column to the right column (its cells would have to change type from `2` to `1`, while
  `8`-adjacent blocked cells meet `S1 ∪ S2` in points at distance `≤ (2√2) h`, hence have equal
  type).  The Hex duality then produces a `4`-connected chain of cells disjoint from `S1 ∪ S2`
  joining the bottom edge to the top edge, whose cell centres joined by straight segments form a
  preconnected subset of `(S1 ∪ S2)ᶜ` joining the two corners.
-/

open Set

namespace Work.Smooth.JordanSeparation

/-- The finite Hex duality in the form used by `squareLemma_of_hex`, obtained from
`hexDualityGrid`. -/
theorem hexDuality_of_grid : HexDuality := by
  intro N hN blocked
  by_cases h : HasBlockedChain blocked
  · exact Or.inr (by simpa only [HasBlockedChain, Adj8, Adj8g] using h)
  · exact Or.inl (by simpa only [HasFreeChain, Adj4, Adj4g] using hex_hard hN blocked h)

/-- **The square lemma.** -/
theorem squareLemmaOfCrossing {S1 S2 : Set (ℝ × ℝ)} (h1c : IsClosed S1) (h2c : IsClosed S2)
    (hdisj : Disjoint S1 S2)
    (hL : S1 ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅)
    (hR : S2 ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅)
    (hB : (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅)
    (hT : (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅) :
    ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S1 ∪ S2)ᶜ ((0, 0) : ℝ × ℝ) :=
  squareLemma_of_hex hexDuality_of_grid h1c h2c hdisj hL hR hB hT

end Work.Smooth.JordanSeparation
