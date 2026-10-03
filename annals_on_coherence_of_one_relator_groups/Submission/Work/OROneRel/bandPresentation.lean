import Mathlib
import Submission.Work.OROneRel.bandCell
import Submission.Work.OROneRel.treeKill_walkCell
import Submission.Work.OROneRel.twoLetterTlDefs

/-!
# The `π₁`-side comparison map of the two-letter band

This assembles §8 of `NOTES_twoLetterBandComparison_injective.md`: given the delegated Tietze step
`Work.OROneRel.treeKill_walkCell`, the band's `2`-cell — read in the window's edge group
(`walkCell`) — becomes, after killing the tree edges (`treeKill`), the **vertex relator**
`winRoot Wt c lo hi w` in the alphabet `winBeta`.

* `treeKill_walkCell_zero` — the `j = 0` case: `treeKill (walkCell c lo hi 0 w h) = winRoot Wt c lo hi w`.
* `tlUCell` — the `2`-cell of `⟨a, b | (tlU p q) ^ l⟩` read in `FreeGroup ↥(winE (tlW p q) 0 (p*q))`.
* `treeKill_tlUCell` — **the statement of the comparison map on the `2`-cell**:
  `treeKill (tlUCell) = winRoot ^ l`, i.e. the band's `2`-cell in the window's full edge group
  becomes the vertex relator.  With `treeKill_of_tree` (the tree relators die) this is exactly what
  makes the comparison map
  `PresentedGroup (treeRel ∪ {tlUCell}) →* PresentedGroup {winRoot ^ l}`
  well defined, i.e. it identifies the `π₁` of the band (with its full `1`-skeleton) with the vertex
  presentation.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The Tietze step at level `0`**: the walk of `w` from level `0`, read in the window's edge group
and then having its tree edges killed, is the vertex relator `winRoot Wt c lo hi w`. -/
theorem treeKill_walkCell_zero {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (w : FreeGroup α)
    (h : ∀ p ∈ decor c 0 (wordOf w), coverEdge p ∈ winE c lo hi) :
    treeKill Wt c lo hi (walkCell c lo hi 0 w h) = winRoot Wt c lo hi w := by
  rw [treeKill_walkCell Wt c lo hi 0 w h]
  rfl

/-- **The `2`-cell of the two-letter band**, read in `FreeGroup ↥(winE (tlW p q) 0 (p*q))`: the
`l`-th power of the walk of `u = tlU p q` (whose walk returns to level `0`, `cohom (tlW p q) u = 1`),
i.e. the walk of `u ^ l` attached by the single relator of `⟨a, b | (tlU p q) ^ l⟩`. -/
noncomputable def tlUCell (p q l : ℕ)
    (h : ∀ p' ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge p' ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    FreeGroup ↥(winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :=
  (walkCell (tlW p q) 0 ((p : ℤ) * (q : ℤ)) 0 (tlU p q) h) ^ l

/-- **The comparison map on the `2`-cell**: killing the tree edges of the band's cell yields the
vertex relator `winRoot ^ l`.  This is what makes
`PresentedGroup (treeRel ∪ {tlUCell}) →* PresentedGroup {winRoot ^ l}` well defined. -/
theorem treeKill_tlUCell {p q l : ℕ} (Wt : ℤ → FreeGroup (Fin 2))
    (h : ∀ p' ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge p' ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    treeKill Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlUCell p q l h) =
      winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) ^ l := by
  rw [tlUCell, map_pow, treeKill_walkCell_zero]

end Work.OROneRel
