import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.wordOfDefs

/-!
# The band `2`-cell read in the window's edge group

`π₁`-side bookkeeping for the `N = 1` union/amalgam step (`Submission/Work/OROneRel/gateBookkeeping.lean`
supplies the gate side).  The band complex on the window `winE c lo hi` has, besides its gauge tree,
one `2`-cell per level `j` of its span, namely the walk of the defining relator `w` started at level
`j`.  Here we

* `walkCellList` / `walkCell` — write that walk as a word in the **free group on the window edges**
  `↥(winE c lo hi)` (the hypothesis says all its letters lie in the window);
* `treeKill` — the map from that edge group to the **free group on the window's non-tree edges**
  `winBeta Wt c lo hi` which kills the tree edges (trivial loop class) and is the identity on the
  non-tree edges.  This is the `π₁`-side of the identification
  `π₁ D ≅ ⟨winBeta | (the walk words)⟩` of the band: `PresentedGroup (treeRel ∪ {walkCell})` under
  `treeKill` becomes `⟨winBeta | treeKill (walkCell)⟩`, and for `w = tlU p q ^ l`, `j = 0` the image
  is the already-defined walk word `winRoot Wt c lo hi (tlU p q ^ l)`.

The identity `treeKill (walkCell …) = FreeGroup.mk (the filtered walk word)` is isolated as
`Work.OROneRel.treeKill_walkCell` (delegated, so that this file stays a leaf of definitions); it is
the Tietze step that removes the tree generators from the band's presentation.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The decorated walk of `w` started at level `j`, as a word in the free group on the **window
edges** `↥(winE c lo hi)`.  The hypothesis `h` says every edge of the walk lies in the window (so
the membership proofs exist). -/
noncomputable def walkCellList (c : α → ℤ) (lo hi j : ℤ) (w : FreeGroup α)
    (h : ∀ p ∈ decor c j (wordOf w), coverEdge p ∈ winE c lo hi) :
    List (↥(winE c lo hi) × Bool) :=
  (decor c j (wordOf w)).attach.map fun p => (⟨coverEdge p.1, h p.1 p.2⟩, p.1.2)

/-- The `2`-cell of `⟨α | w⟩` at level `j`, read in the window's edge group. -/
noncomputable def walkCell (c : α → ℤ) (lo hi j : ℤ) (w : FreeGroup α)
    (h : ∀ p ∈ decor c j (wordOf w), coverEdge p ∈ winE c lo hi) :
    FreeGroup ↥(winE c lo hi) :=
  FreeGroup.mk (walkCellList c lo hi j w h)

/-- The map from the window's edge group to the free group on the window's **non-tree** edges: a
tree edge (trivial loop class) goes to `1`, a non-tree edge goes to itself. -/
noncomputable def treeKill (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    FreeGroup ↥(winE c lo hi) →* FreeGroup (winBeta Wt c lo hi) := by
  classical
  exact FreeGroup.lift fun e =>
    if h : coverClassAt Wt c (e : α × ℤ) = 1 then 1 else FreeGroup.of ⟨(e : α × ℤ), e.2, h⟩

/-- `treeKill` kills the tree edges. -/
theorem treeKill_of_tree (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    {e : ↥(winE c lo hi)} (h : (e : α × ℤ) ∈ winTree Wt c lo hi) :
    treeKill Wt c lo hi (FreeGroup.of e) = 1 := by
  classical
  rw [treeKill, FreeGroup.lift_apply_of]
  exact dif_pos (mem_winTree.mp h).2

/-- `treeKill` is the identity on a non-tree edge (as a basis element). -/
theorem treeKill_of_notMem (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    {e : ↥(winE c lo hi)} (h : (e : α × ℤ) ∉ winTree Wt c lo hi) :
    treeKill Wt c lo hi (FreeGroup.of e) =
      FreeGroup.of ⟨(e : α × ℤ), e.2, fun hc => h (mem_winTree.mpr ⟨e.2, hc⟩)⟩ := by
  classical
  rw [treeKill, FreeGroup.lift_apply_of]
  exact dif_neg fun hc => h (mem_winTree.mpr ⟨e.2, hc⟩)

/-- The non-tree traversals of a decorated walk, read in the vertex alphabet `winBeta Wt c lo hi`.
For `L = decor c 0 (wordOf u)` this is exactly `winRootList Wt c lo hi u`. -/
noncomputable def betaKillList (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (L : List ((α × ℤ) × Bool)) : List (winBeta Wt c lo hi × Bool) := by
  classical
  exact L.filterMap fun p =>
    if hh : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1 then
      some (⟨coverEdge p, hh.1, hh.2⟩, p.2) else none

/-- The same as an element of the free group on `winBeta Wt c lo hi`. -/
noncomputable def betaKill (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (L : List ((α × ℤ) × Bool)) : FreeGroup (winBeta Wt c lo hi) :=
  FreeGroup.mk (betaKillList Wt c lo hi L)

/-- `treeKill` fixes the basis element of a non-tree edge, in `winBeta` form. -/
theorem treeKill_of_beta (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (e : winBeta Wt c lo hi) :
    treeKill Wt c lo hi (FreeGroup.of (⟨e.1, e.2.1⟩ : ↥(winE c lo hi))) =
      FreeGroup.of e := by
  classical
  rw [treeKill, FreeGroup.lift_apply_of, dif_neg (fun hc => e.2.2 hc)]
  congr 1

end Work.OROneRel
