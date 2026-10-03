import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.coverCoedgeDev

/-!
# The projection killing the tree of a window

`keepList Wt c lo hi L` is the `filterMap` of a list of symbols of the level graph onto the alphabet
`β` of the window (the symbols whose edge lies in the window with non-trivial loop class).  Since
`winRoot Wt c lo hi u = FreeGroup.mk (keepList Wt c lo hi (decor c 0 (wordOf u)))`, the projection
of the edge group onto `F (β)` satisfies `mk_mul_map_keepList_mem`: if every symbol of `L`
traverses an edge of the window `[lo,hi]`, then the word `FreeGroup.mk L` differs from the image in
the edge group of its projection by an element of the normal closure of the tree of the window.

This is what converts a statement about the normal closure of the tree of `[lo,hi]` together with
the walk word into a statement about the normal closure of `winRoot`.
-/

namespace Work.OROneRel

noncomputable section

variable {α : Type*}

/-- The `filterMap` onto the alphabet of the window. -/
noncomputable def keepList (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (L : List ((α × ℤ) × Bool)) : List (winBeta Wt c lo hi × Bool) := by
  classical
  exact L.filterMap fun p =>
    if h : p.1 ∈ winE c lo hi ∧ coverClassAt Wt c p.1 ≠ 1 then
      some (⟨p.1, h⟩, p.2) else none

/-- `winRoot` is the word of the `filterMap` of the decorated walk word. -/
theorem winRoot_eq_mk_keepList {Wt : ℤ → FreeGroup (Fin 2)} {c : Fin 2 → ℤ} {lo hi : ℤ}
    {u : FreeGroup (Fin 2)} :
    winRoot Wt c lo hi u = FreeGroup.mk (keepList Wt c lo hi (decor c 0 (wordOf u))) := by
  rw [winRoot, winRootList, keepList]
  congr 1

/-- The tree of the window: the edges of the window of trivial loop class, as generators. -/
def treeSet (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) : Set (FreeGroup (α × ℤ)) :=
  FreeGroup.of '' {e : α × ℤ | e ∈ winE c lo hi ∧ coverClassAt Wt c e = 1}

theorem mem_treeSet {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {e : α × ℤ}
    (h : e ∈ winE c lo hi ∧ coverClassAt Wt c e = 1) :
    FreeGroup.of e ∈ treeSet Wt c lo hi := ⟨e, h, rfl⟩

end

end Work.OROneRel
