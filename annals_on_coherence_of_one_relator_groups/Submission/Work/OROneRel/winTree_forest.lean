import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.delWordDefs
import Submission.Work.OROneRel.mk_eq_one_of_walkIn_winTree

/-!
# A closed walk cannot stay inside the tree of the window

`Work.OROneRel.winTree Wt c lo hi` is the set of edges of the window `[lo,hi]` of the level graph
(of the `ℤ`-cover of a one-relator complex) whose loop class under the gauge `Wt` is trivial; for the
tree-path gauge these are exactly the edges of the spanning tree.

If a non-empty reduced word `L` has vanishing total weight `lsig c L = 0` (so its walk, started at
level `0`, is a closed walk) and *every* traversal of that walk is an edge of the tree, then by the
telescoping identity `gauge_decor` the product of the loop classes of the traversals is
`Wt 0 · mk L · (Wt 0)⁻¹`; on the other hand it is the product of trivial loop classes, hence `1`.
So `mk L = 1`, which is impossible for a non-empty reduced word in a free group.

This is the statement that a closed walk cannot be contained in a forest, in the form needed by the
one-relator machinery.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **A non-empty reduced word spells a non-trivial element of the free group.**  Stated here
without a global `DecidableEq α` (the proof goes through `Classical.decEq`), since `mk` itself does
not depend on the decidable equality instance. -/
theorem mk_ne_one_of_isReduced {γ : Type*} [DecidableEq γ] {L : List (γ × Bool)}
    (hred : FreeGroup.IsReduced L) (hne : L ≠ []) : FreeGroup.mk L ≠ 1 := by
  intro h
  have h1 : FreeGroup.mk L = FreeGroup.mk ([] : List (γ × Bool)) := by rw [h]; rfl
  have h2 := FreeGroup.reduce.sound h1
  rw [FreeGroup.IsReduced.reduce_eq hred, FreeGroup.reduce_nil] at h2
  exact hne h2

theorem winTree_forest {α : Type u} (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi : ℤ}
    (L : List (α × Bool)) (hne : L ≠ [])
    (hred : FreeGroup.IsReduced L)
    (hlsig : Work.OROneRel.lsig c L = 0)
    (hL : ∀ p ∈ Work.OROneRel.decor c 0 L,
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi) : False := by
  classical
  -- the hypothesis says literally that the walk of `L` from level `0` runs inside the tree
  have hw : WalkIn c (winTree Wt c lo hi) 0 L := hL
  -- a closed walk inside the tree spells the trivial word
  have h1 : FreeGroup.mk L = 1 := mk_eq_one_of_walkIn_winTree Wt c lo hi 0 L hw hlsig
  -- but a non-empty reduced word is non-trivial
  exact mk_ne_one_of_isReduced hred hne h1

end Work.OROneRel
