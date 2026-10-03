import Mathlib
import Submission.Work.OROneRel.coverRootDefs
import Submission.Work.OROneRel.gauge_cover_vertices_ncard
import Submission.Work.OROneRel.running_ncard_two
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- **The level set of the decorated word of a nontrivial relator with a letter of non-zero weight
has at least two elements.**

The levels touched by the decorated word `decor c 0 (wordOf u)` -- the union of the source and target
levels of its decorated letters -- are exactly the distinct levels visited by the walk
`running c 0 (wordOf u)` (`gauge_cover_vertices_ncard`).  A letter `x` occurring in `u` with
`c x ≠ 0` yields a letter `(x, b)` of `wordOf u` of non-zero weight, and reading it strictly changes
the level, so the walk visits at least two distinct levels (`running_ncard_two`).  The hypothesis
`u ≠ 1` is used only to know that `wordOf u` is non-empty so that the identification of the level
sets applies. -/
theorem coverLevelSet_ncard_two {α : Type u} (c : α → ℤ) (u : FreeGroup α)
    (hu : u ≠ 1) (hne : ∃ x ∈ Work.OROneRel.relatorLetters u, c x ≠ 0) :
    2 ≤ (Work.OROneRel.coverLevelSet c u).ncard := by
  classical
  -- `u ≠ 1` means the reduced word of `u` is non-empty.
  have hword : wordOf u ≠ [] := by
    intro h
    apply hu
    rw [← mk_wordOf u, h]
    exact FreeGroup.one_eq_mk.symm
  -- A generator `x` occurring in `u` occurs as a letter `(x, b)` of `wordOf u`.
  obtain ⟨x, hx, hcx⟩ := hne
  rw [relatorLetters] at hx
  obtain ⟨b, hb⟩ := hx
  have hne' : ∃ p ∈ wordOf u, c p.1 ≠ 0 := ⟨(x, b), hb, hcx⟩
  -- The level set is the set of levels visited by the walk.
  rw [coverLevelSet, gauge_cover_vertices_ncard c u hword]
  -- A letter of non-zero weight forces the walk to visit at least two levels.
  exact running_ncard_two c (wordOf u) hne'

end Work.OROneRel
