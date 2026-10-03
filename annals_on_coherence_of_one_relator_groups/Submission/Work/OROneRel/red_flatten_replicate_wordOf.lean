import Mathlib
import Submission.Work.OROneRel.wordOfDefs

/-!
# `Red` for a repeated reduced word

If `v` is an element of a free group with reduced word `v.toWord`, then the concatenation of `n`
copies of `v.toWord` freely reduces to the reduced word of `v ^ n`.  Indeed `FreeGroup.toWord_pow`
identifies `(v ^ n).toWord` with the maximal reduction `FreeGroup.reduce` of that concatenation, and
that concatenation reduces to its maximal reduction (`FreeGroup.reduce.red`).

The file then transfers this to the workspace's `wordOf` (which is `FreeGroup.toWord` at the
classical `DecidableEq` instance), so that no `DecidableEq α` hypothesis has to appear in the
statement: `DecidableEq` is a subsingleton, hence the instance hidden inside `wordOf` agrees
definitionally with the instance supplied by `classical`.
-/

namespace Work.OROneRel

/-- `Red` version of `FreeGroup.toWord_pow`: the `n`-fold concatenation of a reduced word reduces
to the reduced word of the `n`-th power. -/
theorem red_flatten_replicate_toWord {α : Type*} [DecidableEq α] (v : FreeGroup α) (n : ℕ) :
    FreeGroup.Red (List.flatten (List.replicate n v.toWord)) (v ^ n).toWord := by
  rw [FreeGroup.toWord_pow]
  exact FreeGroup.reduce.red

theorem red_flatten_replicate_wordOf {α : Type*} (v : FreeGroup α) (n : ℕ) :
    FreeGroup.Red (List.flatten (List.replicate n (Work.OROneRel.wordOf v)))
      (Work.OROneRel.wordOf (v ^ n)) := by
  classical
  exact red_flatten_replicate_toWord v n

end Work.OROneRel
