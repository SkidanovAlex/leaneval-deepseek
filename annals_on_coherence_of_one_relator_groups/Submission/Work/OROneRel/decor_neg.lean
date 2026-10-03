import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.wordOfDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The general level-`i` form of the reflection identity for the decorated walk: decorating by the
negated weights `-c` at level `i` is the same as decorating by `c` at level `-i` and reflecting
every symbol `(x, j) ↦ (x, -j)`.  This is the natural induction hypothesis for `decor_neg`. -/
theorem decor_neg_aux (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    decor (fun a => -c a) i L =
      (decor c (-i) L).map (fun p => (((p.1.1, -(p.1.2)) : α × ℤ), p.2)) := by
  induction L generalizing i with
  | nil => simp [decor]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · -- a negative letter: the running level drops by `c a` in the original decoration,
      -- hence rises by `(-c) a` in the decorated walk of `-c`.
      simp only [decor, List.map_cons]
      have h : (-i : ℤ) - c a = -(i - -c a) := by ring
      rw [h, ih]
      simp
    · -- a positive letter: the running level rises by `c a`.
      simp only [decor, List.map_cons]
      have h : (-i : ℤ) + c a = -(i + -c a) := by ring
      rw [h, ih]
      simp

/-- The reflection of the decorated walk: the walk of `u` in the level graph of `-c` at level `0` is the reflection `(x, i) ↦ (x, -i)` of the walk of `u` in the level graph of `c` at level `0` (the signs of the traversals are unchanged, because the direction of the edge `(x,i) → (x, i + c x)` is reversed together with the level).  A short `List` induction; the general level-`i` form `decor (-c) i L = (decor c (-i) L).map (x,j) ↦ (x,-j)` is the natural induction hypothesis. -/
theorem decor_neg (c : Fin 2 → ℤ) (u : FreeGroup (Fin 2)) :
    Work.OROneRel.decor (fun a => -c a) 0 (Work.OROneRel.wordOf u) =
      (Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u)).map
        (fun p => (((p.1.1, -(p.1.2)) : Fin 2 × ℤ), p.2)) := by
  simpa using decor_neg_aux c 0 (wordOf u)

end Work.OROneRel
