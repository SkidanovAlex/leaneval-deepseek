/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The deleted word at an arbitrary starting level

`Submission/Work/OROneRel/delWordDefs.lean` defines the *deleted word* `delWord T c L` of a word `L`
with respect to a set of edges `T` of the level graph: the traversals of the walk of `L` started at
level `0` whose edge is not in `T`, read as letters `(edge, sign)`.

For the analysis of `delWord` it is convenient to have the same construction available at an
arbitrary starting level, since sub-words of `L` are decorated at shifted levels, and to have the
*traversal* of a single letter at an arbitrary level as an explicit object.

* `trav c a p` -- the traversal of the letter `p` read at level `a`, i.e. the decorated letter
  `((p.1, if p.2 then a else a - c p.1), p.2)`; it is the head of `decor c a [p]`;
* `delWordAt T c a L` -- the deleted word of `L` read from the level `a`; it agrees with `delWord`
  at level `0`;
* `decor_cons`, `coverSrc_trav`, `coverTgt_trav` -- the elementary walk calculus;
* `delWordAt_cons_of_mem` / `delWordAt_cons_of_notMem` -- the recursion of the deleted word, which
  is the basis of every induction on it.
-/
import Mathlib
import Submission.Work.OROneRel.delWordDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The traversal of the letter `p = (x, b)` read at the level `a`: the decorated letter
`((x, a), true)` if `b = true` and `((x, a - c x), false)` if `b = false`.  Its source level is `a`
and its target level is `a + linc c p`. -/
def trav (c : α → ℤ) (a : ℤ) (p : α × Bool) : (α × ℤ) × Bool :=
  ((p.1, if p.2 then a else a - c p.1), p.2)

@[simp] theorem trav_fst (c : α → ℤ) (a : ℤ) (p : α × Bool) : (trav c a p).1.1 = p.1 := by
  obtain ⟨x, b⟩ := p
  cases b <;> rfl

@[simp] theorem trav_snd (c : α → ℤ) (a : ℤ) (p : α × Bool) : (trav c a p).2 = p.2 := rfl

@[simp] theorem coverEdge_trav (c : α → ℤ) (a : ℤ) (p : α × Bool) :
    coverEdge (trav c a p) = (p.1, if p.2 then a else a - c p.1) := rfl

/-- The source level of the traversal of `p` at level `a` is `a`. -/
@[simp] theorem coverSrc_trav (c : α → ℤ) (a : ℤ) (p : α × Bool) : coverSrc c (trav c a p) = a := by
  obtain ⟨x, b⟩ := p
  cases b
  · simp only [trav, Bool.false_eq_true, if_false, coverSrc]; ring
  · simp only [trav, if_true, coverSrc]

/-- The target level of the traversal of `p` at level `a` is `a + linc c p`. -/
@[simp] theorem coverTgt_trav (c : α → ℤ) (a : ℤ) (p : α × Bool) :
    coverTgt c (trav c a p) = a + linc c p := by
  obtain ⟨x, b⟩ := p
  cases b
  · simp only [trav, Bool.false_eq_true, if_false, coverTgt, linc]; ring
  · simp only [trav, if_true, coverTgt, linc]

/-- **The decoration of a cons**: the first decorated letter is the traversal of the head at the
current level, and the decoration of the tail continues at the level shifted by `linc` of the
head. -/
theorem decor_cons (c : α → ℤ) (a : ℤ) (p : α × Bool) (L : List (α × Bool)) :
    decor c a (p :: L) = trav c a p :: decor c (a + linc c p) L := by
  obtain ⟨x, b⟩ := p
  cases b <;> rfl

/-- **The deleted word from an arbitrary level**: the traversals of the walk of `L` started at the
level `a` whose edge does not lie in `T` (with the start level shifted accordingly). -/
noncomputable def delWordAt (T : Set (α × ℤ)) (c : α → ℤ) (a : ℤ) (L : List (α × Bool)) :
    List ((α × ℤ) × Bool) := by
  classical
  exact (decor c a L).filterMap
    (fun p => if coverEdge p ∈ T then none else some (coverEdge p, p.2))

theorem delWord_eq_delWordAt (T : Set (α × ℤ)) (c : α → ℤ) (L : List (α × Bool)) :
    delWord T c L = delWordAt T c 0 L := rfl

@[simp] theorem delWordAt_nil (T : Set (α × ℤ)) (c : α → ℤ) (a : ℤ) :
    delWordAt T c a ([] : List (α × Bool)) = [] := rfl

/-- The head of the recursion formula is the traversal itself. -/
theorem coverEdge_trav_pair (c : α → ℤ) (a : ℤ) (p : α × Bool) :
    (coverEdge (trav c a p), (trav c a p).2) = trav c a p := by
  obtain ⟨x, b⟩ := p
  cases b <;> rfl

/-- The recursion of the deleted word at a letter whose edge lies in `T`: the traversal contributes
nothing. -/
theorem delWordAt_cons_of_mem (T : Set (α × ℤ)) (c : α → ℤ) (a : ℤ) (p : α × Bool)
    (L : List (α × Bool)) (h : coverEdge (trav c a p) ∈ T) :
    delWordAt T c a (p :: L) = delWordAt T c (a + linc c p) L := by
  classical
  unfold delWordAt
  rw [decor_cons]
  exact List.filterMap_cons_none (by rw [if_pos h])

/-- The recursion of the deleted word at a letter whose edge does not lie in `T`: the traversal
contributes the letter `(edge, sign)`. -/
theorem delWordAt_cons_of_notMem (T : Set (α × ℤ)) (c : α → ℤ) (a : ℤ) (p : α × Bool)
    (L : List (α × Bool)) (h : coverEdge (trav c a p) ∉ T) :
    delWordAt T c a (p :: L) = trav c a p :: delWordAt T c (a + linc c p) L := by
  classical
  unfold delWordAt
  rw [decor_cons, List.filterMap_cons_some (by rw [if_neg h]), coverEdge_trav_pair]

end Work.OROneRel
