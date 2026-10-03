/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# Reducedness of the decorated word

The Magnus decoration `decor c a L` (see `Submission.Work.OROneRel.MagnusGenDefs`) rewrites a word
`L` over `α × Bool` into a word over `(α × ℤ) × Bool` by replacing each letter by the *traversal*
of the corresponding edge of the level graph `ℤ` (the levels being shifted by `linc`).

This file proves that this rewriting preserves and reflects reducedness:
`FreeGroup.IsReduced (decor c a L) ↔ FreeGroup.IsReduced L`.  The point is that two consecutive
traversals have equal edge exactly when the underlying `α`-letters are equal and either the signs
differ (in which case the traversals come back along the same edge) or the weight vanishes; in
either case this is exactly the cancellation that `IsReduced` forbids on the two sides.
-/
import Mathlib
import Submission.Work.OROneRel.delWordWalkDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **Adjacency of two consecutive traversals.**  For consecutive letters `p`, `q` of a word, the
two traversals at levels `a` and `a + linc c p` have the same *edge* precisely when `p` and `q`
have the same underlying generator and either they carry different signs, or the weight of that
generator vanishes. -/
theorem trav_head_eq_iff (c : α → ℤ) (a : ℤ) (p q : α × Bool) :
    (trav c a p).1 = (trav c (a + linc c p) q).1 ↔
      p.1 = q.1 ∧ (p.2 = q.2 → c p.1 = 0) := by
  obtain ⟨x, b⟩ := p
  obtain ⟨y, d⟩ := q
  cases b <;> cases d <;>
    simp only [trav, linc, Bool.false_eq_true, if_false, if_true, Prod.mk.injEq] <;>
    (by_cases hxy : x = y <;> simp [hxy, sub_eq_add_neg])

/-- **The adjacency condition of `IsReduced` is the same on both sides.**  For consecutive letters
`p`, `q`, the no-cancellation condition for the two traversals is equivalent to the
no-cancellation condition for `p`, `q` themselves.  (When the signs agree the traversals have the
same edge only if the weight vanishes, and then the combined condition is again exactly that the
signs agree.) -/
theorem trav_imp_iff (c : α → ℤ) (a : ℤ) (p q : α × Bool) :
    ((trav c a p).1 = (trav c (a + linc c p) q).1 → (trav c a p).2 = (trav c (a + linc c p) q).2) ↔
      (p.1 = q.1 → p.2 = q.2) := by
  rw [trav_head_eq_iff, trav_snd, trav_snd]
  constructor
  · intro h hpq
    by_cases hsign : p.2 = q.2
    · exact hsign
    · exact absurd (h ⟨hpq, fun hc => absurd hc hsign⟩) hsign
  · intro h hle
    exact h hle.1

/-- **Reducedness is preserved and reflected by the decoration**, with an arbitrary starting
level. -/
theorem isReduced_decor_iff_aux {α : Type u} (c : α → ℤ) (L : List (α × Bool)) :
    ∀ a, FreeGroup.IsReduced (decor c a L) ↔ FreeGroup.IsReduced L := by
  induction L with
  | nil => intro a; simp [decor]
  | cons p L ih =>
    intro a
    cases L with
    | nil => rw [decor_cons]; simp [decor]
    | cons q L' =>
      have hdec : decor c (a + linc c p) (q :: L') =
          trav c (a + linc c p) q :: decor c (a + linc c p + linc c q) L' := decor_cons ..
      have htail : FreeGroup.IsReduced
            (trav c (a + linc c p) q :: decor c (a + linc c p + linc c q) L') ↔
          FreeGroup.IsReduced (q :: L') := by
        rw [← hdec]
        exact ih (a + linc c p)
      rw [decor_cons, hdec, FreeGroup.isReduced_cons_cons, FreeGroup.isReduced_cons_cons]
      exact Iff.and (trav_imp_iff c a p q) htail

/-- The decoration of a reduced word is reduced. -/
theorem isReduced_decor {α : Type u} {c : α → ℤ} {a : ℤ} {L : List (α × Bool)}
    (h : FreeGroup.IsReduced L) : FreeGroup.IsReduced (decor c a L) :=
  (isReduced_decor_iff_aux c L a).mpr h

/-- The decoration of a word is reduced only if the word is reduced. -/
theorem isReduced_of_decor {α : Type u} {c : α → ℤ} {a : ℤ} {L : List (α × Bool)}
    (h : FreeGroup.IsReduced (decor c a L)) : FreeGroup.IsReduced L :=
  (isReduced_decor_iff_aux c L a).mp h

theorem isReduced_decor_iff {α : Type u} (c : α → ℤ) (a : ℤ) (L : List (α × Bool)) :
    FreeGroup.IsReduced (Work.OROneRel.decor c a L) ↔ FreeGroup.IsReduced L :=
  isReduced_decor_iff_aux c L a

end Work.OROneRel
