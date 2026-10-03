import Mathlib
import Submission.Work.OROneRel.winGateDefs
import Submission.Work.OROneRel.gaugeLevelDefs
import Submission.Work.OROneRel.decor_pow_flatMap

/-!
# The live (non-tree) traversals of a decorated walk

The decorated word `decor c i L` of a word `L` is a walk on the levels `ℤ`: the `j`-th decorated
letter `p = ((x,i),b)` is the traversal of the edge `coverEdge p = (x,i)` of the level graph from the
level `coverSrc c p` to the level `coverTgt c p`, with loop class
`coverClassAt Wt c (coverEdge p)` in the `b = true` direction (and its inverse for `b = false`).

This file fixes the bookkeeping of the **live** traversals of such a walk, i.e. those whose edge lies
in a window `winE c lo hi` and has non-trivial loop class.  They are the letters of the vertex relator
`winRoot` of the window decomposition (`Submission/Work/OROneRel/winBasisDefs.lean`), and the
complementary *tree* traversals contribute the identity to the class map.

* `isLive Wt c lo hi p` -- the traversal `p` is live;
* `liveDecor Wt c lo hi J` -- the sublist of live traversals of the walk `J`, as a word over the
  alphabet `winBeta Wt c lo hi`; for `J = decor c 0 (wordOf u)` this is `winRootList`
  (`winRootList_eq_liveDecor`);
* `mem_liveDecor` -- membership, in terms of the traversal of `J` it comes from;
* `liveDecor_append` / `liveDecor_cons_of_live` / `liveDecor_cons_of_not_live` -- additivity;
* `liveDecor_eq_nil_of_forall` -- a tree stretch has no live traversal;
* `exists_first_live` -- the first live traversal of a walk with a live traversal;
* `coverTgt_eq_coverSrc_of_opposite` / `coverSrc_eq_coverTgt_of_opposite` -- the two traversals of
  one edge run in opposite directions;
* `relatorLetters_mk_of_isReduced` -- the letters of a reduced word.

The point of the development is that for the walk of `u` the live word is always **reduced**
(`Submission/Work/OROneRel/liveDecorReduced.lean`): a stretch of the walk whose live part multiplies
to `1` in the free group on `winBeta` is trivial, because its word in `F α` is a subword of the
reduced word of `u`, hence itself reduced.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **A live traversal**: its edge lies in the window `winE c lo hi` and has non-trivial loop
class. -/
abbrev isLive (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (p : (α × ℤ) × Bool) : Prop :=
  coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1

/-- **The live traversals of a decorated walk**: those whose edge lies in the window `winE c lo hi`
and has non-trivial loop class, with the sign of the traversal.  The alphabet is the vertex alphabet
`winBeta Wt c lo hi`. -/
noncomputable def liveDecor (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (J : List ((α × ℤ) × Bool)) : List (winBeta Wt c lo hi × Bool) := by
  classical
  exact J.filterMap (fun p =>
    if h : isLive Wt c lo hi p then
      some (⟨coverEdge p, h.1, h.2⟩, p.2)
    else none)

/-- The vertex relator of the window decomposition is the live word of the walk of `u`. -/
@[simp] theorem winRootList_eq_liveDecor (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (u : FreeGroup α) :
    winRootList Wt c lo hi u = liveDecor Wt c lo hi (decor c 0 (wordOf u)) := rfl

@[simp] theorem liveDecor_nil (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    liveDecor Wt c lo hi ([] : List ((α × ℤ) × Bool)) = [] := rfl

/-- **Membership in the live word**: a live letter is the pair `(edge, sign)` of a traversal of
`J`. -/
theorem mem_liveDecor {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    {J : List ((α × ℤ) × Bool)} {x : winBeta Wt c lo hi × Bool} :
    x ∈ liveDecor Wt c lo hi J ↔
      ∃ p ∈ J, coverEdge p = (x.1).1 ∧ p.2 = x.2 := by
  classical
  rw [liveDecor, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hpx⟩
    by_cases h : isLive Wt c lo hi p
    · rw [dif_pos h] at hpx
      have h2 := Option.some.inj hpx
      exact ⟨p, hp, congrArg (fun y : winBeta Wt c lo hi × Bool => (y.1).1) h2,
        congrArg (fun y : winBeta Wt c lo hi × Bool => y.2) h2⟩
    · rw [dif_neg h] at hpx
      exact absurd hpx (by simp)
  · rintro ⟨p, hp, h1, h2⟩
    have h : isLive Wt c lo hi p := by
      unfold isLive
      rw [h1]
      exact x.1.2
    refine ⟨p, hp, ?_⟩
    rw [dif_pos h]
    exact congrArg some (Prod.ext (Subtype.ext h1) h2)

/-- A live traversal of a walk is a live letter of its live word. -/
theorem mem_liveDecor_of_mem {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    {J : List ((α × ℤ) × Bool)} {p : (α × ℤ) × Bool} (hp : p ∈ J)
    (h : isLive Wt c lo hi p) :
    ((⟨coverEdge p, h.1, h.2⟩ : winBeta Wt c lo hi), p.2) ∈ liveDecor Wt c lo hi J :=
  mem_liveDecor.mpr ⟨p, hp, rfl, rfl⟩

/-- A live letter of a live word comes from a traversal of the walk. -/
theorem exists_mem_of_mem_liveDecor {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    {J : List ((α × ℤ) × Bool)} {x : winBeta Wt c lo hi × Bool}
    (hx : x ∈ liveDecor Wt c lo hi J) :
    ∃ p ∈ J, coverEdge p = (x.1).1 ∧ p.2 = x.2 :=
  mem_liveDecor.mp hx

/-- **Every live letter lies in the window and has non-trivial loop class.** -/
theorem liveDecor_window {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    {J : List ((α × ℤ) × Bool)} {x : winBeta Wt c lo hi × Bool}
    (hx : x ∈ liveDecor Wt c lo hi J) :
    (x.1).1 ∈ winE c lo hi ∧ coverClassAt Wt c (x.1).1 ≠ 1 := x.1.2

/-- The live word of a concatenation is the concatenation of the live words. -/
theorem liveDecor_append (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (J₁ J₂ : List ((α × ℤ) × Bool)) :
    liveDecor Wt c lo hi (J₁ ++ J₂) =
      liveDecor Wt c lo hi J₁ ++ liveDecor Wt c lo hi J₂ := by
  classical
  rw [liveDecor, liveDecor, liveDecor, List.filterMap_append]

/-- The live word of a walk beginning with a live traversal. -/
theorem liveDecor_cons_of_live (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (p : (α × ℤ) × Bool) (J : List ((α × ℤ) × Bool)) (h : isLive Wt c lo hi p) :
    liveDecor Wt c lo hi (p :: J) =
      ((⟨coverEdge p, h.1, h.2⟩, p.2) : winBeta Wt c lo hi × Bool) ::
        liveDecor Wt c lo hi J := by
  classical
  rw [liveDecor, liveDecor, List.filterMap_cons, dif_pos h]

/-- The live word of a walk beginning with a tree traversal. -/
theorem liveDecor_cons_of_not_live (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (p : (α × ℤ) × Bool) (J : List ((α × ℤ) × Bool)) (h : ¬ isLive Wt c lo hi p) :
    liveDecor Wt c lo hi (p :: J) = liveDecor Wt c lo hi J := by
  classical
  rw [liveDecor, liveDecor, List.filterMap_cons, dif_neg h]

/-- **A tree stretch has no live traversal.** -/
theorem liveDecor_eq_nil_of_forall (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (J : List ((α × ℤ) × Bool)) (h : ∀ p ∈ J, ¬ isLive Wt c lo hi p) :
    liveDecor Wt c lo hi J = [] := by
  classical
  induction J with
  | nil => rfl
  | cons p J ih =>
    rw [liveDecor_cons_of_not_live Wt c lo hi p J (h p (by simp))]
    exact ih (fun q hq => h q (by simp [hq]))

/-- **The first live traversal.**  If a walk has a live traversal, it splits as a tree stretch
followed by a live traversal followed by the rest. -/
theorem exists_first_live (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (J : List ((α × ℤ) × Bool)) (h : liveDecor Wt c lo hi J ≠ []) :
    ∃ (A : List ((α × ℤ) × Bool)) (p : (α × ℤ) × Bool) (B : List ((α × ℤ) × Bool)),
      J = A ++ p :: B ∧ liveDecor Wt c lo hi A = [] ∧
        ∃ (hL : isLive Wt c lo hi p),
          liveDecor Wt c lo hi J =
            ((⟨coverEdge p, hL.1, hL.2⟩, p.2) : winBeta Wt c lo hi × Bool) ::
              liveDecor Wt c lo hi B := by
  classical
  induction J with
  | nil => exact absurd rfl h
  | cons q J ih =>
    by_cases hq : isLive Wt c lo hi q
    · refine ⟨[], q, J, by simp, by simp, hq, ?_⟩
      rw [liveDecor_cons_of_live Wt c lo hi q J hq]
    · have hJ : liveDecor Wt c lo hi J ≠ [] := by
        rwa [liveDecor_cons_of_not_live Wt c lo hi q J hq] at h
      obtain ⟨A, p, B, hAB, hA, hL, hlive⟩ := ih hJ
      exact ⟨q :: A, p, B, by simp [hAB], by
        rw [liveDecor_cons_of_not_live Wt c lo hi q A hq]; exact hA, hL, by
        rw [liveDecor_cons_of_not_live Wt c lo hi q J hq]; exact hlive⟩

/-- **The two traversals of one edge run in opposite directions**: the target of a traversal is the
source of the reversed traversal of the same edge. -/
theorem coverTgt_eq_coverSrc_of_opposite (c : α → ℤ) {p q : (α × ℤ) × Bool}
    (h1 : coverEdge p = coverEdge q) (h2 : p.2 ≠ q.2) :
    coverTgt c p = coverSrc c q := by
  obtain ⟨⟨x, i⟩, b⟩ := p
  obtain ⟨⟨x', i'⟩, b'⟩ := q
  simp only [coverEdge] at h1
  injection h1 with h1 h1'
  cases b <;> cases b' <;> simp_all [coverTgt, coverSrc]

/-- The same, in the other direction. -/
theorem coverSrc_eq_coverTgt_of_opposite (c : α → ℤ) {p q : (α × ℤ) × Bool}
    (h1 : coverEdge p = coverEdge q) (h2 : p.2 ≠ q.2) :
    coverSrc c p = coverTgt c q := by
  obtain ⟨⟨x, i⟩, b⟩ := p
  obtain ⟨⟨x', i'⟩, b'⟩ := q
  simp only [coverEdge] at h1
  injection h1 with h1 h1'
  cases b <;> cases b' <;> simp_all [coverTgt, coverSrc]

/-- **The letters of an element of a free group, read off a reduced word.** -/
theorem relatorLetters_mk_of_isReduced {β : Type u} {L : List (β × Bool)}
    (hL : FreeGroup.IsReduced L) (a : β) :
    a ∈ relatorLetters (FreeGroup.mk L) ↔ ∃ b : Bool, (a, b) ∈ L := by
  classical
  rw [relatorLetters, Set.mem_ofPred_eq, FreeGroup.toWord_mk, hL.reduce_eq]

end Work.OROneRel
