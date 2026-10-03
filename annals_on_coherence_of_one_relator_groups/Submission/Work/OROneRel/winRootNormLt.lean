import Mathlib
import Submission.Work.OROneRel.winBasisDefs

/-!
# The window root is strictly shorter than the relator

Let `c : α → ℤ`, `u : FreeGroup α`, `Wt : ℤ → FreeGroup α` a gauge and `[lo,hi]` a window.  The
*candidate root* `winRoot Wt c lo hi u` (`Submission.Work.OROneRel.winBasisDefs`) is the word over
the alphabet `β = winBeta Wt c lo hi` (the edges of the window of non-trivial loop class) spelled by
the traversals of the walk of `u` whose edge lies in `β`; the traversals through tree edges
(`winTree`, i.e. edges of trivial loop class) are deleted.

This file proves that, as soon as the walk of `u` traverses at least one tree edge of the window
(hypothesis `hdel`), the root is strictly shorter than `u`:

  `relatorNorm (winRoot Wt c lo hi u) < relatorNorm u`.

The argument is purely list-theoretic:

* `relatorNorm (winRoot …) ≤ (winRootList …).length`, because `winRoot = FreeGroup.mk winRootList`
  and `FreeGroup.norm_mk_le`;
* `winRootList` is the `filterMap` of `decor c 0 (wordOf u)` that keeps exactly the traversals of
  non-trivial loop class lying in the window; the traversal supplied by `hdel` has trivial loop
  class, hence is sent to `none`, so the `filterMap` drops at least one entry;
* `(decor c 0 (wordOf u)).length = relatorNorm u` (`decor_length`), and `hdel` exhibits an entry of
  `decor c 0 (wordOf u)`, so this length is positive.

The hypotheses `hcyc` and `hwin` are not used by the estimate (deleting more edges only shortens the
word); they are present for API uniformity with the companions `winRho_winRoot` and
`winFreiheitssatz`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Auxiliary list lemmas -/

/-- The length of a `filterMap` is at most the length of the list. -/
private theorem winRootNormLt_length_filterMap_le {β γ : Type*} (F : β → Option γ) (l : List β) :
    (l.filterMap F).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons y t ih =>
      rw [List.filterMap_cons]
      split <;> simp only [List.length_cons] <;> omega

/-- A `filterMap` that sends an element of its list to `none` drops at least one element, so its
length is at most `l.length - 1`. -/
private theorem winRootNormLt_length_filterMap_le_pred {β γ : Type*} (F : β → Option γ) :
    ∀ (l : List β) (x : β), x ∈ l → F x = none → (l.filterMap F).length ≤ l.length - 1 := by
  intro l
  induction l with
  | nil => intro x hx _; exact absurd hx (by simp)
  | cons y t ih =>
      intro x hx hF
      rcases List.mem_cons.mp hx with rfl | hxt
      · -- the dropped element is the head
        have heq : List.filterMap F (x :: t) = List.filterMap F t := by
          rw [List.filterMap_cons, hF]
        have hlen : (List.filterMap F t).length ≤ t.length :=
          winRootNormLt_length_filterMap_le F t
        rw [heq, List.length_cons]
        omega
      · -- the dropped element is in the tail
        have h1 : (List.filterMap F (y :: t)).length ≤ (List.filterMap F t).length + 1 := by
          rw [List.filterMap_cons]; cases h : F y <;> simp
        have h2 := ih x hxt hF
        have htne : t ≠ [] := by rintro rfl; exact absurd hxt (by simp)
        have htpos : 1 ≤ t.length := List.length_pos_iff.mpr htne
        rw [List.length_cons]
        omega

/-- **The window root list drops a traversal through a tree edge.**  If some traversal of the walk
of `u` passes through an edge of trivial loop class (`winTree`), then `winRootList` — whose
`filterMap` keeps exactly the traversals through edges of the window of *non*-trivial loop class —
has strictly fewer entries than the decorated word of `u`. -/
private theorem winRootNormLt_winRootList_length_le (Wt : ℤ → FreeGroup α) (c : α → ℤ)
    (lo hi : ℤ) (u : FreeGroup α)
    (hdel : ∃ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winTree Wt c lo hi) :
    (winRootList Wt c lo hi u).length ≤ (decor c 0 (wordOf u)).length - 1 := by
  classical
  obtain ⟨p, hpD, hptree⟩ := hdel
  have hclass : coverClassAt Wt c (coverEdge p) = 1 := (mem_winTree.mp hptree).2
  -- The filter function of `winRootList`, named so that it can be applied at `p`.
  let F : (α × ℤ) × Bool → Option (winBeta Wt c lo hi × Bool) :=
    fun q => if h : coverEdge q ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge q) ≠ 1 then
      some (⟨coverEdge q, h.1, h.2⟩, q.2) else none
  have hdrop : F p = none := by
    dsimp only [F]
    rw [dif_neg (fun h => h.2 hclass)]
  have hEq : winRootList Wt c lo hi u = (decor c 0 (wordOf u)).filterMap F := by
    rw [winRootList]
  rw [hEq]
  exact winRootNormLt_length_filterMap_le_pred F _ p hpD hdrop

/-- The length of the decorated word of `u` is the relator norm of `u`. -/
private theorem winRootNormLt_decor_length_eq_relatorNorm (c : α → ℤ) (u : FreeGroup α) :
    (decor c 0 (wordOf u)).length = relatorNorm u := by
  classical
  rw [decor_length, relatorNorm, wordOf, FreeGroup.norm]

/-! ## The target -/

theorem winRootNormLt {α : Type*} {c : α → ℤ} {u : FreeGroup α} (Wt : ℤ → FreeGroup α)
    (lo hi : ℤ) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hdel : ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi) :
    Work.OROneRel.relatorNorm (Work.OROneRel.winRoot Wt c lo hi u) <
      Work.OROneRel.relatorNorm u := by
  classical
  -- The root has at most as many letters as its defining list.
  have h1 : relatorNorm (winRoot Wt c lo hi u) ≤ (winRootList Wt c lo hi u).length := by
    rw [relatorNorm, winRoot]
    exact FreeGroup.norm_mk_le
  -- The defining list drops the traversal through the tree edge of `hdel`.
  have h2 : (winRootList Wt c lo hi u).length ≤ (decor c 0 (wordOf u)).length - 1 :=
    winRootNormLt_winRootList_length_le Wt c lo hi u hdel
  obtain ⟨p, hpD, -⟩ := hdel
  -- The decorated word has the length of the relator, and is non-empty.
  have hne : decor c 0 (wordOf u) ≠ [] := by
    rintro h; rw [h] at hpD; simp at hpD
  have hpos : 1 ≤ (decor c 0 (wordOf u)).length := List.length_pos_iff.mpr hne
  calc
    relatorNorm (winRoot Wt c lo hi u) ≤ (winRootList Wt c lo hi u).length := h1
    _ ≤ (decor c 0 (wordOf u)).length - 1 := h2
    _ < (decor c 0 (wordOf u)).length := by omega
    _ = relatorNorm u := winRootNormLt_decor_length_eq_relatorNorm c u

end Work.OROneRel
