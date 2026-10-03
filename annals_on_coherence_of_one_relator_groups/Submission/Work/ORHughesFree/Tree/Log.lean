/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The logarithm and the width of a finite rooted tree

[DHS04, §5] and [JZLA20, Lemma 4.3(vii)–(xiii)] use two numerical invariants of a finite rooted
tree `X`:

* `log X`, the largest element of the family `fam X` of `X` (the family is the multiset of the
  rooted subtrees obtained by deleting the root); it is the `-∞` "least element" adjoined in
  [JZLA20, §4.2] when `X = 0` is the one-vertex tree, so here it is an element of `Option Tree`
  (`none` for `x = 0`; the `Option` is ordered by declaring `none` least);
* `wid X`, the *width* of `X`, i.e. the number of elements of `fam X` = the number of edges
  incident to the root.

They are related to the tree order `Tree.lt` of [DHS04, Lemma 3.3] by: `X ≤ Y` as soon as
`log X < log Y`, and the elements of `fam X` are at most `log X` with `log X ∈ fam X`.

This file only contains the definitions and the existence of the maximum; the API is in
`Submission/Work/ORHughesFree/Tree/log_lemmas.lean`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.order_le
import Submission.Work.ORHughesFree.Tree.fam_basic
import Submission.Work.ORHughesFree.Tree.fam_exp
import Submission.Work.ORHughesFree.Tree.fam_mul
import Submission.Work.ORHughesFree.Tree.sum_fam
import Submission.Work.ORHughesFree.Tree.order_alg

set_option autoImplicit false

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- The family of a nonempty tree has a largest element. -/
theorem exists_fam_max (x : Tree) (hx : fam x ≠ 0) :
    ∃ b ∈ fam x, ∀ a ∈ fam x, Tree.le a b := by
  have key : ∀ s : Multiset Tree, s ≠ 0 → ∃ b ∈ s, ∀ a ∈ s, Tree.le a b := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro h; exact absurd rfl h
    · intro y s ih _
      by_cases hs : s = 0
      · subst hs
        refine ⟨y, Multiset.mem_cons_self y 0, ?_⟩
        intro a ha
        rcases Multiset.mem_cons.mp ha with h | ha
        · rw [h]; exact Tree.le_refl _
        · exact absurd ha (by simp)
      · obtain ⟨b, hb, hmax⟩ := ih hs
        rcases Tree.le_total y b with hyb | hby
        · refine ⟨b, Multiset.mem_cons_of_mem hb, ?_⟩
          intro a ha
          rcases Multiset.mem_cons.mp ha with h | ha
          · rw [h]; exact hyb
          · exact hmax a ha
        · refine ⟨y, Multiset.mem_cons_self y s, ?_⟩
          intro a ha
          rcases Multiset.mem_cons.mp ha with h | ha
          · rw [h]; exact Tree.le_refl _
          · exact Tree.le_trans (hmax a ha) hby
  exact key (fam x) hx

/-- **The logarithm of a finite rooted tree**: the largest element of its family, i.e. the largest
rooted subtree obtained by deleting the root.  It is `none` for the one-vertex tree `0`. -/
noncomputable def log (x : Tree) : Option Tree := by
  classical
  exact if h : fam x = 0 then none else some (Classical.choose (exists_fam_max x h))

/-- **The width of a finite rooted tree**: the number of its children, i.e. the number of edges
incident to the root. -/
noncomputable def wid (x : Tree) : ℕ := (fam x).card

/-- The max of two optional trees, with `none` as least element. -/
noncomputable def omax : Option Tree → Option Tree → Option Tree
  | none, y => y
  | some x, none => some x
  | some x, some y => by classical exact if Tree.le x y then some y else some x

@[simp] theorem omax_none_left (y : Option Tree) : omax none y = y := rfl

@[simp] theorem omax_none_right (x : Option Tree) : omax x none = x := by
  cases x <;> rfl

/-! ### The logarithm is the largest element of the family -/

/-- **`log` is the largest element of the family**: `log x = none` for the one-vertex tree, and
`log x = some b` with `b ∈ fam x` the maximum of `fam x` otherwise. -/
theorem log_spec (x : Tree) :
    (x = 0 → log x = none) ∧
    (∀ b, log x = some b → b ∈ fam x ∧ ∀ a ∈ fam x, Tree.le a b) ∧
    (x ≠ 0 → ∃ b, log x = some b) := by
  classical
  have hzero : fam x = 0 ↔ x = 0 := Tree.fam_eq_zero_iff
  refine ⟨fun hx => ?_, fun b hb => ?_, fun hx => ?_⟩
  · show dite (fam x = 0) _ _ = none
    rw [dif_pos (hzero.mpr hx)]
  · cases hb' : log x with
    | none => exact absurd hb (by simp [hb'])
    | some c =>
        have hne : fam x ≠ 0 := by
          intro h
          rw [log, dif_pos h] at hb'
          exact absurd hb' (by simp)
        have hc : c = Classical.choose (exists_fam_max x hne) := by
          rw [log, dif_neg hne] at hb'
          exact Option.some.inj hb'.symm
        have hbc : b = c := Option.some.inj (hb.symm.trans hb')
        subst hbc
        subst hc
        exact Classical.choose_spec (exists_fam_max x hne)
  · refine ⟨Classical.choose (exists_fam_max x (fun h => hx (hzero.mp h))), ?_⟩
    rw [log, dif_neg (fun h => hx (hzero.mp h))]

/-- A summand of a sum of trees is below the sum. -/
theorem le_sum_of_mem (s : Multiset Tree) (a : Tree) (ha : a ∈ s) : Tree.le a s.sum := by
  revert ha a
  refine Multiset.induction_on (p := fun s => ∀ a : Tree, a ∈ s → Tree.le a s.sum) s ?_ ?_
  · intro a ha; exact absurd ha (by simp)
  · intro y s ih a ha
    rw [Multiset.sum_cons]
    rcases Multiset.mem_cons.mp ha with h | ha
    · rw [h]
      simpa using Tree.le_add (Tree.le_refl y) (Tree.le_zero s.sum)
    · exact Tree.le_trans (ih a ha)
        (by simpa using Tree.le_add (Tree.le_zero y) (Tree.le_refl s.sum))

/-- `exp (log x) ≤ x`: the child of `x` of maximal complexity, raised by `exp`, is below `x`. -/
theorem le_exp_log {x a : Tree} (h : log x = some a) : Tree.le (Tree.exp a) x := by
  obtain ⟨hmem, -⟩ := (log_spec x).2.1 a h
  rw [← Tree.sum_fam x]
  exact le_sum_of_mem _ _ (Multiset.mem_map_of_mem Tree.exp hmem)

/-- A tree of width one is a single root extension of its maximal child. -/
theorem eq_exp_log_of_wid_eq_one {x a : Tree} (h : log x = some a) (hw : wid x = 1) :
    x = Tree.exp a := by
  obtain ⟨hmem, -⟩ := (log_spec x).2.1 a h
  have hcard : (fam x).card = 1 := hw
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hcard
  have hba : b = a := by
    rw [hb] at hmem
    rw [Multiset.mem_singleton] at hmem
    exact hmem.symm
  subst hba
  rw [← Tree.sum_fam x, hb, Multiset.map_singleton, Multiset.sum_singleton]

/-- The width of a single root extension is one. -/
@[simp] theorem wid_exp (x : Tree) : wid (Tree.exp x) = 1 := by
  rw [wid, Tree.fam_exp]
  rfl

/-- The width is multiplicative. -/
theorem wid_mul (x y : Tree) : wid (x * y) = wid x * wid y := by
  rw [wid, wid, wid, Tree.fam_mul, Multiset.card_bind]
  rw [show Multiset.map (Multiset.card ∘ fun a => Multiset.map (fun b => a + b) (fam y)) (fam x)
      = Multiset.map (fun _ => (fam y).card) (fam x) from
    Multiset.map_congr rfl (fun a _ => Multiset.card_map (fun b => a + b) (fam y))]
  rw [show Multiset.map (fun _ => (fam y).card) (fam x)
      = Multiset.replicate (fam x).card (fam y).card from Multiset.map_const _ _]
  rw [Multiset.sum_replicate, smul_eq_mul]

end Work.ORHughesFree.Tree
