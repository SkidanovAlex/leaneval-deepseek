/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A tree is below its double root extension

We prove that `x < exp (exp x)` for every finite rooted tree `x` (the hypothesis `x ≠ 0` required
by the statement is in fact unnecessary).

The order `Tree.lt` is the recursive Dershowitz–Manna ordering of the family `fam x` of children
(`Tree.lt_iff`): `x < y` iff `fam y = X + Z` over `fam x = X + Y` with `Z ≠ 0` and every element of
`Y` strictly below some element of `Z`.  So `lt x (exp (exp x))` follows from
`fam (exp (exp x)) = {exp x}` once we know that every child `a ∈ fam x` satisfies `a < exp x`.

The latter is a single induction on the number of edges:

* `lt_of_mem_fam : a ∈ fam x → a < x`, proved by strong induction on `edge x`.  If `a` is a child
  of `x`, the witnesses `X = 0`, `Y = fam a`, `Z = fam x` reduce `a < x` to the instance
  `lt y a` for `y ∈ fam a` of the induction hypothesis, which applies because
  `edge y < edge a < edge x`;
* `lt_exp_self : x < exp x`, which is `lt_of_mem_fam` again with `fam (exp x) = {x}`.

Since `lt a x` and `x < exp x` give `a < exp x` by transitivity, the Dershowitz–Manna witnesses
`X = 0`, `Y = fam x`, `Z = {exp x}` for the pair `(x, exp (exp x))` are then available.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree.Log
import Submission.Work.ORHughesFree.Tree.edge
import Submission.Work.ORHughesFree.Tree.fam_basic
import Submission.Work.ORHughesFree.Tree.fam_exp
import Submission.Work.ORHughesFree.Tree.order_good
import Submission.Work.ORHughesFree.Tree.order_le

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- **A child is strictly below its parent.**  If `a` is an element of the family of `x`, then
`a < x`.

Proof by strong induction on `edge x`.  Reading `a < x` through `lt_iff`, the witnesses
`X = 0`, `Y = fam a`, `Z = fam x` (note `fam x ≠ 0` since `a` lies in it) require that every
`y ∈ fam a` be strictly below some element of `fam x`; taking that element to be `a` itself, we
need `y < a`, which is the induction hypothesis at `a`, applicable because
`edge y < edge a < edge x`. -/
theorem lt_of_mem_fam {a x : Tree} (h : a ∈ fam x) : lt a x := by
  have key : ∀ n, ∀ x : Tree, edge x = n → ∀ a : Tree, a ∈ fam x → lt a x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx a ha
      rw [lt_iff]
      refine ⟨0, fam a, fam x, ?_, by simp, by simp, ?_⟩
      · intro hf; rw [hf] at ha; simp at ha
      · intro y hy
        exact ⟨a, ha, ih (edge a) (by rw [← hx]; exact edge_lt_of_mem_fam ha) a rfl y hy⟩
  exact key (edge x) x rfl a h

/-- **A tree is strictly below its root extension** `exp x` (the tree with the single child `x`).
This is `lt_of_mem_fam` read through `fam (exp x) = {x}`: `x < exp x` needs every `a ∈ fam x` to be
strictly below the unique child `x` of `exp x`, which is exactly `lt_of_mem_fam`. -/
theorem lt_exp_self (x : Tree) : lt x (exp x) := by
  rw [lt_iff]
  refine ⟨0, fam x, {x}, ?_, by simp, ?_, ?_⟩
  · simp
  · rw [fam_exp]; simp
  · intro a ha
    exact ⟨x, Multiset.mem_singleton_self x, lt_of_mem_fam ha⟩

/-- **A nonzero tree is strictly below its double root extension**: `x < exp (exp x)`.  The
witnesses `X = 0`, `Y = fam x`, `Z = {exp x}` for the Dershowitz–Manna decomposition of
`fam (exp (exp x)) = {exp x}` over `fam x` need every child `a ∈ fam x` to satisfy `a < exp x`,
which follows from `a < x` (`lt_of_mem_fam`) and `x < exp x` (`lt_exp_self`). -/
theorem lt_exp_exp {x : Work.ORHughesFree.Tree} (hx : x ≠ 0) :
    Work.ORHughesFree.Tree.lt x (Work.ORHughesFree.Tree.exp (Work.ORHughesFree.Tree.exp x)) := by
  rw [lt_iff]
  refine ⟨0, fam x, {exp x}, ?_, by simp, ?_, ?_⟩
  · simp
  · rw [fam_exp]; simp
  · intro a ha
    exact ⟨exp x, Multiset.mem_singleton_self _,
      lt_trans (lt_of_mem_fam ha) (lt_exp_self x)⟩

end Work.ORHughesFree.Tree
