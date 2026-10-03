/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The finite rooted trees as a rational `U`-semiring, and the DHS04 tree order

[JZLA20, §4.1] makes the finite rooted trees `T` into a `U`-semiring with the *trivial*
`U`-action (`uX = Xu = X`) and the rational operation `X⋄ = exp (exp X)`.  This is a rational
`U`-semiring for every group `U`.

This file also assembles the tree order of [DHS04, Lemma 3.3] (as developed in
`Submission/Work/ORHughesFree/Tree/order_alg.lean` for the concrete trees) into a model
`RootedTrees Tree` of [JZLA20, §4.1].
-/
import Mathlib
import Submission.Work.ORHughesFree.JZLA20
import Submission.Work.ORHughesFree.TreeInstances
import Submission.Work.ORHughesFree.TreeAlgebra
import Submission.Work.ORHughesFree.Tree.order_alg

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- The finite rooted trees form a semiring: `+` identifies roots, `*` is the product of
[JZLA20, §4.1], and `0`, `1` are the one-vertex and one-edge trees. -/
noncomputable instance instSemiringTree : Semiring Tree where
  zero_mul := Tree.zero_mul
  mul_zero := Tree.mul_zero
  left_distrib := Tree.left_distrib
  right_distrib := fun x y z => by
    rw [Tree.mul_comm (x + y) z, Tree.mul_comm x z, Tree.mul_comm y z, Tree.left_distrib]

/-- The rational operation on the tree semiring: `X⋄ = exp (exp X)` for `X ≠ 0`, and `0⋄ = 0`.
There is no `DecidableEq Tree`, hence the `classical` in the definition. -/
noncomputable def treeRatOp (x : Tree) : Tree := by
  classical
  exact if x = 0 then 0 else Tree.exp (Tree.exp x)

theorem treeRatOp_zero : treeRatOp (0 : Tree) = 0 := by
  rw [treeRatOp]; simp

theorem treeRatOp_of_ne {x : Tree} (h : x ≠ 0) : treeRatOp x = Tree.exp (Tree.exp x) := by
  rw [treeRatOp]; simp [h]

/-- **[JZLA20, §4.1]**: the finite rooted trees form a rational `U`-semiring with trivial
`U`-action and rational operation `X⋄ = exp (exp X)`.  Since `⋄` must fix `0`
(`RationalUSemiring.ratOp_zero`) the value at `X = 0` is overridden to `0`; the paper's `Tree`
([JZLA20, Lemma 4.3]) is a morphism of *`U`-semirings*, not of rational `U`-semirings, and
[JZLA20, Lemma 4.3(xi)] is stated for `X ≠ 0`. -/
noncomputable def treeRational (U : Type) [Group U] : RationalUSemiring U Tree where
  ratOp := treeRatOp
  smul _ x := x
  smulRight x _ := x
  smul_eq_mul := fun _ _ => by simp
  smulRight_eq_mul := fun _ _ => by simp
  smul_mul := fun _ _ => by simp
  smul_one_one := rfl
  smulRight_one_one := rfl
  smulRight_one := fun _ => rfl
  rat_smul := fun _ _ r => by
    by_cases h : r = 0
    · subst h; rw [treeRatOp_zero]
    · rw [treeRatOp_of_ne h]
  ratOp_zero := treeRatOp_zero

/-- **The finite rooted trees with the DHS04 well-order** ([JZLA20, §4.1]): the tree semiring of
`rootedTreeAlgebra` together with the recursive Dershowitz–Manna order of
`Submission/Work/ORHughesFree/Tree/order_defs.lean`. -/
noncomputable def treeRootedTrees : RootedTrees Tree :=
  { rootedTreeAlgebra with
    le := Tree.le
    le_refl := Tree.le_refl
    le_antisymm := Tree.le_antisymm
    le_trans := Tree.le_trans
    le_total := Tree.le_total
    le_wf := Tree.le_wf
    add_le_add := Tree.le_add
    add_le_add_eq := Tree.le_add_eq
    mul_le_mul := Tree.le_mul
    mul_le_mul_eq := Tree.le_mul_eq }

@[simp]
theorem treeRootedTrees_le (x y : Tree) : treeRootedTrees.le x y ↔ Tree.le x y := Iff.rfl

@[simp]
theorem treeRootedTrees_exp (x : Tree) : treeRootedTrees.exp x = Tree.exp x := rfl

/-! ### Elementary facts on the tree semiring

These are the facts about `0`, `1`, `+`, `*` and `exp` in the tree semiring that are used to
control the complexity map `Tree : Rat(U) ∪ {0} → T` ([JZLA20, Lemma 4.3]). -/

namespace Tree

/-- The family of a product has multiplicative cardinality. -/
private theorem fam_card_mul (x y : Tree) : (fam (x * y)).card =
    (fam x).card * (fam y).card := by
  rw [fam_mul, Multiset.card_bind]
  rw [show Multiset.map (Multiset.card ∘ fun a => Multiset.map (fun b => a + b) (fam y)) (fam x)
      = Multiset.map (fun _ => (fam y).card) (fam x) from
    Multiset.map_congr rfl (fun a _ => Multiset.card_map (fun b => a + b) (fam y))]
  rw [show Multiset.map (fun _ => (fam y).card) (fam x)
      = Multiset.replicate (fam x).card (fam y).card from Multiset.map_const _ _]
  rw [Multiset.sum_replicate]
  simp

/-- A sum of trees is the one-vertex tree only if both summands are. -/
theorem add_eq_zero_iff (a b : Tree) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hf : fam a + fam b = 0 := by rw [← fam_add, h, fam_zero]
    have hc : (fam a).card + (fam b).card = 0 := by
      rw [← Multiset.card_add, hf, Multiset.card_zero]
    obtain ⟨ha, hb⟩ := Nat.add_eq_zero_iff.mp hc
    exact ⟨fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp ha),
      fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp hb)⟩
  · rintro ⟨rfl, rfl⟩
    rw [add_zero]

/-- A product of trees is the one-vertex tree only if one of the factors is. -/
theorem mul_eq_zero (a b : Tree) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  have key : a * b = 0 → a = 0 ∨ b = 0 := by
    intro h
    have hcard : (fam a).card * (fam b).card = 0 := by
      have h2 := fam_card_mul a b
      rw [h, fam_zero, Multiset.card_zero] at h2
      exact h2.symm
    rcases Nat.mul_eq_zero.mp hcard with h' | h'
    · exact Or.inl (fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp h'))
    · exact Or.inr (fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp h'))
  exact ⟨key, fun h => h.elim (fun h => by rw [h, zero_mul])
    (fun h => by rw [h, mul_zero])⟩

/-- `exp x` is never the one-vertex tree. -/
theorem exp_ne_zero (x : Tree) : Tree.exp x ≠ 0 := by
  intro h
  have h1 : fam (Tree.exp x) = ({x} : Multiset Tree) := Tree.fam_exp x
  rw [h, Tree.fam_zero] at h1
  exact Multiset.singleton_ne_zero x h1.symm

/-- The one-edge tree is not the one-vertex tree. -/
theorem one_ne_zero : (1 : Tree) ≠ 0 := by
  rw [show (1 : Tree) = Tree.exp (0 : Tree) from rfl]
  exact Tree.exp_ne_zero 0

/-- Adding a tree does not change the sum unless the added tree is the one-vertex tree. -/
theorem add_eq_self_iff (a b : Tree) : a + b = a ↔ b = 0 := by
  constructor
  · intro h
    have hf : fam a + fam b = fam a := by rw [← fam_add, h]
    have hc : (fam b).card = 0 := by
      have h2 : (fam a).card + (fam b).card = (fam a).card := by
        rw [← Multiset.card_add, hf]
      omega
    exact fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp hc)
  · intro h
    rw [h, add_zero]

end Tree

end Work.ORHughesFree
