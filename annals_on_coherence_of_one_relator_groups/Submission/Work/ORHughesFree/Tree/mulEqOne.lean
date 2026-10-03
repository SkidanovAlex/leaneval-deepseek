/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The group of units of the tree monoid

`Tree` is the type of finite rooted trees up to isomorphism
(`Submission/Work/ORHughesFree/Tree.lean`), a commutative monoid under `*`
(`Submission/Work/ORHughesFree/TreeInstances.lean`), with `1 = exp 0` the one-edge tree.  This
file proves that its only unit is `1` itself, in the sharp form

`x * y = 1 ↔ x = 1 ∧ y = 1`,

i.e. `Tree` has no non-trivial factorisation of the identity.

The proof is entirely carried by the family map `fam : Tree → Multiset Tree`
(`Submission/Work/ORHughesFree/Tree/fam_mul.lean`), which is injective (`Tree.fam_injective`),
additive (`Tree.fam_add`) and whose value on a product is the double sum
`fam (x * y) = (fam x).bind (fun a => (fam y).map (fun b => a + b))` (`Tree.fam_mul`).

The two ingredients are:

* `fam_card_mul` : taking cardinalities of `Tree.fam_mul` gives `|fam (x * y)| = |fam x| · |fam y|`,
  since every multiset `(fam y).map (fun b => a + b)` has the cardinality of `fam y`.  Cardinalities
  are natural numbers, so `|fam x| · |fam y| = 1` forces `|fam x| = |fam y| = 1`: both families are
  singletons.
* `add_eq_zero_iff` : the sum of two trees is the one-vertex tree only if both summands are, since
  `fam (a + b) = fam a + fam b` and a multiset sum is empty only if both summands are.

Finally `fam 1 = fam (exp 0) = {0}` (`Tree.fam_exp`), so `fam x = {a}` with `a + b = 0` gives
`a = 0`, hence `fam x = {0} = fam 1` and `x = 1` by injectivity of `fam`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.TreeInstances
import Submission.Work.ORHughesFree.Tree.fam_mul
import Submission.Work.ORHughesFree.Tree.fam_exp
import Submission.Work.ORHughesFree.Tree.fam_basic

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- **The family of a product has multiplicative cardinality**: every element `a` of `fam x`
contributes a copy of `(fam y).map (fun b => a + b)` to `fam (x * y)`, and permuting a multiset
does not change its cardinality, so `|fam (x * y)| = |fam x| · |fam y|`. -/
private theorem fam_card_mul (x y : Tree) :
    (fam (x * y)).card = (fam x).card * (fam y).card := by
  rw [fam_mul, Multiset.card_bind]
  -- Each summand `(fam y).map (fun b => a + b)` has the cardinality of `fam y`.
  rw [show Multiset.map (Multiset.card ∘ fun a => Multiset.map (fun b => a + b) (fam y)) (fam x)
      = Multiset.map (fun _ => (fam y).card) (fam x) from
    Multiset.map_congr rfl (fun a _ => Multiset.card_map (fun b => a + b) (fam y))]
  -- A constant map takes the value `s.card`-many times.
  rw [show Multiset.map (fun _ => (fam y).card) (fam x)
      = Multiset.replicate (fam x).card (fam y).card from Multiset.map_const _ _]
  rw [Multiset.sum_replicate]
  simp

/-- A sum of two trees is the one-vertex tree if and only if both summands are: `fam` is additive
and the one-vertex tree is the only tree with empty family. -/
private theorem add_eq_zero_iff (a b : Tree) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hf : fam a + fam b = 0 := by rw [← fam_add, h, fam_zero]
    have hc : (fam a + fam b).card = 0 := by rw [hf, Multiset.card_zero]
    have h2 : (fam a).card + (fam b).card = 0 := by rw [← Multiset.card_add]; exact hc
    obtain ⟨ha, hb⟩ := Nat.add_eq_zero_iff.mp h2
    exact ⟨fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp ha),
      fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp hb)⟩
  · rintro ⟨rfl, rfl⟩
    exact Tree.add_zero 0

/-- The family of the one-edge tree is the singleton consisting of the one-vertex tree. -/
private theorem fam_one : fam (1 : Tree) = ({0} : Multiset Tree) := by
  show fam (exp (0 : Tree)) = ({0} : Multiset Tree)
  rw [fam_exp]

theorem mulEqOne (x y : Tree) : x * y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro h
    -- Cardinality: `|fam x| · |fam y| = |fam 1| = 1`, so both families are singletons.
    have hcard : (fam x).card * (fam y).card = 1 := by
      have hmul := fam_card_mul x y
      rw [h, fam_one, Multiset.card_singleton] at hmul
      exact hmul.symm
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp (Nat.eq_one_of_mul_eq_one_right hcard)
    obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp (Nat.eq_one_of_mul_eq_one_left hcard)
    -- The family of the product is then `{a + b} = fam 1 = {0}`, so `a + b = 0`.
    have hab : a + b = 0 := by
      have h2 : fam (x * y) = ({a + b} : Multiset Tree) := by
        rw [fam_mul, ha, hb, Multiset.singleton_bind, Multiset.map_singleton]
      have h3 : fam (x * y) = ({0} : Multiset Tree) := by rw [h, fam_one]
      exact Multiset.singleton_inj.mp (h2.symm.trans h3)
    obtain ⟨ha0, hb0⟩ := (add_eq_zero_iff a b).mp hab
    -- Hence `fam x = {0} = fam 1` and `fam y = {0} = fam 1`, and `fam` is injective.
    exact ⟨fam_injective (by rw [ha, ha0, fam_one]),
      fam_injective (by rw [hb, hb0, fam_one])⟩
  · rintro ⟨rfl, rfl⟩
    exact Tree.mul_one 1

end Work.ORHughesFree.Tree
