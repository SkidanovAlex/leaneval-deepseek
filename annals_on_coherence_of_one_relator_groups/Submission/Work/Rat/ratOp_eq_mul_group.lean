/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A factorisation of a `⋄`-value in `Rat(U)` has a group-element factor

`RatU.ratOp x = x ⋄` is the rational operation of the universal rational `U`-semiring `Rat(U)`
(`Submission/Work/ORHughesFree/Rat/RTerm.lean`), and `RatU.ofGroup u = u · 1` is the image of the
group `U` in `Rat(U)` (`Submission/Work/ORHughesFree/Rat/OfGroup.lean`).

The complexity map `Tree : Rat(U) → T` of [JZLA20, Lemma 4.3] sends `⋄` to `exp ∘ exp`
(`Rat.treeOfRat_rat`), and an element of complexity `1` is exactly a group element
(`Rat.treeOfRat_eq_one_iff`).  Consequently the whole content of the lemma
`ratOp_eq_mul_group` is the tree-theoretic statement

> if `A * B = exp (exp y)` in the tree semiring, then `A = 1` or `B = 1`.

That statement is proved here as `Tree.mul_eq_exp_exp`: in the model of [JZLA20, §4.1] the family
of children of the one-child tree `exp z` is the singleton `{z}`, while
`fam (A * B) = {a + b : a ∈ fam A, b ∈ fam B}`; comparing cardinalities forces `fam A` and
`fam B` to be singletons, say `A = exp a₀` and `B = exp b₀` with `a₀ + b₀ = exp y`, and then
`fam a₀ + fam b₀ = fam (a₀ + b₀) = {y}` is again a singleton, so one of `fam a₀`, `fam b₀` is
empty, i.e. `a₀ = 0` or `b₀ = 0`, i.e. `A = 1` or `B = 1`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.OfGroup

namespace Work.ORHughesFree.Tree

/-- The family of a product of trees has cardinality the product of the cardinalities: the family
of `x * y` is the multiset `{a + b : a ∈ fam x, b ∈ fam y}` (`Tree.fam_mul`). -/
theorem fam_card_mul (x y : Tree) : (fam (x * y)).card = (fam x).card * (fam y).card := by
  rw [fam_mul, Multiset.card_bind]
  rw [show Multiset.map (Multiset.card ∘ fun a => Multiset.map (fun b => a + b) (fam y)) (fam x)
      = Multiset.map (fun _ => (fam y).card) (fam x) from
    Multiset.map_congr rfl (fun a _ => Multiset.card_map (fun b => a + b) (fam y))]
  rw [show Multiset.map (fun _ => (fam y).card) (fam x)
      = Multiset.replicate (fam x).card (fam y).card from Multiset.map_const _ _]
  rw [Multiset.sum_replicate]
  simp

/-- **A product of trees equal to the double one-child tree `exp (exp y)` has a trivial factor.**
Since `fam (exp z) = {z}`, the family of `A * B = exp (exp y)` is the singleton `{exp y}`; as the
family of `A * B` is `{a + b : a ∈ fam A, b ∈ fam B}`, both families are singletons, and the same
argument one level down shows that `A = 1` or `B = 1`. -/
theorem mul_eq_exp_exp {A B y : Tree} (h : A * B = exp (exp y)) : A = 1 ∨ B = 1 := by
  have hfam : fam (A * B) = {exp y} := by rw [h, fam_exp]
  have hcard : (fam A).card * (fam B).card = 1 := by
    have h1 : (fam (A * B)).card = 1 := by rw [hfam, Multiset.card_singleton]
    rwa [fam_card_mul] at h1
  obtain ⟨ha1, hb1⟩ := mul_eq_one.mp hcard
  obtain ⟨a₀, ha₀⟩ := Multiset.card_eq_one.mp ha1
  obtain ⟨b₀, hb₀⟩ := Multiset.card_eq_one.mp hb1
  have hA : A = exp a₀ := by rw [← sum_fam A, ha₀]; simp
  have hB : B = exp b₀ := by rw [← sum_fam B, hb₀]; simp
  have hsum : a₀ + b₀ = exp y := by
    apply exp_injective
    rw [exp_add, ← hA, ← hB]
    exact h
  have hf : fam a₀ + fam b₀ = {y} := by rw [← fam_add, hsum, fam_exp]
  have hc : (fam a₀).card + (fam b₀).card = 1 := by
    have h1 := congrArg Multiset.card hf
    rwa [Multiset.card_add, Multiset.card_singleton] at h1
  rcases Nat.add_eq_one_iff.mp hc with ⟨h1, -⟩ | ⟨-, h2⟩
  · left
    exact hA.trans ((exp_eq_one_iff a₀).mpr (fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp h1)))
  · right
    exact hB.trans ((exp_eq_one_iff b₀).mpr (fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp h2)))

end Work.ORHughesFree.Tree

namespace Work.Rat

theorem ratOp_eq_mul_group {U : Type} [Group U] {x a b : Work.ORHughesFree.RatU U} (hx : x ≠ 0)
    (h : Work.ORHughesFree.RatU.ratOp x = a * b) :
    (∃ u : U, a = Work.ORHughesFree.RatU.ofGroup u) ∨
      (∃ u : U, b = Work.ORHughesFree.RatU.ofGroup u) := by
  have hrat : Work.ORHughesFree.Rat.treeOfRat U (Work.ORHughesFree.RatU.ratOp x)
      = Work.ORHughesFree.Tree.exp (Work.ORHughesFree.Tree.exp
          (Work.ORHughesFree.Rat.treeOfRat U x)) :=
    Work.ORHughesFree.Rat.treeOfRat_rat hx
  have h1 : Work.ORHughesFree.Tree.exp (Work.ORHughesFree.Tree.exp
        (Work.ORHughesFree.Rat.treeOfRat U x))
      = Work.ORHughesFree.Rat.treeOfRat U a * Work.ORHughesFree.Rat.treeOfRat U b := by
    rw [← hrat, h, Work.ORHughesFree.Rat.treeOfRat_mul]
  rcases Work.ORHughesFree.Tree.mul_eq_exp_exp h1.symm with hA | hB
  · exact Or.inl ((Work.ORHughesFree.Rat.treeOfRat_eq_one_iff a).mp hA)
  · exact Or.inr ((Work.ORHughesFree.Rat.treeOfRat_eq_one_iff b).mp hB)

end Work.Rat
