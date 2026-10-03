import Mathlib
import Submission.Work.ORHughesFree.Tree.Log
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.order_alg

/-!
# `exp` is an order embedding of the finite rooted trees

The root extension `exp x` is the tree with the single child `x`, so `fam (exp x) = {x}`
(`fam_exp`).  Since the tree order is the Dershowitz–Manna order on the family
(`lt_iff`), a comparison between the two singletons `{x}` and `{y}` reduces to the
comparison of `x` and `y`:  in the unfolding

  `{x} = X + Y`,  `{y} = X + Z`,  `Z ≠ 0`,  every `a ∈ Y` below some `b ∈ Z`

of `exp x < exp y` the common part `X` is a submultiset of the singleton `{x}`, hence
`X = 0` or `X = {x}`; the second case forces `Z = 0`, contrary to `Z ≠ 0`, so `X = 0`,
`Y = {x}`, `Z = {y}`, and the condition on the `Z`-part is exactly `x < y`.

Consequently `exp` reflects and preserves `lt` and `le`:  `exp x ≤ exp y ↔ x ≤ y`.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- If `X + Y` is a singleton `{x}` then `X` is either empty or the same singleton. -/
theorem multiset_add_eq_singleton {X Y : Multiset Tree} {x : Tree} (h : X + Y = {x}) :
    X = 0 ∨ X = {x} := by
  have hcard : X.card + Y.card = 1 := by
    rw [← Multiset.card_add, h, Multiset.card_singleton]
  have hX : X.card = 0 ∨ X.card = 1 := by omega
  rcases hX with h0 | h1
  · exact Or.inl (Multiset.card_eq_zero.mp h0)
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h1
    have hax : a = x := by
      have : a ∈ X + Y := by
        rw [ha]
        exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self a))
      rw [h, Multiset.mem_singleton] at this
      exact this
    subst hax
    exact Or.inr ha

/-- The root extension is strictly monotone. -/
theorem exp_lt_exp {x y : Tree} (h : lt x y) : lt (exp x) (exp y) := by
  rw [lt_iff]
  refine ⟨0, {x}, {y}, by simp, ?_, ?_, ?_⟩
  · rw [fam_exp]; simp
  · rw [fam_exp]; simp
  · intro a ha
    rw [Multiset.mem_singleton] at ha
    subst ha
    exact ⟨y, Multiset.mem_singleton_self y, h⟩

/-- The root extension reflects the strict order. -/
theorem lt_of_exp_lt_exp {x y : Tree} (h : lt (exp x) (exp y)) : lt x y := by
  obtain ⟨X, Y, Z, hZ, h1, h2, hstep⟩ := (lt_iff (exp x) (exp y)).mp h
  rw [fam_exp] at h1
  rw [fam_exp] at h2
  rcases multiset_add_eq_singleton h1.symm with hX0 | hXx
  · -- `X = 0`: then `Y = {x}` and `Z = {y}`, so the step condition gives `x < y`.
    have hY : Y = {x} := by
      rw [hX0, Multiset.zero_add] at h1
      exact h1.symm
    have hZr : Z = {y} := by
      rw [hX0, Multiset.zero_add] at h2
      exact h2.symm
    obtain ⟨b, hbZ, hxb⟩ := hstep x (by rw [hY]; exact Multiset.mem_singleton_self x)
    have hby : b = y := by
      rw [hZr, Multiset.mem_singleton] at hbZ
      exact hbZ
    rwa [hby] at hxb
  · -- `X = {x}`: then `{y} = {x} + Z` has cardinality at least `2`, contradiction.
    have hc := congrArg Multiset.card h2
    rw [Multiset.card_add, hXx, Multiset.card_singleton, Multiset.card_singleton] at hc
    have hZc : Z.card = 0 := by omega
    exact absurd (Multiset.card_eq_zero.mp hZc) hZ

/-- The root extension is monotone. -/
theorem exp_le_exp {x y : Tree} (h : le x y) : le (exp x) (exp y) := by
  rcases h with h | h
  · rw [h]; exact le_refl _
  · exact Or.inr (exp_lt_exp h)

/-- The root extension reflects the weak order. -/
theorem le_of_exp_le_exp {x y : Tree} (h : le (exp x) (exp y)) : le x y := by
  rcases h with h | h
  · have hf : fam (exp x) = fam (exp y) := by rw [h]
    rw [fam_exp, fam_exp] at hf
    exact Or.inl (Multiset.singleton_inj.mp hf)
  · exact Or.inr (lt_of_exp_lt_exp h)

theorem exp_mono {x y : Work.ORHughesFree.Tree} :
    ((Work.ORHughesFree.Tree.le x y → Work.ORHughesFree.Tree.le (Work.ORHughesFree.Tree.exp x) (Work.ORHughesFree.Tree.exp y)) ∧
     (Work.ORHughesFree.Tree.le (Work.ORHughesFree.Tree.exp x) (Work.ORHughesFree.Tree.exp y) → Work.ORHughesFree.Tree.le x y) ∧
     (Work.ORHughesFree.Tree.lt x y → Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Tree.exp x) (Work.ORHughesFree.Tree.exp y)) ∧
     (Work.ORHughesFree.Tree.lt (Work.ORHughesFree.Tree.exp x) (Work.ORHughesFree.Tree.exp y) → Work.ORHughesFree.Tree.lt x y)) :=
  ⟨exp_le_exp, le_of_exp_le_exp, exp_lt_exp, lt_of_exp_lt_exp⟩

end Work.ORHughesFree.Tree
