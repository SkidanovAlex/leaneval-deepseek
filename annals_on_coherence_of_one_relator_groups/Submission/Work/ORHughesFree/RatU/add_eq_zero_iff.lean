import Mathlib
import Submission.Work.ORHughesFree.Rat.OfGroup

/-!
# `Rat(U)` has no additive zero divisors

`Rat(U)` is the initial rational `U`-semiring, i.e. the quotient of the free term algebra by the
relation "equal in every rational `U`-semiring".  It is therefore detected by *any* faithful model;
we use the tree model of [JZLA20, §4.1, §4.2].

The complexity map `Rat.treeOfRat : Rat(U) → Tree` is a ring homomorphism whose kernel is trivial
(`Rat.treeOfRat_eq_zero_iff`), and the semiring `Tree` of finite rooted trees is *positive*: a sum
of trees is the one-vertex tree only if both summands are (`Tree.add_eq_zero_iff`).  Consequently
the same cancellation holds in `Rat(U)` itself.
-/

namespace Work.ORHughesFree.RatU

/-- **`Rat(U)` is additively positive**: a sum of two elements of `Rat(U)` vanishes only if both
summands do. -/
theorem add_eq_zero_iff {U : Type} [Group U] (x y : Work.ORHughesFree.RatU U) :
    x + y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h1 : Work.ORHughesFree.Rat.treeOfRat U (x + y) = 0 := by
      rw [h]
      exact Work.ORHughesFree.Rat.treeOfRat_zero U
    rw [Work.ORHughesFree.Rat.treeOfRat_add U x y] at h1
    obtain ⟨hx, hy⟩ := (Work.ORHughesFree.Tree.add_eq_zero_iff _ _).mp h1
    exact ⟨(Work.ORHughesFree.Rat.treeOfRat_eq_zero_iff U x).mp hx,
      (Work.ORHughesFree.Rat.treeOfRat_eq_zero_iff U y).mp hy⟩
  · rintro ⟨rfl, rfl⟩
    rw [add_zero]

end Work.ORHughesFree.RatU
