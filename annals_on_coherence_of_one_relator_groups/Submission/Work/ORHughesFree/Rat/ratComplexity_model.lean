/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A model of `Rat(U)` with its complexity map ([JZLA20, Lemma 4.2, Lemma 4.3])

`Submission/Work/ORHughesFree/Rat/RTerm.lean` constructs the initial rational `U`-semiring
`RatU U = Rat(U)` as the quotient of the free term algebra by the relation "equal in every
rational `U`-semiring", and proves its universal property (there is a *unique* morphism of
rational `U`-semirings `Rat(U) → A` for every rational `U`-semiring `A`).

This file puts the pieces together: the complexity map `Tree : Rat(U) → T` is the universal
morphism into the rational `U`-semiring of finite rooted trees (`treeRational`), and it satisfies
the properties of [JZLA20, Lemma 4.3] that are recorded in the structure `RatComplexity`:
additivity, multiplicativity, `Tree(x⋄) = exp (exp (Tree x))`, and the order-theoretic
comparison statements.  Consequently `RatComplexity U Tree R` is inhabited for `R = Rat(U)`,
which is the statement of `ratComplexity_model`.
-/
import Mathlib
import Submission.Work.ORHughesFree.JZLA20
import Submission.Work.ORHughesFree.RootedTreesConcrete
import Submission.Work.ORHughesFree.TreeInstances
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.TreeModel
import Submission.Work.ORHughesFree.Rat.evalTree_eq_zero
import Submission.Work.ORHughesFree.Rat.treeOrderFacts

set_option autoImplicit false

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

/-! ### Triviality of the kernel of the tree complexity

A term whose value in the tree semiring is `0` is `0` in *every* rational `U`-semiring; this is
`Work.ORHughesFree.Rat.evalTree_eq_zero` (proved in
`Submission/Work/ORHughesFree/Rat/evalTree_eq_zero.lean`). -/

/-! ### `1` is the least non-zero tree

Together with the cancellation statements of [JZLA20, Lemma 4.1(ii)] this gives the comparison
between `Tree x` and `Tree x * Tree y`; the packaged statement is
`Work.ORHughesFree.Rat.treeOrderFacts` (proved in
`Submission/Work/ORHughesFree/Rat/treeOrderFacts.lean`). -/

/-! ### The complexity map -/

/-- **The complexity map** `Tree : Rat(U) → T`, i.e. the universal morphism of rational
`U`-semirings from `Rat(U)` to the finite rooted trees ([JZLA20, Lemma 4.2]). -/
noncomputable def treeOfRat (U : Type) [Group U] : RatU U → Tree :=
  fun x => RatU.lift Tree (treeRational U) x

theorem treeOfRat_apply (U : Type) [Group U] (t : RTerm U) :
    treeOfRat U (RatU.mk t) = RTerm.eval Tree (treeRational U) t := rfl

theorem treeOfRat_zero (U : Type) [Group U] : treeOfRat U 0 = 0 := map_zero _

theorem treeOfRat_one (U : Type) [Group U] : treeOfRat U 1 = 1 := map_one _

theorem treeOfRat_add (U : Type) [Group U] (x y : RatU U) :
    treeOfRat U (x + y) = treeOfRat U x + treeOfRat U y := map_add _ x y

theorem treeOfRat_mul (U : Type) [Group U] (x y : RatU U) :
    treeOfRat U (x * y) = treeOfRat U x * treeOfRat U y := map_mul _ x y

/-- `⋄ 0 = 0` for the complexity map as well. -/
theorem treeOfRat_rat_zero (U : Type) [Group U] :
    treeOfRat U ((RatU.rational (U := U)).ratOp 0) = 0 := by
  rw [show (RatU.rational (U := U)).ratOp 0 = 0 from RatU.ratOp_zero, treeOfRat_zero]

/-- [JZLA20, Lemma 4.3(i)]: the complexity of `x` is the one-vertex tree if and only if `x = 0`. -/
theorem treeOfRat_eq_zero_iff (U : Type) [Group U] (x : RatU U) : treeOfRat U x = 0 ↔ x = 0 := by
  constructor
  · intro h
    revert h
    refine Quotient.inductionOn x ?_
    intro t h
    change treeOfRat U (RatU.mk t) = 0 at h
    have h1 : RTerm.eval Tree (treeRational U) t = 0 := by
      rw [← treeOfRat_apply]; exact h
    change (RatU.mk t : RatU U) = 0
    rw [show (0 : RatU U) = RatU.mk RTerm.z from rfl]
    refine Quotient.sound ?_
    intro A i rA
    show RTerm.eval A rA t = RTerm.eval A rA RTerm.z
    have h0 : RTerm.eval A rA RTerm.z = 0 := rfl
    rw [evalTree_eq_zero t h1 A rA, h0]
  · intro h
    rw [h]
    exact treeOfRat_zero U

/-- [JZLA20, Lemma 4.3(xi)], for non-zero `x` (see `RatComplexity.tree_rat`). -/
theorem treeOfRat_rat {U : Type} [Group U] {x : RatU U} (hx : x ≠ 0) :
    treeOfRat U (RatU.ratOp x) = Tree.exp (Tree.exp (treeOfRat U x)) := by
  have h := (RatU.lift_isHom Tree (treeRational U)).map_rat x
  have hy : treeOfRat U x ≠ 0 := fun h0 => hx ((treeOfRat_eq_zero_iff U x).mp h0)
  change treeOfRat U ((RatU.rational (U := U)).ratOp x) = treeRatOp (treeOfRat U x) at h
  rw [treeRatOp_of_ne hy] at h
  exact h

/-- `treeOfRat_rat` in the form in which the term appears when it is produced by
`RatU.lift_isHom`: with the `ratOp` field of `RatU.rational`. -/
theorem treeOfRat_rat_rational {U : Type} [Group U] {x : RatU U} (hx : x ≠ 0) :
    treeOfRat U ((RatU.rational (U := U)).ratOp x) = Tree.exp (Tree.exp (treeOfRat U x)) :=
  treeOfRat_rat hx

/-- The complexity of `⋄ x` is at most `exp (exp (Tree x))`, with equality for `x ≠ 0`
(`treeOfRat_rat`) and `Tree (⋄ 0) = 0` for `x = 0` (`treeOfRat_rat_zero`). -/
theorem treeOfRat_rat_le (U : Type) [Group U] (x : RatU U) :
    Tree.le (treeOfRat U (RatU.ratOp x)) (Tree.exp (Tree.exp (treeOfRat U x))) := by
  by_cases hx : x = 0
  · rw [hx, RatU.ratOp_zero, treeOfRat_zero]
    exact Tree.le_zero _
  · rw [treeOfRat_rat hx]
    exact Tree.le_refl _

/-- **`⋄ x = 0` if and only if `x = 0`** — the counterpart of `RationalUSemiring.ratOp_zero`
(`⋄ 0 = 0`) and of `treeOfRat_rat` (whose value is `exp (exp _)`, never `0`, for `x ≠ 0`). -/
theorem ratOp_eq_zero_iff {U : Type} [Group U] {x : RatU U} : RatU.ratOp x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have h1 : Rat.treeOfRat U (RatU.ratOp x) = 0 := by rw [h, Rat.treeOfRat_zero]
    rw [treeOfRat_rat hx] at h1
    exact Tree.exp_ne_zero _ h1
  · rintro rfl
    exact RatU.ratOp_zero

/-! ### The `RatComplexity` structure -/

/-- **A model of the universal rational `U`-semiring with its complexity**: `R = Rat(U)`, its
rational structure, and the complexity map `Tree : Rat(U) → T` of [JZLA20, §4.2]. -/
noncomputable def ratComplexity (U : Type) [Group U] : RatComplexity U Tree (RatU U) where
  trees := treeRootedTrees
  rational := RatU.rational
  tree := treeOfRat U
  tree_zero := treeOfRat_zero U
  tree_one := treeOfRat_one U
  tree_add := treeOfRat_add U
  tree_mul := treeOfRat_mul U
  tree_rat := fun x hx => treeOfRat_rat hx
  tree_add_le := by
    intro x y
    show Tree.le (treeOfRat U x) (treeOfRat U x + treeOfRat U y)
    simpa using Tree.le_add (Tree.le_refl (treeOfRat U x)) (Tree.le_zero (treeOfRat U y))
  tree_add_eq := by
    intro x y hy hxy
    have hy' : treeOfRat U y ≠ 0 := fun h => hy ((treeOfRat_eq_zero_iff U y).mp h)
    exact hy' ((Tree.add_eq_self_iff _ _).mp hxy)
  tree_mul_le := by
    intro x y hx hy
    show Tree.le (treeOfRat U x) (treeOfRat U x * treeOfRat U y)
    exact treeOrderFacts.2.1 (treeOfRat U x) (treeOfRat U y)
      (fun h => hx ((treeOfRat_eq_zero_iff U x).mp h))
      (fun h => hy ((treeOfRat_eq_zero_iff U y).mp h))
  tree_mul_eq_iff := by
    intro x y hx hy
    exact treeOrderFacts.2.2 (treeOfRat U x) (treeOfRat U y)
      (fun h => hx ((treeOfRat_eq_zero_iff U x).mp h))
      (fun h => hy ((treeOfRat_eq_zero_iff U y).mp h))
  lift := fun A i rA => RatU.lift_existsUnique A rA

/-- **The complexification of `Rat(U)` exists**: the universal rational `U`-semiring `Rat(U)`
carries a complexity map to the finite rooted trees with all the properties of
[JZLA20, Lemma 4.3], so `RatComplexity U Tree (Rat(U))` is inhabited. -/
theorem ratComplexity_model (U : Type) [Group U] :
    ∃ (R : Type) (_ : Semiring R), Nonempty (RatComplexity U Tree R) :=
  ⟨RatU U, RatU.instSemiring, ⟨ratComplexity U⟩⟩

end Work.ORHughesFree.Rat
