import Mathlib
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.TreeModel

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

/-- A term whose value in the tree model is the zero tree evaluates to `0` in every rational
`U`-semiring.

The tree model `Tree` (with the trivial `U`-action and `x⋄ = exp (exp x)`) detects `0`: its zero is
the one-vertex tree, `exp _` is never the one-vertex tree, and both `+` and `*` have the expected
zero laws (`Tree.add_eq_zero_iff`, `Tree.mul_eq_zero`).  Hence a term that evaluates to `0` in
`Tree` evaluates to `0` in every rational `U`-semiring. -/
theorem evalTree_eq_zero {U : Type} [Group U] (t : Work.ORHughesFree.RTerm U)
    (h : Work.ORHughesFree.RTerm.eval Work.ORHughesFree.Tree (Work.ORHughesFree.treeRational U) t = 0) :
    ∀ (A : Type) [Semiring A] (rA : Work.ORHughesFree.RationalUSemiring U A),
      Work.ORHughesFree.RTerm.eval A rA t = 0 := by
  induction t with
  | z =>
      intro A _ rA
      rfl
  | o =>
      intro A _ rA
      exact absurd h Tree.one_ne_zero
  | add a b iha ihb =>
      intro A _ rA
      have h' : RTerm.eval Tree (treeRational U) a + RTerm.eval Tree (treeRational U) b = 0 := h
      obtain ⟨ha, hb⟩ := (Tree.add_eq_zero_iff _ _).mp h'
      show RTerm.eval A rA a + RTerm.eval A rA b = 0
      rw [iha ha, ihb hb, zero_add]
  | mul a b iha ihb =>
      intro A _ rA
      have h' : RTerm.eval Tree (treeRational U) a * RTerm.eval Tree (treeRational U) b = 0 := h
      rcases (Tree.mul_eq_zero _ _).mp h' with ha | hb
      · show RTerm.eval A rA a * RTerm.eval A rA b = 0
        rw [iha ha, zero_mul]
      · show RTerm.eval A rA a * RTerm.eval A rA b = 0
        rw [ihb hb, mul_zero]
  | rat a iha =>
      intro A _ rA
      by_cases hx : RTerm.eval Tree (treeRational U) a = 0
      · show rA.ratOp (RTerm.eval A rA a) = 0
        rw [iha hx, rA.ratOp_zero]
      · exfalso
        have h' : treeRatOp (RTerm.eval Tree (treeRational U) a) = 0 := h
        rw [treeRatOp_of_ne hx] at h'
        exact Tree.exp_ne_zero _ h'
  | smulL u a iha =>
      intro A _ rA
      show rA.smul u (RTerm.eval A rA a) = 0
      rw [iha h, rA.smul_eq_mul, mul_zero]
  | smulR u a iha =>
      intro A _ rA
      show rA.smulRight (RTerm.eval A rA a) u = 0
      rw [iha h, rA.smulRight_eq_mul, zero_mul]

end Work.ORHughesFree.Rat
