import Mathlib
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.TreeModel
import Submission.Work.ORHughesFree.Rat.evalTree_eq_zero

namespace Work.ORHughesFree.RatU

variable {U : Type} [Group U]

/-- The tree model `Tree` **detects `0`**: the universal morphism of rational `U`-semirings
`Rat(U) → Tree` of `Submission.Work.ORHughesFree.Rat.TreeModel` maps an element to the
one-vertex tree (the zero of the tree semiring) only if that element is `0`.

Indeed, `Rat.evalTree_eq_zero` says that a term whose value in `Tree` is `0` has value `0` in
every rational `U`-semiring, i.e. it *is* `0` in `Rat(U)`, the latter being the quotient of the
free term algebra by exactly this relation. -/
theorem lift_tree_eq_zero_iff (x : RatU U) :
    lift Work.ORHughesFree.Tree (Work.ORHughesFree.treeRational U) x = 0 ↔ x = 0 := by
  constructor
  · intro h
    revert h
    refine Quotient.inductionOn x ?_
    intro t ht
    have ht' : RTerm.eval Work.ORHughesFree.Tree (Work.ORHughesFree.treeRational U) t = 0 := ht
    exact Quotient.sound (show RTerm.Rel t RTerm.z from
      fun A i rA => Work.ORHughesFree.Rat.evalTree_eq_zero t ht' A rA)
  · intro h
    rw [h, map_zero]

theorem mul_ne_zero {U : Type} [Group U] {x y : Work.ORHughesFree.RatU U}
    (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  intro h
  have key : lift Work.ORHughesFree.Tree (Work.ORHughesFree.treeRational U) (x * y) = 0 := by
    rw [h, map_zero]
  rw [map_mul] at key
  rcases (Work.ORHughesFree.Tree.mul_eq_zero _ _).mp key with h' | h'
  · exact hx ((lift_tree_eq_zero_iff x).mp h')
  · exact hy ((lift_tree_eq_zero_iff y).mp h')

end Work.ORHughesFree.RatU
