import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.Eval

namespace Work.ORHughesFree.Rat.FreeProduct

theorem evalList_mulFirst {U : Type} [Group U] (u : U) {L : List (Work.ORHughesFree.RatU U)}
    (hL : L ≠ []) :
    Work.ORHughesFree.Rat.FreeProduct.evalList
        (Work.ORHughesFree.Rat.FreeProduct.mulFirst u L)
      = Work.ORHughesFree.RatU.ofGroup u
        * Work.ORHughesFree.Rat.FreeProduct.evalList L := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hL
  rw [mulFirst_cons, evalList_cons, evalList_cons]
  have h : Work.ORHughesFree.RatU.ratOp (actL u x)
      = Work.ORHughesFree.RatU.ofGroup u * Work.ORHughesFree.RatU.ratOp x := by
    rw [actL]
    exact (Work.ORHughesFree.RatU.ofGroup_mul_ratOp u x).symm
  rw [h, mul_assoc]

end Work.ORHughesFree.Rat.FreeProduct
