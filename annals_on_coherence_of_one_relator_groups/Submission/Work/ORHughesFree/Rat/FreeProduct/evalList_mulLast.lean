import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.Eval

namespace Work.ORHughesFree.Rat.FreeProduct

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- Right multiplication of the last coordinate only changes the value of the word by a right
factor `ofGroup u`. -/
theorem evalList_mulLast_aux {U : Type} [Group U] (u : U) (l : List (RatU U)) (hl : l ≠ []) :
    evalList (mulLast l u) = evalList l * RatU.ofGroup u := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    cases xs with
    | nil => rw [mulLast, evalList_singleton, evalList_singleton, ratOp_actR]
    | cons y ys =>
      have h := ih (List.cons_ne_nil y ys)
      simp only [mulLast, evalList_cons, h]
      group

theorem evalList_mulLast {U : Type} [Group U] {L : List (Work.ORHughesFree.RatU U)} (u : U)
    (hL : L ≠ []) :
    Work.ORHughesFree.Rat.FreeProduct.evalList
        (Work.ORHughesFree.Rat.FreeProduct.mulLast L u)
      = Work.ORHughesFree.Rat.FreeProduct.evalList L
        * Work.ORHughesFree.RatU.ofGroup u := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hL
  exact evalList_mulLast_aux u (x :: xs) (by simp)

end Work.ORHughesFree.Rat.FreeProduct
