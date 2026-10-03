import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid

/-!
# The evaluation of `U ♮ X` in `Rat(U)`

The monoid `U ♮ X` of `Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid` maps to the
multiplicative monoid of `Rat(U)` by `Ugen u ↦ ofGroup u` and `Xgen a ↦ a⋄`; this file sets up
the value `evalList` of a list of `X`-letters and the value `evalWord` of an `X`-word, from which
the monoid homomorphism is assembled.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat
namespace FreeProduct

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- The value of a list of `X`-letters: the product of the `⋄`-values. -/
noncomputable def evalList (l : List (RatU U)) : RatU U := (l.map RatU.ratOp).prod

/-- The value of an `X`-word. -/
noncomputable def evalWord (L : NEL (U := U)) : RatU U := evalList L.1

@[simp] theorem evalList_nil : evalList ([] : List (RatU U)) = 1 := rfl

theorem evalList_cons (a : RatU U) (l : List (RatU U)) :
    evalList (a :: l) = RatU.ratOp a * evalList l := by
  simp [evalList]

theorem evalList_append (l l' : List (RatU U)) :
    evalList (l ++ l') = evalList l * evalList l' := by
  simp [evalList, List.map_append, List.prod_append]

theorem evalList_singleton (a : RatU U) : evalList [a] = RatU.ratOp a := by
  simp [evalList]

@[simp] theorem evalWord_mk (L : NEL (U := U)) : evalWord L = evalList L.1 := rfl

end FreeProduct
end Work.ORHughesFree.Rat
