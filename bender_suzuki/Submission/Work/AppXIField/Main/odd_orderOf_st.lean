import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Bender.twoInvolutionsOdd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIField.Main

/-- In the standing context `CtxF H Q t s r P`, the element `s` is an involution of the
strongly embedded subgroup `H` (`s ∈ Q ≤ H`) and `t ∉ H` is an involution.  Peterfalvi I
Ch. I §1 (`Work.ThmF.Bender.twoInvolutionsOdd`) then gives that `s * t` has odd order, so in
particular it is odd whenever it is prime. -/
theorem odd_orderOf_st {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hf : (orderOf (s * t)).Prime) :
    Odd (orderOf (s * t)) :=
  Work.ThmF.Bender.twoInvolutionsOdd c.split.stronglyEmbedded (c.split.le c.s_mem) c.s_inv
    c.split.invol c.split.not_mem

end Work.AppXIField.Main
