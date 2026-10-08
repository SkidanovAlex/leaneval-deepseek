import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.isNilpotent_of_fpf_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# **Thompson's theorem** (area `ThompsonFrobenius`): the blueprint's `ThompsonFrobeniusProp`

A finite group admitting a fixed-point-free automorphism of prime order is nilpotent
(Thompson 1959).  This is `Submission.Blueprint.ThompsonFrobeniusProp`, derived from the strong
induction `isNilpotent_of_fpf_pow` with `q = orderOf α` (and `α ^ orderOf α = 1`).

The hypothesis `hFT : FeitThompsonProp` is carried for the blueprint's convention (it is not used
in this route: the ZJ input `hZJ : GlaubermanZJProp` replaces Feit–Thompson).
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem thompsonFrobenius (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) :
    Submission.Blueprint.ThompsonFrobeniusProp := by
  intro Q _ _ α hq hfpf
  exact isNilpotent_of_fpf_pow hZJ (Nat.card Q) Q rfl α (orderOf α) hq
    (pow_orderOf_eq_one α) hfpf

end Work.ThompsonFrobenius
